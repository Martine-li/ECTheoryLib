[CmdletBinding()]
param()
$ErrorActionPreference = "Stop"
$Started = [DateTimeOffset]::UtcNow
$Entries = [System.Collections.Generic.List[object]]::new()
$Status = "failed"
$Failure = $null
$Before = @()
$Stable = $false

function Get-SourceHashes {
    $Files = @((Get-Item -LiteralPath "ECTheoryLib.lean"),
        (Get-ChildItem -LiteralPath "ECTheoryLib" -Filter "*.lean" -File -Recurse),
        (Get-ChildItem -LiteralPath "Examples" -Filter "*.lean" -File -Recurse)) |
        ForEach-Object { $_ } | Sort-Object FullName
    foreach ($File in $Files) {
        [ordered]@{
            path = $File.FullName.Substring($PSScriptRoot.Length + 1).Replace('\', '/')
            sha256 = (Get-FileHash -LiteralPath $File.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
        }
    }
}

function Invoke-Check {
    param([string]$Label, [string[]]$Arguments)
    $StepStarted = [DateTimeOffset]::UtcNow
    Write-Output "Checking: $Label"
    $Saved = $ErrorActionPreference
    try {
        $ErrorActionPreference = "Continue"
        & $LakeExecutable @Arguments
        $Code = $LASTEXITCODE
    } finally { $ErrorActionPreference = $Saved }
    $Entries.Add([ordered]@{
        label = $Label
        command = "lake " + ($Arguments -join " ")
        exit_code = $Code
        seconds = [Math]::Round(([DateTimeOffset]::UtcNow - $StepStarted).TotalSeconds, 3)
    })
    if ($Code -ne 0) { throw "Check failed: $Label (exit $Code)." }
}

Push-Location $PSScriptRoot
try {
    $LakeExecutable = (Get-Command lake -ErrorAction Stop).Source
    $Before = @(Get-SourceHashes)
    $Examples = @(Get-ChildItem -LiteralPath "Examples" -Filter "*.lean" -File -Recurse | Sort-Object FullName)
    Invoke-Check "Formal library" @("--wfail", "build")
    foreach ($Example in $Examples) {
        $Relative = $Example.FullName.Substring($PSScriptRoot.Length + 1).Replace('\', '/')
        Invoke-Check $Relative @("env", "lean", "-DwarningAsError=true", $Relative)
    }
    $After = @(Get-SourceHashes)
    $Stable = (ConvertTo-Json -InputObject $Before -Depth 3 -Compress) -ceq
        (ConvertTo-Json -InputObject $After -Depth 3 -Compress)
    if (-not $Stable) { throw "Lean sources changed during the checks." }
    $Status = "passed"
} catch {
    $Failure = $_.Exception.Message
    throw
} finally {
    try {
        $Directory = Join-Path $PSScriptRoot "validation"
        [System.IO.Directory]::CreateDirectory($Directory) | Out-Null
        $Report = [ordered]@{
            status = $Status
            scope = "Formal library and published examples; internal regression and axiom-audit tools are not included."
            started_at_utc = $Started.ToString("o")
            finished_at_utc = [DateTimeOffset]::UtcNow.ToString("o")
            seconds = [Math]::Round(([DateTimeOffset]::UtcNow - $Started).TotalSeconds, 3)
            lean_toolchain = (Get-Content -LiteralPath "lean-toolchain" -Raw).Trim()
            example_files = @($Examples).Count
            checks_completed = $Entries.Count
            source_stable = $Stable
            failure = $Failure
            checks = @($Entries.ToArray())
            source_hashes = @(Get-SourceHashes)
        }
        [System.IO.File]::WriteAllText((Join-Path $Directory "latest-check.json"),
            ($Report | ConvertTo-Json -Depth 8), [System.Text.UTF8Encoding]::new($false))
        Write-Output "Distribution check report: validation/latest-check.json ($Status)"
    } finally { Pop-Location }
}
