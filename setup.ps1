[CmdletBinding()]
param()
$ErrorActionPreference = "Stop"
Push-Location $PSScriptRoot
try {
    Get-Command lake -ErrorAction Stop | Out-Null
    $Before = (Get-FileHash -LiteralPath "lake-manifest.json" -Algorithm SHA256).Hash
    $SavedErrorPreference = $ErrorActionPreference
    try {
        $ErrorActionPreference = "Continue"
        & lake exe cache get
        $Code = $LASTEXITCODE
    } finally { $ErrorActionPreference = $SavedErrorPreference }
    if ($Code -ne 0) { throw "Dependency/cache setup failed (exit $Code)." }
    $After = (Get-FileHash -LiteralPath "lake-manifest.json" -Algorithm SHA256).Hash
    if ($Before -ne $After) { throw "Dependency lock changed during setup; review it before building." }
    Write-Output "Dependencies ready. Run lake build for the library, or ./check.ps1 for the distribution checks."
} finally { Pop-Location }
