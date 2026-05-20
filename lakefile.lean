import Lake
open Lake DSL System

package «auto» {
  precompileModules := true
  preferReleaseBuild := true
}

/-- Extract `zipFile` into `dir`, then mark `exeFile` executable on Unix. -/
def extract (zipFile exeFile dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  if System.Platform.isWindows || System.Platform.isOSX then
    proc (quiet := true) {
      cmd := "tar"
      args := #["-xf", zipFile.toString, "-C", dir.toString]
    }
  else
    proc (quiet := true) {
      cmd := "unzip"
      args := #["-d", dir.toString, zipFile.toString]
    }
  unless System.Platform.isWindows do
    proc (quiet := true) {
      cmd := "chmod"
      args := #["+x", exeFile.toString]
    }

namespace Zipperposition

def urlPrefix : String :=
  "https://github.com/sneeuwballen/zipperposition/releases/download/2.1"

def zipName : String :=
  if System.Platform.isWindows then "zipperposition-bin-windows-latest-4.12.x.exe.zip"
  else if System.Platform.isOSX then "zipperposition-bin-macos-big-sur.exe.zip"
  else "zipperposition-bin-ubuntu-latest-4.12.x.exe.zip"

-- Mirrors `Auto/Solver/TPTP.lean/def zipperpositionDefaultPath`
def exeName : String :=
  if System.Platform.isOSX then
    "zipperposition-bin-macos-big-sur.exe"
  else
    "zipperposition.exe"

/-- Check whether `zipperposition` is already present at the expected
    download location (`buildDir / exeName`). Returns its absolute path if
    it exists, or `none` otherwise. -/
def findAutoDownload (buildDir : FilePath) : IO (Option FilePath) := do
  let exeFile := buildDir / exeName
  if (← exeFile.pathExists) then return some exeFile
  return none

end Zipperposition

/-- File target that yields the path to a usable `zipperposition` executable.
    Reuses a previously extracted copy in `pkg.buildDir` if present;
    otherwise downloads and extracts the appropriate release archive into
    `pkg.buildDir`. -/
target zipperpositionAutoDownload pkg : FilePath := do
  if let some onPath ← Zipperposition.findAutoDownload pkg.buildDir then
    return .pure onPath
  let exeFile := pkg.buildDir / Zipperposition.exeName
  let zipFile := pkg.buildDir / Zipperposition.zipName
  IO.FS.createDirAll pkg.buildDir
  download s!"{Zipperposition.urlPrefix}/{Zipperposition.zipName}" zipFile
  extract zipFile exeFile pkg.buildDir
  IO.FS.removeFile zipFile
  return .pure exeFile

@[default_target]
lean_lib «Auto» {
  /-
    Download the zipperposition executable.
    Lake re-evaluates this target each build, but the action is a no-op once the
    binary is present in `pkg.buildDir`.
  -/
  extraDepTargets := #[``zipperpositionAutoDownload]
}

def Lake.unzip (zipFile exeFile : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  if System.Platform.isWindows then
    proc (quiet := true) {
      cmd := "tar"
      args := #["-xf", zipFile.toString, "-C", dir.toString]
    }
  else if System.Platform.isOSX then
    proc (quiet := true) {
      cmd := "tar"
      args := #["-xf", zipFile.toString, "-C", dir.toString]
    }
    proc (quiet := true) {
      cmd := "chmod"
      args := #["+x", exeFile.toString]
    }
  else
    proc (quiet := true) {
      cmd := "unzip"
      args := #["-d", dir.toString, zipFile.toString]
    }
    proc (quiet := true) {
      cmd := "chmod"
      args := #["+x", exeFile.toString]
    }

def zipperposition.url := "https://github.com/sneeuwballen/zipperposition/releases/download/2.1"

def zipperposition.zip_name :=
  if System.Platform.isWindows then "zipperposition-bin-windows-latest-4.12.x.exe.zip"
  else if System.Platform.isOSX then "zipperposition-bin-macos-big-sur.exe.zip"
  else "zipperposition-bin-ubuntu-latest-4.12.x.exe.zip"

def zipperposition.exe_name :=
  if System.Platform.isWindows then "zipperposition.exe"
  else if System.Platform.isOSX then "zipperposition-bin-macos-big-sur.exe"
  else "zipperposition.exe"

-- Code for automatically downloading a Zipperposition executable (triggers on `lake update`)
post_update pkg do
  let ws ← getWorkspace
  let args := ws.lakeArgs?.getD #[]
  let v := Verbosity.normal
  let v := if args.contains "-q" || args.contains "--quiet" then Verbosity.quiet else v
  let v := if args.contains "-v" || args.contains "--verbose" then Verbosity.verbose else v
  let exitCode? ← LoggerIO.toBaseIO (cfg := {outLv := v.minLogLv}) <| ws.runLakeT do
    if let some pkg ← findPackageByKey? __name__ then
      let zipperpositionZipFile := pkg.buildDir / zipperposition.zip_name
      let zipperpositionExeFile := pkg.buildDir / zipperposition.exe_name
      if !(← zipperpositionExeFile.pathExists) then
        download s!"{zipperposition.url}/{zipperposition.zip_name}" zipperpositionZipFile
        unzip zipperpositionZipFile zipperpositionExeFile pkg.buildDir
        IO.FS.removeFile zipperpositionZipFile
      return 0
    else
      logError "package not found"
      return 1
  let exitCode := exitCode?.getD 1
  if exitCode = 0 then return () else error s!"{pkg.baseName}: failed to download/setup `zipperposition`"
