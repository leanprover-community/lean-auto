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
