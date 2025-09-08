import Lake
open Lake DSL System

package «auto» {
  precompileModules := true
  preferReleaseBuild := true
}

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
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
  let exitCode? ← LoggerIO.toBaseIO (minLv := v.minLogLv) <| ws.runLakeT do
    if let some pkg ← findPackage? _package.name then
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
  if exitCode = 0 then return () else error s!"{pkg.name}: failed to download/setup `zipperposition`"
