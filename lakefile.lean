import Lake
open System Lake DSL


def buildDir := defaultBuildDir
def cDir : FilePath := "csrc"

-- given a package dir and c source file, constructs a FileTarget that builds the
-- corresponding .o file using the lean C compiler
def ffiOTarget (pkgDir : FilePath) (ffiSrc : FilePath): FileTarget :=
  let oFile := pkgDir / buildDir / cDir / (System.FilePath.withExtension ffiSrc "o")
  let srcTarget := inputFileTarget <| pkgDir / cDir/ ffiSrc
  let localIncludeDir := pkgDir / cDir / "include"
  fileTargetWithDep oFile srcTarget fun srcFile => do
    let compileOptions := #[
                              "-I", (← getLeanIncludeDir).toString,
                              "-I", localIncludeDir.toString
    ]
    compileO oFile srcFile compileOptions "cc"

-- a FileTarget to build the ffi lib from component c files
def cLibTarget (pkgDir : FilePath) : FileTarget :=
  let libFile := pkgDir / buildDir / cDir / "libql.a"
  staticLibTarget libFile #[
                            ffiOTarget pkgDir "data_marshal.c",
                            ffiOTarget pkgDir "mutex_ffi.c"
                            ]


package QingLong (pkgDir) (args) {
  srcDir := "src"

  -- specify the c binding library as an additional target
  moreLibTargets := #[cLibTarget pkgDir]
}
