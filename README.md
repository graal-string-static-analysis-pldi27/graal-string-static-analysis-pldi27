# String Static Analysis in GraalVM Native Image

Optimizing string performance and memory allocation in GraalVM Native Image by using
custom string representations at each allocation site during compile time by 
string-oriented static analysis techniques.

# Build instructions

The commands below target Linux x86-64. Install a C/C++ build toolchain, the OpenJDK build dependencies, a bootstrap JDK 25, and `mx` version 7.83.1. Ensure `mx` is on your PATH.

From the repository root:

```sh
export ARTIFACT_ROOT="$(pwd)"
export BOOT_JDK=/path/to/jdk-25
```

## Build custom LabsJDK
```sh
cd "$ARTIFACT_ROOT/labsJDK"
bash configure --with-boot-jdk="$BOOT_JDK" --disable-warnings-as-errors
make graal-builder-image
```

## Build custom GraalVM
```sh
export JAVA_HOME="$ARTIFACT_ROOT/labsJDK/build/linux-x86_64-server-release/images/graal-builder-jdk"

cd "$ARTIFACT_ROOT/graal/vm"
mx --env ce build

export GRAALVM_HOME="$ARTIFACT_ROOT/graal/sdk/latest_graalvm_home"
"$GRAALVM_HOME/bin/native-image" --version
```

Enable string analysis when building native images with `-H:+StringAnalysis`.
