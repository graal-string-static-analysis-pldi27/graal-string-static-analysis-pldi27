# Benchmarks

`build-benchmark.sh` downloads pinned sources, applies patches, prepares inputs,
and builds the paper's 62 benchmarks as Java workloads and native images.

## Usage

Run from this directory on Linux x86-64. Install Git, Python 3, curl, Maven,
Ant, and a C/C++ build toolchain. Gradle projects use their bundled wrappers.

Build all benchmarks:

```sh
./build-benchmark.sh \
  --jdk /opt/jdk25 \
  --graalvm /opt/graalvm \
  --jdk8 /opt/jdk8 \
  --jdk9 /opt/jdk9 \
  --jdk11 /opt/jdk11 \
  --jdk17 /opt/jdk17 \
  --jdk21 /opt/jdk21 \
  --jdk25 /opt/jdk25
```

`--graalvm` selects the modified GraalVM built using the repository's
[build instructions](../README.md#build-instructions).

| JDK option | Use |
|---|---|
| `--jdk` | JDK 25 for Java compilation and Maven |
| `--jdk8`, `--jdk11` | DaCapo |
| `--jdk9` | tinylog |
| `--jdk17` | Log4j, Calcite, JSqlParser, SQL Formatter, Yauaa |
| `--jdk21` | Palantir, Yauaa |
| `--jdk25` | Release JDK 25 for Lucene and Spring |

Select benchmarks by appending their paper names:

```sh
./build-benchmark.sh --jdk /opt/jdk25 --graalvm /opt/graalvm \
  jsonparser StringConcat
```

Build stock and modified native images:

```sh
./build-benchmark.sh --jdk /opt/jdk25 --graalvm /opt/graalvm \
  --baseline /opt/graalvm-stock --configs BASE,FULL \
  jsonparser StringConcat
```

Configurations are `BASE` (stock), `FULL` (all string representations),
`SBS` (single-byte strings), `SV` (string views), and `LS` (lazy strings).
The default is `FULL`.

| Option | Purpose |
|---|---|
| `--list` | List benchmark names |
| `--stage fetch` | Download and patch sources |
| `--stage java` | Download, patch, and build Java workloads and inputs |
| `--stage native` | Build native images from prepared Java workloads |
| `--stage all` | Perform all stages; the default |
| `--work-dir PATH` | Select the workspace; defaults to `work/` |
| `--maven PATH` | Select the Maven executable |
| `--parallelism N` | Native-image workers; defaults to 16 |
| `--heap SIZE` | Native-image builder heap; defaults to `48g` |
| `--alignment N` | Code alignment; defaults to 64 |
| `--dry-run` | Print the selected build plan |
| `--help` | Show all options |

Sources are downloaded into `work/sources/`. Java build paths and working
directories are recorded in `work/build/<source-name>/target.env`.
Native images and build logs are written to
`work/build/<benchmark>/native/<configuration>` and `<configuration>.log`.
Benchmarks sharing an upstream project share its Java build.

## Patches

The script applies patches from `patches/<source-name>/` to the revisions
listed in [`recipes/sources.tsv`](recipes/sources.tsv).

| Benchmark | Patch |
|---|---|
| commons-csv | Enables JMH annotation processing. |
| commons-lang-charseq, commons-lang-join | Enables JMH annotation processing. |
| commons-text | Enables JMH annotation processing. |
| csv-parsers-comparison | Sets Java 8 compilation and moves the Flatpack adapter to `excluded-src/`. |
| DaCapo benchmarks | Adds the `paper` Ant target for the 12 selected benchmarks. |
| gson | Copies ZIP resources to temporary files for the resource loader. |
| jackson, jackson-yaml | Enables JMH annotation processing. |
| java-json-benchmark | Configures shaded dependencies and JSON provider selection. |
| jsoup-plaintext | Reads local HTML files and adds a configurable repetition loop. |
| logback-fileappender | Pins Logback 1.6.4 and moves the MDC adapter benchmark to `excluded-src/`. |
| lucene-bytask, lucene-jmh | Adds document preparation and indexing algorithm files. |
| minimal-json | Sets Java 8 compilation and adds a main-method harness for the read/write benchmarks. |
| pdfbox | Makes Log4j Core a compile dependency. |
| template-benchmark | Enables JMH annotation processing and pins JMustache 1.16. |
| thymeleaf | Sets JMH 1.37, Maven Compiler Plugin 3.13.0, and annotation processing. |
| yauaa | Packages Log4j Core and configures Lombok and JMH annotation processors. |

## Contents

- `micro-benchmarks/`, `json-parser/`: bundled benchmark sources.
- `harness/`: Java drivers, dependency definitions, and build helpers.
- `recipes/`: pinned upstream revisions and native-image arguments.
- `config/`: native-image configuration files.
- `patches/`: upstream source and build adaptations.
- [`raw-data/`](raw-data/README.md): evaluation outputs and result tables.
