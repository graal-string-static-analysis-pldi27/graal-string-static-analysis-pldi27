#!/usr/bin/env bash
set -euo pipefail

BENCH=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
WORK=${BENCHMARK_WORK:-"$BENCH/work"}
JDK=${JAVA_HOME:-}
GRAALVM=${GRAALVM_HOME:-}
BASELINE=${BASELINE_GRAALVM_HOME:-}
JDK8=${JDK8_HOME:-}; JDK9=${JDK9_HOME:-}; JDK11=${JDK11_HOME:-}
JDK17=${JDK17_HOME:-}; JDK21=${JDK21_HOME:-}; JDK25=${JDK25_HOME:-}
MVN=${MVN:-mvn}
CONFIGS=FULL
STAGE=all
DRY=0
PARALLELISM=16
ALIGNMENT=64
HEAP=48g
NAMES=()
JAVAC_FLAGS=()

usage() {
    cat <<'EOF'
Usage: build-benchmark.sh --jdk PATH --graalvm PATH [options] [BENCHMARK ...]

Downloads pinned sources, applies patches, and builds Java and native workloads.
Benchmark names match the paper. The default selection is all 62 benchmarks.

  --jdk PATH          JDK 25 for Java compilation and Maven
  --graalvm PATH      Modified GraalVM for FULL/SBS/SV/LS native images
  --baseline PATH     Stock GraalVM for BASE native images
  --jdk8 PATH         DaCapo build JDK
  --jdk9 PATH         tinylog build JDK
  --jdk11 PATH        DaCapo build JDK
  --jdk17 PATH        Log4j, Calcite, JSqlParser, SQL Formatter build JDK
  --jdk21 PATH        Palantir and Yauaa build JDK
  --jdk25 PATH        Release JDK 25 for Lucene and Spring
  --maven PATH        Maven executable (default: mvn)
  --work-dir PATH     Sources, dependencies and build outputs (default: work/)
  --configs LIST      Comma-separated BASE,FULL,SBS,SV,LS (default: FULL)
  --stage STAGE       all, fetch, java, native (default: all)
  --parallelism N     Native-image worker count (default: 16)
  --alignment N       Native-image code alignment (default: 64)
  --heap SIZE         Native-image builder heap (default: 48g)
  --dry-run           Print the selected build plan
  --list              List benchmark names
  --help              Show usage

Examples:
  ./build-benchmark.sh --jdk /opt/jdk25 --graalvm /opt/graalvm jsonparser StringConcat
  ./build-benchmark.sh --jdk /opt/jdk25 --graalvm /opt/graalvm \
      --baseline /opt/graalvm-stock --configs BASE,FULL guava-strings
EOF
}

die() { printf 'Error: %s\n' "$*" >&2; exit 1; }
need_value() { [[ $# -ge 2 && -n $2 ]] || die "$1 requires a value"; }
while (($#)); do
    case $1 in
        --jdk) need_value "$@"; JDK=$2; shift 2;;
        --graalvm) need_value "$@"; GRAALVM=$2; shift 2;;
        --baseline) need_value "$@"; BASELINE=$2; shift 2;;
        --jdk8) need_value "$@"; JDK8=$2; shift 2;;
        --jdk9) need_value "$@"; JDK9=$2; shift 2;;
        --jdk11) need_value "$@"; JDK11=$2; shift 2;;
        --jdk17) need_value "$@"; JDK17=$2; shift 2;;
        --jdk21) need_value "$@"; JDK21=$2; shift 2;;
        --jdk25) need_value "$@"; JDK25=$2; shift 2;;
        --maven) need_value "$@"; MVN=$2; shift 2;;
        --work-dir) need_value "$@"; WORK=$2; shift 2;;
        --configs) need_value "$@"; CONFIGS=$2; shift 2;;
        --stage) need_value "$@"; STAGE=$2; shift 2;;
        --parallelism) need_value "$@"; PARALLELISM=$2; shift 2;;
        --alignment) need_value "$@"; ALIGNMENT=$2; shift 2;;
        --heap) need_value "$@"; HEAP=$2; shift 2;;
        --dry-run) DRY=1; shift;;
        --list) find "$BENCH/recipes" -mindepth 2 -maxdepth 2 -name native.args -printf '%h\n' | sed 's#.*/##' | sort; exit 0;;
        --help|-h) usage; exit 0;;
        --) shift; NAMES+=("$@"); break;;
        -*) die "Unknown option: $1";;
        *) NAMES+=("$1"); shift;;
    esac
done
case $STAGE in all|fetch|java|native) ;; *) die "Unknown stage: $STAGE";; esac
[[ $PARALLELISM =~ ^[1-9][0-9]*$ ]] || die "Invalid parallelism"
[[ $ALIGNMENT =~ ^[1-9][0-9]*$ ]] || die "Invalid alignment"
IFS=, read -ra VARIANTS <<< "$CONFIGS"
[[ -n $CONFIGS && $CONFIGS != *, ]] || die "Empty configuration"
for variant in "${VARIANTS[@]}"; do
    case $variant in BASE|FULL|SBS|SV|LS) ;; *) die "Unknown configuration: $variant";; esac
done
if ((${#NAMES[@]} == 0)); then
    mapfile -t NAMES < <(find "$BENCH/recipes" -mindepth 2 -maxdepth 2 -name native.args -printf '%h\n' | sed 's#.*/##' | sort)
fi
for name in "${NAMES[@]}"; do
    [[ -f "$BENCH/recipes/$name/native.args" ]] || die "Unknown benchmark: $name"
done

source_key() {
    case $1 in
        avrora|batik|biojava|fop|graphchi|h2|luindex|lusearch|pmd|sunflow|xalan|zxing) echo dacapo;;
        commons-lang-join) echo commons-lang-charseq;;
        lucene-jmh) echo lucene-bytask;;
        jackson-yaml) echo jackson;;
        *) echo "$1";;
    esac
}
if ((DRY)); then
    for name in "${NAMES[@]}"; do
        printf '%s: source=%s stage=%s configs=%s\n' "$name" "$(source_key "$name")" "$STAGE" "$CONFIGS"
    done
    exit 0
fi
command -v python3 >/dev/null || die "python3 is required"
command -v git >/dev/null || die "git is required"
WORK=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$WORK")
SOURCES=$WORK/sources
BUILDS=$WORK/build
M2=$WORK/m2
mkdir -p "$SOURCES" "$BUILDS" "$M2" "$WORK/downloads"

check_jdk() {
    [[ -n $2 && -x "$2/bin/javac" && -x "$2/bin/java" ]] || die "Specify $1 with a JDK path"
}
if [[ $STAGE != fetch ]]; then
    check_jdk --jdk "$JDK"
    JDK=$(cd "$JDK" && pwd)
    export JAVA_HOME=$JDK PATH="$JDK/bin:$PATH"
fi
for toolchain in JDK8 JDK9 JDK11 JDK17 JDK21 JDK25 GRAALVM BASELINE; do
    if [[ -n ${!toolchain} ]]; then
        printf -v "$toolchain" '%s' "$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "${!toolchain}")"
    fi
done
if [[ $STAGE == java || $STAGE == all ]]; then
    for name in "${NAMES[@]}"; do
        case $(source_key "$name") in
            jsonparser|regex-redux|calcite-parser|rhino|java-json-benchmark|fastcsv|spring-stringutils|lucene-bytask|palantir) ;;
            *) MVN=$(command -v "$MVN") || die "Maven is required; specify --maven PATH"
               MVN=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$MVN")
               break;;
        esac
    done
fi
if [[ $STAGE == all || $STAGE == native ]]; then
    for variant in "${VARIANTS[@]}"; do
        if [[ $variant == BASE ]]; then
            [[ -x "$BASELINE/bin/native-image" ]] || die "Specify --baseline for BASE"
            BASELINE=$(cd "$BASELINE" && pwd)
        else
            [[ -x "$GRAALVM/bin/native-image" ]] || die "Specify --graalvm for $variant"
            GRAALVM=$(cd "$GRAALVM" && pwd)
        fi
    done
fi

declare -A FETCHED=() BUILT=()
fetch_repo() {
    local key=$1 url sha patch
    [[ ${FETCHED[$key]:-} == yes ]] && return
    if ! IFS=$'\t' read -r _ url sha < <(awk -F '\t' -v n="$key" '$1==n {print; exit}' "$BENCH/recipes/sources.tsv"); then
        die "Missing source pin for $key"
    fi
    [[ -n ${url:-} && -n ${sha:-} ]] || die "Missing source pin for $key"
    local dir=$SOURCES/$key
    if [[ ! -e $dir ]]; then
        git init -q "$dir"
        git -C "$dir" remote add origin "$url"
    fi
    [[ -d "$dir/.git" ]] || die "Expected a source checkout at $dir"
    if ! git -C "$dir" rev-parse --verify HEAD >/dev/null 2>&1; then
        git -C "$dir" fetch --depth 1 origin "$sha"
        git -C "$dir" -c advice.detachedHead=false checkout --detach FETCH_HEAD
    fi
    [[ $(git -C "$dir" rev-parse HEAD) == "$sha" ]] || die "Source revision differs at $dir"
    for patch in "$BENCH/patches/$key/"*.patch; do
        [[ -f $patch ]] || continue
        if git -C "$dir" apply --reverse --check "$patch" 2>/dev/null; then
            continue
        fi
        git -C "$dir" apply --check "$patch"
        git -C "$dir" apply "$patch"
    done
    FETCHED[$key]=yes
}
download() {
    local url=$1 dest=$2
    [[ -s $dest ]] && return
    command -v curl >/dev/null || die "curl is required"
    mkdir -p "$(dirname "$dest")"
    curl --fail --location --retry 3 "$url" -o "$dest.part"
    mv "$dest.part" "$dest"
}
maven() {
    (cd "$S" && JAVA_HOME=$BUILD_JDK PATH="$BUILD_JDK/bin:$PATH" \
        "$MVN" -B "-Dmaven.repo.local=$M2" "$@")
}
gradle() {
    (cd "$S" && JAVA_HOME=$BUILD_JDK PATH="$BUILD_JDK/bin:$PATH" \
        ./gradlew --no-daemon "$@")
}
dependencies() {
    maven "$@" dependency:build-classpath -Dmdep.includeScope=test "-Dmdep.outputFile=$B/dependencies.txt"
    DEPS=$(cat "$B/dependencies.txt")
}
classes() {
    local dest=$1 cp=$2; shift 2
    mkdir -p "$dest"
    "$JDK/bin/javac" "${JAVAC_FLAGS[@]}" -proc:full -nowarn -cp "$cp" -d "$dest" "$@"
}
jar_match() {
    local matches=()
    mapfile -t matches < <(compgen -G "$1" | sort)
    ((${#matches[@]} == 1)) || die "Expected one JAR matching $1"
    JAR=${matches[0]}
}
toolchains() {
    python3 - "$B/toolchains.xml" "$@" <<'PY'
import sys
import xml.etree.ElementTree as E
root=E.Element("toolchains")
for spec in sys.argv[2:]:
    version,path=spec.split("=",1)
    t=E.SubElement(root,"toolchain")
    E.SubElement(t,"type").text="jdk"
    p=E.SubElement(t,"provides")
    E.SubElement(p,"version").text=version
    E.SubElement(p,"vendor").text="temurin"
    E.SubElement(E.SubElement(t,"configuration"),"jdkHome").text=path
E.ElementTree(root).write(sys.argv[1],encoding="unicode")
PY
}

build_java() {
    local key=$1
    [[ ${BUILT[$key]:-} == yes ]] && return
    local S=$SOURCES/$key B=$BUILDS/$key BUILD_JDK=$JDK
    local JAR="" CLASSPATH="" DEPS="" RWD=$B
    local sources=()
    mkdir -p "$B"
    case $key in
        StringBuilders|StringBuffers|StringBuilderToString|StringConcat|StringConcatStartup|StringJoiner|StringSubstring)
            S=$BENCH/micro-benchmarks/$key
            (cd "$S" && "$MVN" -B "-Dmaven.repo.local=$M2" -DskipTests package)
            JAR=$S/target/benchmarks.jar;;
        jsonparser)
            mapfile -d '' -t sources < <(find "$BENCH/json-parser/src" -name '*.java' -print0)
            classes "$B/classes" . "${sources[@]}"
            CLASSPATH=$B/classes;;
        dacapo)
            check_jdk --jdk8 "$JDK8"; check_jdk --jdk11 "$JDK11"
            command -v ant >/dev/null || die "ant is required"
            (cd "$S/benchmarks" && JAVA_HOME=$JDK8 PATH="$JDK8/bin:$PATH" \
                ant "-Djdk.11.home=$JDK11" "-Dmvn-exe=$MVN" \
                "-Dbuild.target-dir=$B/suite" "-Dbuild.target-jar=$B/suite.jar" paper)
            RWD=$B/suite;;
        regex-redux)
            mapfile -d '' -t sources < <(find "$BENCH/harness/regex-redux" -name '*.java' -print0)
            classes "$B/classes" . "${sources[@]}"
            [[ -s "$B/regexredux-input5000000.txt" ]] || \
                "$JDK/bin/java" -cp "$B/classes" fasta 5000000 > "$B/regexredux-input5000000.txt"
            CLASSPATH=$B/classes;;
        template-benchmark|jackson|logback-fileappender)
            maven package -DskipTests -Dmaven.javadoc.skip=true
            if [[ $key == jackson ]]; then JAR=$S/target/perf.jar
            else JAR=$S/target/benchmarks.jar; fi;;
        fastjson2)
            maven -pl benchmark -am package -DskipTests -Dmaven.javadoc.skip=true -Dgpg.skip
            JAR=$S/benchmark/target/fastjson2-benchmarks.jar;;
        minimal-json)
            maven -pl com.eclipsesource.json,com.eclipsesource.json.performancetest install \
                -DskipTests -Danimal.sniffer.skip=true -Dgpg.skip=true \
                -Dmaven.javadoc.skip=true -Ddownload.plugin.skip=true
            S=$S/com.eclipsesource.json.performancetest
            maven dependency:build-classpath
            DEPS=$(cat "$S/target/runtime-classpath")
            CLASSPATH=$S/target/classes:$DEPS;;
        commonmark)
            maven -pl commonmark -am install -DskipTests -Dmaven.javadoc.skip=true
            dependencies -pl commonmark
            maven -pl commonmark test-compile -Dmaven.compiler.proc=full -DskipTests
            CLASSPATH=$S/commonmark/target/classes:$S/commonmark/target/test-classes:$S/commonmark-test-util/target/classes:$DEPS;;
        gson|guava-strings)
            local module=gson
            [[ $key == guava-strings ]] && module=guava-tests
            maven -pl "$module" -am install -DskipTests -Dmaven.javadoc.skip=true \
                -Dcheckstyle.skip=true -Dforbiddenapis.skip=true -Danimal.sniffer.skip=true -Denforcer.skip=true
            if [[ $key == gson ]]; then
                maven -pl metrics test-compile -DskipTests
                dependencies -pl metrics
                CLASSPATH=$B/classes:$S/metrics/target/classes:$DEPS
            else
                dependencies -pl guava-tests
                CLASSPATH=$B/classes:$S/guava/target/classes:$S/guava-tests/target/test-classes:$DEPS
            fi
            mapfile -d '' -t sources < <(find "$BENCH/harness/$key" -name '*.java' -print0)
            classes "$B/classes" "$CLASSPATH" "${sources[@]}"
            RWD=$S;;
        commons-lang-charseq|commons-text|commons-csv)
            if [[ $key == commons-csv ]]; then
                download 'https://web.archive.org/web/2020id_/https://kasparov.skife.org/csv/csv-1.0.jar' "$B/csv-1.0.jar"
                maven install:install-file "-Dfile=$B/csv-1.0.jar" \
                    -DgroupId=org.skife.kasparov -DartifactId=csv -Dversion=1.0 -Dpackaging=jar
            fi
            maven -Pbenchmark test-compile -DskipTests -Dmaven.javadoc.skip=true
            dependencies -Pbenchmark
            if [[ $key == commons-text ]]; then
                DEPS=$(printf '%s' "$DEPS" | tr ':' '\n' | grep -v '/org/graalvm/' | paste -sd:)
            fi
            CLASSPATH=$S/target/classes:$S/target/test-classes:$DEPS;;
        csv-parsers-comparison)
            fetch_repo commons-csv
            gzip -dc "$SOURCES/commons-csv/src/test/resources/org/apache/commons/csv/perf/worldcitiespop.txt.gz" > "$B/worldcitiespop.txt"
            maven package -DskipTests
            JAR=$S/target/csv-parsers-comparison-1.0-uber.jar;;
        log4j2-plc)
            check_jdk --jdk17 "$JDK17"; BUILD_JDK=$JDK17
            maven -pl log4j-perf-test -am package -DskipTests -Dmaven.javadoc.skip=true
            jar_match "$S/log4j-perf-test/target/*-uber.jar";;
        opennlp)
            maven -Pjmh -pl opennlp-core/opennlp-runtime -am test-compile \
                -Dforbiddenapis.skip=true -Dcheckstyle.skip=true -DskipTests -Dmaven.javadoc.skip=true
            dependencies -Pjmh -pl opennlp-core/opennlp-runtime
            CLASSPATH=$S/opennlp-core/opennlp-runtime/target/classes:$S/opennlp-core/opennlp-runtime/target/test-classes:$DEPS;;
        owasp-sanitizer)
            maven -pl java8-shim,java10-shim -am install -DskipTests -Dmaven.javadoc.skip=true -Denforcer.skip=true
            maven -pl owasp-java-html-sanitizer -am test-compile -DskipTests -Dmaven.javadoc.skip=true -Denforcer.skip=true
            dependencies -pl owasp-java-html-sanitizer -Denforcer.skip=true
            CLASSPATH=$S/owasp-java-html-sanitizer/target/classes:$S/owasp-java-html-sanitizer/target/test-classes:$DEPS
            RWD=$S/owasp-java-html-sanitizer;;
        tinylog)
            check_jdk --jdk9 "$JDK9"; BUILD_JDK=$JDK9
            maven -pl benchmarks -am install -DskipTests -Dmaven.javadoc.skip=true -Danimal.sniffer.skip=true
            dependencies -pl benchmarks
            CLASSPATH=$S/benchmarks/target/classes:$DEPS;;
        flexmark)
            maven -pl flexmark-core-test -am install -DskipTests -Dmaven.javadoc.skip=true
            dependencies -pl flexmark-core-test
            CLASSPATH=$S/flexmark-core-test/target/classes:$B/tc:$DEPS
            classes "$B/tc" "$CLASSPATH" "$S/flexmark-core-test/src/test/java/com/vladsch/flexmark/core/test/util/parser/SpecBenchmark.java";;
        re2j)
            cp "$BENCH/harness/re2j/pom.xml" "$B/pom.xml"
            (cd "$B" && "$MVN" -B "-Dmaven.repo.local=$M2" dependency:copy-dependencies "-DoutputDirectory=$B/lib")
            mapfile -d '' -t sources < <(find "$S/java" -name '*.java' -not -path '*/super/*' -print0)
            classes "$B/classes" . "${sources[@]}"
            mapfile -d '' -t sources < <(find "$S/benchmarks/src/main/java" -name '*.java' -print0)
            classes "$B/tc" "$B/classes:$B/lib/*" "${sources[@]}"
            CLASSPATH=$B/classes:$B/tc:$S/benchmarks/src/main/resources:$B/lib/jmh-core-1.21.jar:$B/lib/jopt-simple-4.6.jar:$B/lib/commons-math3-3.2.jar;;
        jsqlparser)
            check_jdk --jdk17 "$JDK17"
            toolchains "17=$JDK17"
            maven --toolchains "$B/toolchains.xml" test-compile -DskipTests
            dependencies --toolchains "$B/toolchains.xml"
            CLASSPATH=$S/target/classes:$S/target/test-classes:$DEPS
            RWD=$S;;
        handlebars)
            maven -pl handlebars -am install -DskipTests -Dmaven.javadoc.skip=true
            dependencies -pl handlebars
            CLASSPATH=$S/handlebars/target/classes:$S/handlebars/target/test-classes:$B/tc:$DEPS
            classes "$B/tc" "$CLASSPATH" "$BENCH/harness/handlebars/Hunt3BenchMain.java";;
        calcite-parser)
            check_jdk --jdk17 "$JDK17"; BUILD_JDK=$JDK17
            gradle :ubenchmark:jmhJar
            jar_match "$S/ubenchmark/build/libs/*-jmh.jar";;
        mustache)
            maven -pl compiler -am install -DskipTests -Dmaven.javadoc.skip=true
            maven -pl benchmarks package -DskipTests -Dexec.skip=true
            dependencies -pl benchmarks
            mapfile -d '' -t sources < <(find "$S/benchmarks/src/main/java/mustachejava/benchmarks" -name '*.java' -print0)
            classes "$B/tc" "$S/benchmarks/target/classes:$DEPS" "${sources[@]}"
            JAR=$S/benchmarks/target/benchmarks.jar
            "$JDK/bin/jar" uf "$JAR" -C "$B/tc" .;;
        antlr)
            maven -pl runtime-testsuite -am test-compile -DskipTests -Dmaven.javadoc.skip=true
            maven dependency:get -Dartifact=org.openjdk.jol:jol-core:0.16
            local jol=$M2/org/openjdk/jol/jol-core/0.16/jol-core-0.16.jar
            CLASSPATH=$S/runtime/Java/target/classes:$S/runtime-testsuite/target/test-classes:$S/runtime:$jol:$B/subclasses
            [[ -n $GRAALVM ]] || die "Specify --graalvm for ANTLR substitutions"
            local svm=$GRAALVM/lib/svm/builder/svm.jar
            [[ -f $svm ]] || svm=$GRAALVM/lib/svm.jar
            mapfile -d '' -t sources < <(find "$BENCH/harness/antlr" -name '*.java' -print0)
            classes "$B/subclasses" "$jol:$svm" "${sources[@]}";;
        snakeyaml|snakeyaml-engine|commons-codec)
            maven test-compile -DskipTests
            dependencies
            CLASSPATH=$S/target/classes:$S/target/test-classes:$DEPS
            if [[ $key == snakeyaml-engine ]]; then
                classes "$B/tc" "$CLASSPATH" "$S/src/test/java/org/snakeyaml/engine/v2/util/ParseBenchmark.java"
                CLASSPATH=$B/tc:$CLASSPATH
            elif [[ $key == commons-codec ]]; then
                mapfile -d '' -t sources < <(find "$BENCH/harness/commons-codec" -name '*.java' -print0)
                classes "$B/hclasses" "$CLASSPATH" "${sources[@]}"
                CLASSPATH=$B/hclasses:$CLASSPATH
            fi;;
        rhino)
            gradle :benchmarks:jmhJar
            jar_match "$S/benchmarks/build/libs/*-jmh.jar"
            RWD=$S/benchmarks;;
        java-json-benchmark)
            gradle shadowJar
            JAR=$S/build/libs/app.jar;;
        fastcsv)
            gradle -Dorg.gradle.jvmargs=-Xmx2g :lib:jmhJar
            jar_match "$S/lib/build/libs/*-jmh.jar";;
        spring-stringutils)
            check_jdk --jdk25 "$JDK25"; BUILD_JDK=$JDK25
            gradle :spring-core:jmhJar
            jar_match "$S/spring-core/build/libs/*-jmh.jar";;
        lucene-bytask)
            check_jdk --jdk25 "$JDK25"; BUILD_JDK=$JDK25
            gradle :lucene:benchmark:getEnWikiRandomLines :lucene:benchmark:assemble :lucene:benchmark-jmh:assemble -x test
            gradle -I "$BENCH/harness/lucene-bytask/initcp.gradle" :lucene:benchmark:huntClasspath -q > "$B/classpath.log"
            CLASSPATH=$(sed -n 's/^HUNTCP=//p' "$B/classpath.log")
            [[ -n $CLASSPATH ]] || die "Lucene classpath task produced no classpath"
            cp "$BENCH/harness/lucene-bytask/indexLineFile.alg" "$S/lucene/benchmark/conf/hunt3-indexLineFile-enwiki-r2.alg"
            RWD=$S/lucene/benchmark;;
        pdfbox)
            download 'https://opensource.adobe.com/dc-acrobat-sdk-docs/standards/pdfstandards/pdf/PDF32000_2008.pdf' \
                "$S/benchmark/target/pdfs/PDF32000_2008.pdf"
            maven -pl benchmark -am package -DskipTests -Ddownload.plugin.skip=true -Dmaven.javadoc.skip=true
            JAR=$S/benchmark/target/benchmarks.jar
            RWD=$S/benchmark;;
        yauaa)
            check_jdk --jdk17 "$JDK17"; check_jdk --jdk21 "$JDK21"
            toolchains "17=$JDK17" "21=$JDK21"
            maven --toolchains "$B/toolchains.xml" -PskipQuality -pl devtools,devtools/sort,analyzer \
                install -DskipTests -Dmaven.javadoc.skip=true -Dlicense.skip=true
            maven --toolchains "$B/toolchains.xml" -PskipQuality -pl benchmarks package \
                -Dmaven.compiler.proc=full -DskipTests -Dmaven.javadoc.skip=true -Dlicense.skip=true
            JAR=$S/benchmarks/target/benchmarks.jar;;
        sql-formatter)
            check_jdk --jdk17 "$JDK17"; BUILD_JDK=$JDK17
            maven package -DskipTests -Dmaven.javadoc.skip=true -Dspotless.check.skip=true
            dependencies
            CLASSPATH=$S/target/classes:$S/target/test-classes:$DEPS
            classes "$S/target/test-classes" "$CLASSPATH" "$S/src/test/java/com/github/vertical_blank/sqlformatter/Benchmark.java";;
        palantir)
            check_jdk --jdk21 "$JDK21"; BUILD_JDK=$JDK21
            gradle :palantir-java-format:classes :palantir-java-format-spi:jar
            gradle -I "$BENCH/harness/lucene-bytask/initcp.gradle" :palantir-java-format:huntClasspath -q > "$B/classpath.log"
            CLASSPATH=$(sed -n 's/^HUNTCP=//p' "$B/classpath.log")
            [[ -n $CLASSPATH ]] || die "Palantir classpath task produced no classpath";;
        jsoup-plaintext)
            maven package -DskipTests -Dmaven.javadoc.skip=true -Danimal.sniffer.skip=true
            jar_match "$S/target/*-examples.jar"
            RWD=$S;;
        thymeleaf)
            maven -f thymeleaf-benchmark01/pom.xml -P3.0.0 package -DskipTests \
                -Dmaven.compile.source=1.8 -Dmaven.compile.target=1.8
            CLASSPATH=$S/thymeleaf-benchmark01/target/thymeleaf-benchmark01.jar;;
        jte)
            build_jte;;
        *) die "Missing Java build recipe: $key";;
    esac
    {
        printf 'JAR=%q\n' "$JAR"
        printf 'CLASSPATH=%q\n' "$CLASSPATH"
        printf 'RWD=%q\n' "$RWD"
    } > "$B/target.env"
    BUILT[$key]=yes
}

build_jte() {
    local h=$BENCH/harness/jte/gg/jte/bench
    local -a JAVAC_FLAGS=(--release 17)
    mkdir -p "$B/cls/"{rt,comp,model,gentool,bench} "$B/tmpl"
    mapfile -d '' -t sources < <(find "$S/jte-runtime/src/main/java" -name '*.java' -print0)
    classes "$B/cls/rt" . "${sources[@]}"
    mapfile -d '' -t sources < <(find "$S/jte-extension-api/src/main/java" "$S/jte/src/main/java" -name '*.java' -print0)
    classes "$B/cls/comp" "$B/cls/rt" "${sources[@]}"
    local model=$S/jte/src/test/java/gg/jte/benchmark
    classes "$B/cls/model" . "$model/Page.java" "$model/WelcomePage.java" "$model/MenuItem.java"
    classes "$B/cls/gentool" "$B/cls/rt:$B/cls/comp" "$h/Gen.java"
    cp -R "$S/jte/src/test/resources/benchmark/." "$B/tmpl/"
    local generator_cp=$B/cls/rt:$B/cls/comp:$B/cls/model:$B/cls/gentool
    "$JDK/bin/java" -cp "$generator_cp" gg.jte.bench.Gen "$B/tmpl" "$B/gen-s" gg.jte.generated.s false
    "$JDK/bin/java" -cp "$generator_cp" gg.jte.bench.Gen "$B/tmpl" "$B/gen-b" gg.jte.generated.b true
    cp "$BENCH/harness/jte/pom.xml" "$B/pom.xml"
    (cd "$B" && "$MVN" -B "-Dmaven.repo.local=$M2" dependency:copy-dependencies "-DoutputDirectory=$B/lib")
    mapfile -d '' -t sources < <(find "$B/gen-s" "$B/gen-b" -name '*.java' -print0)
    classes "$B/cls/bench" "$B/cls/rt:$B/cls/model:$B/lib/*" \
        "${sources[@]}" "$S/test/jte-benchmark/src/main/java/gg/jte/TemplateOutputTest.java" \
        "$h/Variants.java" "$h/JteBench.java" "$h/Census.java" "$h/EscPage.java"
    (cd "$B/gen-b" && find . -name '*.bin' -exec cp --parents {} "$B/cls/bench/" \;)
    CLASSPATH=$B/cls/rt:$B/cls/model:$B/cls/bench:$B/lib/jmh-core-1.37.jar:$B/lib/jopt-simple-5.0.4.jar:$B/lib/commons-math3-3.6.1.jar
}

build_native() {
    local name=$1 key=$2 JAR CLASSPATH RWD
    local B=$BUILDS/$key
    [[ -f "$B/target.env" ]] || die "Build Java workload first: $name"
    source "$B/target.env"
    case $key:$name in
        dacapo:*) JAR=$B/suite/launchers/$name.jar;;
        lucene-bytask:lucene-jmh)
            CLASSPATH=$(find "$SOURCES/lucene-bytask/lucene/benchmark-jmh/build/benchmarks" -maxdepth 1 -name '*.jar' -print | sort | paste -sd:)
            [[ -n $CLASSPATH ]] || die "Lucene JMH JARs are missing";;
    esac
    local config_root=$BENCH/config/$name config_dirs="" count i arg gv variant
    count=$(cat "$BENCH/recipes/$name/config-count")
    for ((i=0;i<count;i++)); do
        [[ -d "$config_root/$i" ]] || die "Missing native-image configuration: $name/$i"
        config_dirs+="${config_dirs:+,}$config_root/$i"
    done
    local args=()
    while IFS= read -r arg; do
        case $arg in
            @CLASSPATH@) [[ -n $CLASSPATH ]] || die "Missing classpath: $name"; arg=$CLASSPATH;;
            @JAR@) [[ -f $JAR ]] || die "Missing JAR: $JAR"; arg=$JAR;;
            @CONFIG@) arg="-H:ConfigurationFileDirectories=$config_dirs";;
        esac
        arg=${arg//@CONFIG_ROOT@/$config_root}
        args+=("$arg")
    done < "$BENCH/recipes/$name/native.args"
    mkdir -p "$BUILDS/$name/native" "$RWD"
    for variant in "${VARIANTS[@]}"; do
        local flags=("--parallelism=$PARALLELISM" --no-fallback --enable-monitoring=jfr \
            -H:+UnlockExperimentalVMOptions "-H:CodeAlignment=$ALIGNMENT" "-J-Xmx$HEAP")
        gv=$GRAALVM
        if [[ $variant == BASE ]]; then
            gv=$BASELINE
        else
            flags+=(-H:+StringAnalysis -H:+StringAnalysisKeepProfile \
                "-J-Dsvm.stringanalysis.fwd.threads=$PARALLELISM" \
                -J-Dsvm.stringanalysis.fwd.rtrack.ctxk=1 \
                -J-Dsvm.stringanalysis.fwd.rtrack.pathk=1 \
                -J-Dsvm.stringanalysis.fwd.rtrack.pathk.bwd=1)
            case $variant in
                SBS) flags+=(-H:+StringAnalysisSingleByteOnly);;
                SV) flags+=(-H:+StringAnalysisStringViewOnly);;
                LS) flags+=(-H:+StringAnalysisLazyConcatOnly);;
            esac
        fi
        printf 'Building %s %s\n' "$name" "$variant"
        (cd "$RWD" && JAVA_HOME=$gv PATH="$gv/bin:$PATH" \
            "$gv/bin/native-image" "${flags[@]}" "${args[@]}" \
            -o "$BUILDS/$name/native/$variant") \
            > "$BUILDS/$name/native/$variant.log" 2>&1 \
            || die "Native build failed; see $BUILDS/$name/native/$variant.log"
    done
}

for name in "${NAMES[@]}"; do
    key=$(source_key "$name")
    printf '%s\n' "$name"
    case $key in
        StringBuilders|StringBuffers|StringBuilderToString|StringConcat|StringConcatStartup|StringJoiner|StringSubstring|jsonparser|regex-redux) ;;
        *) [[ $STAGE == native ]] || fetch_repo "$key";;
    esac
    case $STAGE in
        fetch) ;;
        java) build_java "$key";;
        native) build_native "$name" "$key";;
        all) build_java "$key"; build_native "$name" "$key";;
    esac
done
