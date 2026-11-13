analyzer=org.apache.lucene.analysis.core.SimpleAnalyzer
content.source=org.apache.lucene.benchmark.byTask.feeds.LineDocSource
docs.file=work/enwiki.random.lines.txt
content.source.forever=false
# C101 align (supervisor 2026-11-11): 2-round copy of hunt3-indexLineFile-enwiki-r3.alg (lucene/benchmark/conf, unchanged).
# ONLY change: the third round (ResetSystemErase CreateIndex { "AddDocR2" AddDoc } : * CloseIndex) is removed. Round 0 =
# warm-up (info), round 1 = the measured round. Properties, task classes, the line file (relative to the run dir RWD =
# lucene/benchmark) and the final RepSumByPref AddDoc are identical. Used via the kit overlay rows-overlay/lucene-bytask.sh.
ResetSystemErase
CreateIndex
{ "AddDocR0" AddDoc } : *
CloseIndex
ResetSystemErase
CreateIndex
{ "AddDocR1" AddDoc } : *
CloseIndex
RepSumByPref AddDoc
