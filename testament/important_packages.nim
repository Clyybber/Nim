import strutils

template pkg(name: string; cmd = "nimble test"; version = ""; hasDeps = false): untyped =
  packages.add((name, cmd, version, hasDeps))

var packages*: seq[tuple[name, cmd, version: string; hasDeps: bool]] = @[]


pkg "argparse"
pkg "arraymancer", "nim c -r src/arraymancer.nim", "", true
pkg "ast_pattern_matching", "nim c -r tests/test1.nim"
pkg "binaryheap", "nim c -r binaryheap.nim"
pkg "blscurve", "", "", true
pkg "bncurve", "", "", true
pkg "c2nim", "nim c testsuite/tester.nim"
pkg "cascade"
pkg "chroma"
pkg "chroma"
pkg "chronicles", "nim c -o:chr -r chronicles.nim", "", true
pkg "chrono", "", "", true
pkg "chronos"
pkg "cligen", "nim c -o:cligenn -r cligen.nim"
pkg "combparser"
pkg "compactdict"
pkg "criterion"
pkg "dashing", "nim c tests/functional.nim"
pkg "docopt"
pkg "flippy", "", "", true
pkg "fragments", "nim c -r fragments/dsl.nim"
pkg "gara"
pkg "glm"
pkg "glob"
pkg "gnuplot"
# pkg "graphemes"
pkg "hts", "nim c -o:htss -r src/hts.nim"
pkg "inim"
pkg "itertools", "nim doc src/itertools.nim"
pkg "iterutils"
pkg "jstin"
pkg "karax", "nim c -r tests/tester.nim"
pkg "loopfusion"
pkg "nake", "nim c nakefile.nim"
pkg "neo", "nim c -d:blas=openblas tests/all.nim", "", true
pkg "nicy", "nim c src/nicy.nim"
pkg "nigui", "nim c -o:niguii -r src/nigui.nim"
pkg "nimcrypto", "nim c -r tests/testapi.nim"
pkg "NimData", "nim c -o:nimdataa src/nimdata.nim", "", true
pkg "nimes", "nim c src/nimes.nim", "", true
pkg "nimgame2", "nim c nimgame2/nimgame.nim", "", true
pkg "nimgen", "", "", true
pkg "nimhdf5", "", "", true
pkg "nimi3status", "nim c nimi3status.nim", "", true
pkg "nimlsp", "", "", true
pkg "nimly", "nim c -r tests/test_nimly", "", true
pkg "nimongo", "nimble test_ci", "", true
pkg "nimpy", "nim c -r tests/nimfrompy.nim"
pkg "nimquery"
pkg "nimsl", "", "", true
pkg "nimsvg"
pkg "nimx", "nim c --threads:on test/main.nim", "", true
pkg "norm", "nim c -o:normm src/norm.nim"
pkg "normalize", "", "", true
pkg "npeg"
pkg "ormin", "nim c -o:orminn ormin.nim", "", true
pkg "parsetoml"
pkg "patty"
pkg "plotly", "nim c examples/all.nim", "", true
pkg "protobuf", "nim c -o:protobuff -r src/protobuf.nim", "", true
# pkg "redis"
pkg "regex", "nim c src/regex", "", true
pkg "result", "nim c -r result.nim"
pkg "ringdeque"
pkg "rosencrantz", "nim c -o:rsncntz -r rosencrantz.nim"
pkg "sdl1", "nim c -r src/sdl.nim"
pkg "sdl2_nim", "nim c -r sdl2/sdl.nim"
pkg "stint", "nim c -o:stintt -r stint.nim"
pkg "strunicode", "nim c -r src/strunicode.nim", "", true
pkg "timezones"
pkg "tiny_sqlite" # or tinysqlite?
pkg "typography", "", "", true
pkg "unicodedb"
pkg "unicodeplus", "", "", true
pkg "unpack"
pkg "untar", "nim c -o:untarr -r src/untar.nim"
pkg "yaml"
pkg "zero_functional", "nim c -r test.nim"
