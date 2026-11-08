#!/bin/bash
# Builds every version with the sanitizers on and checks what programs print.
cd "$(dirname "$0")" || exit 1

failed=0
FLAGS="-std=c99 -Wall -Wextra -Wno-unused-parameter -Werror -g -fsanitize=address,undefined"
export ASAN_OPTIONS=abort_on_error=0

build() {
  (cd "$1" && cc $FLAGS *.c -o clox -lm) || { echo "BUILD FAILED $1"; exit 1; }
}

# expect <dir> <expected exit code> <expected output> <program>
expect() {
  local file actual code
  file=$(mktemp)
  printf '%s' "$4" > "$file"
  actual=$("$1/clox" "$file" 2>&1)
  code=$?
  rm -f "$file"
  if [ "$code" != "$2" ] || [ "$actual" != "$3" ]; then
    echo "FAIL [$1] $4"
    echo "  expected ($2): $3"
    echo "  actual   ($code): $actual"
    failed=1
  fi
}

# Chapter 22 behavior. ch23 builds on ch22, so it has to pass these too.
for dir in ch22 ch23; do
  build "$dir"
  expect "$dir" 0 '3' 'print 1 + 2;'
  expect "$dir" 0 'inner
outer' '{ var a = "outer"; { var a = "inner"; print a; } print a; }'
  expect "$dir" 0 'g!?' 'var g = "g"; { var x = g + "!"; x = x + "?"; print x; }'
  expect "$dir" 0 '5
5' '{ var a; var b; a = b = 5; print a; print b; }'
  expect "$dir" 0 '2' 'var a = 1; var a = 2; print a;'
  expect "$dir" 65 "[line 1] Error at 'a': Can't read local variable in its own initializer." \
    '{ var a = "outer"; { var a = a; } }'
  expect "$dir" 65 "[line 1] Error at 'a': Already a variable with this name in this scope." \
    '{ var a = 1; var a = 2; }'
  expect "$dir" 70 "Undefined variable 'nope'.
[line 1] in script" '{ var a = 1; } print a = nope;'

  # Challenge 3: const.
  expect "$dir" 0 '3' '{ const c = 3; print c; }'
  expect "$dir" 0 '10' 'const k = 2; print k * 5;'
  expect "$dir" 65 "[line 1] Error at '=': Can't assign to a constant." '{ const c = 3; c = 4; }'
  expect "$dir" 65 "[line 1] Error at '=': Can't assign to a constant." 'const g = 1; g = 2;'
  expect "$dir" 65 "[line 1] Error at '=': Can't assign to a constant." '{ const c = 1; { var d; d = c = 2; } }'
  expect "$dir" 65 "[line 1] Error at ';': Expect '=' after constant name." '{ const c; }'
  expect "$dir" 0 '6
1' 'const g = 1; { var g = 5; g = 6; print g; } print g;'
  expect "$dir" 0 '3' 'const g = 1; var g = 2; g = 3; print g;'
  out=$(printf 'const z = 1;\nz = 2;\nprint z;\n' | "$dir/clox" 2>&1 >/dev/null)
  [ "$out" = "[line 1] Error at '=': Can't assign to a constant." ] ||
    { echo "FAIL [$dir] const across REPL lines: $out"; failed=1; }

  # Challenge 4: more than 256 locals.
  many=$(mktemp)
  { echo '{'; for i in $(seq 0 299); do echo "var v$i = $i;"; done
    echo 'v299 = v299 + v0 + v255 + v256; print v299; print v1 + v298; }'; } > "$many"
  out=$("$dir/clox" "$many" 2>&1)
  [ "$out" = "810
299" ] || { echo "FAIL [$dir] 300 locals: $out"; failed=1; }

  # 65,536 locals is the most a two byte slot can name. They are split into 256
  # nested blocks, since the duplicate check scans the whole current scope and
  # 65,536 names in one scope takes seconds to compile.
  python3 -c "
for b in range(256):
    print('{')
    for i in range(256): print('var v%d = %d;' % (b * 256 + i, b * 256 + i))
print('print v65535 + v0 + v300;')
print('}' * 256)" > "$many"
  out=$("$dir/clox" "$many" 2>&1)
  [ "$out" = "65835" ] || { echo "FAIL [$dir] 65536 locals: $out"; failed=1; }
  python3 -c "
for b in range(257):
    print('{')
    for i in range(256): print('var v%d;' % (b * 256 + i))
print('}' * 257)" > "$many"
  out=$("$dir/clox" "$many" 2>&1 | head -1)
  [ "$out" = "[line 65794] Error at 'v65536': Too many local variables in function." ] ||
    { echo "FAIL [$dir] local limit: $out"; failed=1; }
  rm -f "$many"
done

# Chapter 23 behavior.
d=ch23
expect $d 0 'yes
else
or
2
nil' 'if (1 < 2) print "yes"; else print "no"; if (nil) print "x"; else print "else";
print false or "or"; print 1 and 2; print nil and 3;'
expect $d 0 '0
1
2
0
10
20' 'var i = 0; while (i < 3) { print i; i = i + 1; }
for (var j = 0; j < 3; j = j + 1) print j * 10;'

# Challenge 1: switch.
expect $d 0 'zero
one
other
other' 'for (var i = 0; i < 4; i = i + 1) {
  switch (i) { case 0: print "zero"; case 1: print "one"; default: print "other"; }
}'
expect $d 0 '2
after' 'switch ("b") { case "a": print 1; case "b": print 2; case "c": print 3; } print "after";'
expect $d 0 'none' 'switch (9) { case 1: print 1; } print "none";'
expect $d 0 'empty' 'switch (1) {} print "empty";'
# Case values are full expressions, and only the first match runs.
expect $d 0 'first' 'switch (2) { case 1 + 1: print "first"; case 2: print "second"; }'
expect $d 65 "[line 1] Error at 'print': Can't have statements before any case." \
  'switch (1) { print 1; case 1: print 2; }'
expect $d 65 "[line 1] Error at 'case': Can't have another case or default after the default case." \
  'switch (1) { default: print 1; case 1: print 2; }'

# Challenge 2: continue.
expect $d 0 '0
2
6
10' 'for (var i = 0; i < 6; i = i + 1) {
  var x = i * 2;
  { var y = x; if (i == 2 or i == 4) continue; }
  print x;
}'
expect $d 0 '1
4
16
25' 'var i = 0; while (i < 5) { i = i + 1; var sq = i * i; if (sq == 9) continue; print sq; }'
expect $d 0 '0
2
10
12' 'for (var i = 0; i < 2; i = i + 1) {
  for (var j = 0; j < 3; j = j + 1) { if (j == 1) continue; print i * 10 + j; }
}'
# Continue inside a switch has to pop the switch value too. If any slot is
# left behind, "after" reads the wrong stack slot.
expect $d 0 '0
2
bok' '{
  var before = "b";
  for (var i = 0; i < 3; i = i + 1) {
    var a = 1;
    switch (i) { case 1: { var z = 2; continue; } default: print i; }
  }
  var after = "ok";
  print before + after;
}'
expect $d 65 "[line 1] Error at 'continue': Can't use 'continue' outside of a loop." 'continue;'
expect $d 65 "[line 1] Error at 'continue': Can't use 'continue' outside of a loop." \
  'for (var i = 0; i < 1; i = i + 1) {} continue;'

if [ "$failed" = 0 ]; then
  echo "all tests passed"
else
  exit 1
fi
