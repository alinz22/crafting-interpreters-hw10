#include <stdarg.h>
#include <stdio.h>
#ifdef BENCH_TIMING
#include <time.h>
#endif
#include <string.h>

#include "common.h"
#include "compiler.h"
#include "debug.h"
#include "memory.h"
#include "object.h"
#include "vm.h"

VM vm;

static void resetStack(void) {
  vm.stackTop = vm.stack;
}

static void runtimeError(const char* format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  va_end(args);
  fputs("\n", stderr);

  int instruction = (int)(vm.ip - vm.chunk->code - 1);
  int line = getLine(vm.chunk, instruction);
  fprintf(stderr, "[line %d] in script\n", line);
  resetStack();
}

void initVM(void) {
  vm.stack = GROW_ARRAY(Value, NULL, 0, STACK_INITIAL);
  vm.stackCapacity = STACK_INITIAL;
  resetStack();
  vm.objects = NULL;
  initTable(&vm.globals);
  initTable(&vm.constGlobals);
  initTable(&vm.strings);
}

void freeVM(void) {
  FREE_ARRAY(Value, vm.stack, vm.stackCapacity);
  vm.stack = NULL;
  vm.stackCapacity = 0;
  freeTable(&vm.globals);
  freeTable(&vm.constGlobals);
  freeTable(&vm.strings);
  freeObjects();
}

void push(Value value) {
  int count = (int)(vm.stackTop - vm.stack);
  if (count == vm.stackCapacity) {
    int oldCapacity = vm.stackCapacity;
    vm.stackCapacity = GROW_CAPACITY(oldCapacity);
    vm.stack = GROW_ARRAY(Value, vm.stack, oldCapacity, vm.stackCapacity);
    vm.stackTop = vm.stack + count;
  }
  *vm.stackTop = value;
  vm.stackTop++;
}

Value pop(void) {
  vm.stackTop--;
  return *vm.stackTop;
}

static Value peek(int distance) {
  return vm.stackTop[-1 - distance];
}

static bool isFalsey(Value value) {
  return IS_NIL(value) || (IS_BOOL(value) && !AS_BOOL(value));
}

static void concatenate(void) {
  ObjString* b = AS_STRING(pop());
  ObjString* a = AS_STRING(pop());

  int length = a->length + b->length;
  char* chars = ALLOCATE(char, length + 1);
  memcpy(chars, a->chars, a->length);
  memcpy(chars + a->length, b->chars, b->length);
  chars[length] = '\0';

  ObjString* result = takeString(chars, length);
  push(OBJ_VAL(result));
}

static InterpretResult run(void) {
#define READ_BYTE() (*vm.ip++)
#define READ_SHORT() \
    (vm.ip += 2, (uint16_t)((vm.ip[-2] << 8) | vm.ip[-1]))
#define READ_CONSTANT() (vm.chunk->constants.values[READ_BYTE()])
#define READ_STRING() AS_STRING(READ_CONSTANT())
#define BINARY_OP(valueType, op) \
    do { \
      if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) { \
        runtimeError("Operands must be numbers."); \
        return INTERPRET_RUNTIME_ERROR; \
      } \
      double b = AS_NUMBER(pop()); \
      double a = AS_NUMBER(peek(0)); \
      vm.stackTop[-1] = valueType(a op b); \
    } while (false)

  for (;;) {
    uint8_t instruction;
    switch (instruction = READ_BYTE()) {
      case OP_CONSTANT:
        push(READ_CONSTANT());
        break;
      case OP_CONSTANT_LONG: {
        int index = READ_BYTE();
        index |= READ_BYTE() << 8;
        index |= READ_BYTE() << 16;
        push(vm.chunk->constants.values[index]);
        break;
      }
      case OP_NIL:   push(NIL_VAL); break;
      case OP_TRUE:  push(BOOL_VAL(true)); break;
      case OP_FALSE: push(BOOL_VAL(false)); break;
      case OP_POP:   pop(); break;
      case OP_GET_LOCAL: {
        uint8_t slot = READ_BYTE();
        push(vm.stack[slot]);
        break;
      }
      case OP_SET_LOCAL: {
        uint8_t slot = READ_BYTE();
        vm.stack[slot] = peek(0);
        break;
      }
      case OP_GET_LOCAL_LONG: {
        uint16_t slot = READ_SHORT();
        push(vm.stack[slot]);
        break;
      }
      case OP_SET_LOCAL_LONG: {
        uint16_t slot = READ_SHORT();
        vm.stack[slot] = peek(0);
        break;
      }
      case OP_GET_GLOBAL: {
        ObjString* name = READ_STRING();
        Value value;
        if (!tableGet(&vm.globals, OBJ_VAL(name), &value)) {
          runtimeError("Undefined variable '%s'.", name->chars);
          return INTERPRET_RUNTIME_ERROR;
        }
        push(value);
        break;
      }
      case OP_DEFINE_GLOBAL: {
        ObjString* name = READ_STRING();
        tableSet(&vm.globals, OBJ_VAL(name), peek(0));
        pop();
        break;
      }
      case OP_SET_GLOBAL: {
        ObjString* name = READ_STRING();
        if (tableSet(&vm.globals, OBJ_VAL(name), peek(0))) {
          tableDelete(&vm.globals, OBJ_VAL(name));
          runtimeError("Undefined variable '%s'.", name->chars);
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_ZERO:  push(NUMBER_VAL(0)); break;
      case OP_ONE:   push(NUMBER_VAL(1)); break;
      case OP_EQUAL: {
        Value b = pop();
        vm.stackTop[-1] = BOOL_VAL(valuesEqual(peek(0), b));
        break;
      }
      case OP_NOT_EQUAL: {
        Value b = pop();
        vm.stackTop[-1] = BOOL_VAL(!valuesEqual(peek(0), b));
        break;
      }
      case OP_GREATER:       BINARY_OP(BOOL_VAL, >); break;
      case OP_GREATER_EQUAL: BINARY_OP(BOOL_VAL, >=); break;
      case OP_LESS:          BINARY_OP(BOOL_VAL, <); break;
      case OP_LESS_EQUAL:    BINARY_OP(BOOL_VAL, <=); break;
      case OP_ADD: {
        if (IS_STRING(peek(0)) && IS_STRING(peek(1))) {
          concatenate();
        } else if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          double b = AS_NUMBER(pop());
          double a = AS_NUMBER(pop());
          push(NUMBER_VAL(a + b));
        } else {
          runtimeError("Operands must be two numbers or two strings.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_SUBTRACT:      BINARY_OP(NUMBER_VAL, -); break;
      case OP_MULTIPLY:      BINARY_OP(NUMBER_VAL, *); break;
      case OP_DIVIDE:        BINARY_OP(NUMBER_VAL, /); break;
      case OP_NOT:
        vm.stackTop[-1] = BOOL_VAL(isFalsey(peek(0)));
        break;
      case OP_NEGATE:
        if (!IS_NUMBER(peek(0))) {
          runtimeError("Operand must be a number.");
          return INTERPRET_RUNTIME_ERROR;
        }
        vm.stackTop[-1] = NUMBER_VAL(-AS_NUMBER(peek(0)));
        break;
      case OP_CONDITIONAL: {
        Value elseValue = pop();
        Value thenValue = pop();
        vm.stackTop[-1] = isFalsey(peek(0)) ? elseValue : thenValue;
        break;
      }
      case OP_PRINT:
        printValue(pop());
        printf("\n");
        break;
      case OP_RETURN:
        // Exit interpreter.
        return INTERPRET_OK;
    }
  }

#undef READ_BYTE
#undef READ_SHORT
#undef READ_CONSTANT
#undef READ_STRING
#undef BINARY_OP
}

InterpretResult interpret(const char* source) {
  Chunk chunk;
  initChunk(&chunk);

#ifdef BENCH_TIMING
  clock_t compileStart = clock();
#endif

  if (!compile(source, &chunk)) {
    freeChunk(&chunk);
    return INTERPRET_COMPILE_ERROR;
  }

  vm.chunk = &chunk;
  vm.ip = vm.chunk->code;
  resetStack();

#ifdef BENCH_TIMING
  clock_t runStart = clock();
#endif

  InterpretResult result = run();

#ifdef BENCH_TIMING
  fprintf(stderr, "compile %.3fs  run %.3fs\n",
          (double)(runStart - compileStart) / CLOCKS_PER_SEC,
          (double)(clock() - runStart) / CLOCKS_PER_SEC);
#endif

  freeChunk(&chunk);
  return result;
}
