#ifndef clox_vm_h
#define clox_vm_h

#include "chunk.h"
#include "table.h"
#include "value.h"

#define STACK_INITIAL 256

typedef struct {
  Chunk* chunk;
  uint8_t* ip;
  Value* stack;
  int stackCapacity;
  Value* stackTop;
  Table globals;
  // Names of globals declared with const. The compiler checks these, and they
  // live here so they carry over from one REPL line to the next.
  Table constGlobals;
  Table strings;
  Obj* objects;
} VM;

typedef enum {
  INTERPRET_OK,
  INTERPRET_COMPILE_ERROR,
  INTERPRET_RUNTIME_ERROR
} InterpretResult;

extern VM vm;

void initVM(void);
void freeVM(void);
InterpretResult interpret(const char* source);
void push(Value value);
Value pop(void);

#endif
