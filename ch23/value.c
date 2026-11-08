#include <stdio.h>
#include <string.h>

#include "object.h"
#include "memory.h"
#include "value.h"

void initValueArray(ValueArray* array) {
  array->values = NULL;
  array->capacity = 0;
  array->count = 0;
}

void writeValueArray(ValueArray* array, Value value) {
  if (array->capacity < array->count + 1) {
    int oldCapacity = array->capacity;
    array->capacity = GROW_CAPACITY(oldCapacity);
    array->values = GROW_ARRAY(Value, array->values, oldCapacity, array->capacity);
  }
  array->values[array->count] = value;
  array->count++;
}

void freeValueArray(ValueArray* array) {
  FREE_ARRAY(Value, array->values, array->capacity);
  initValueArray(array);
}

void printValue(Value value) {
  switch (value.type) {
    case VAL_BOOL:
      printf(AS_BOOL(value) ? "true" : "false");
      break;
    case VAL_NIL: printf("nil"); break;
    case VAL_NUMBER: printf("%g", AS_NUMBER(value)); break;
    case VAL_OBJ: printObject(value); break;
    case VAL_EMPTY: printf("<empty>"); break;
  }
}

bool valuesEqual(Value a, Value b) {
  if (a.type != b.type) return false;
  switch (a.type) {
    case VAL_BOOL:   return AS_BOOL(a) == AS_BOOL(b);
    case VAL_NIL:    return true;
    case VAL_NUMBER: return AS_NUMBER(a) == AS_NUMBER(b);
    // Every string is interned, so comparing pointers is enough.
    case VAL_OBJ:    return AS_OBJ(a) == AS_OBJ(b);
    case VAL_EMPTY:  return true;
    default:         return false;
  }
}

static uint32_t hashNumber(double value) {
#ifdef NAIVE_NUMBER_HASH
  // Adds the two halves of the bits. Small integers leave the low bits zero,
  // which is all a power of two capacity looks at.
  value += 1.0;
  uint32_t halves[2];
  memcpy(halves, &value, sizeof(value));
  return halves[0] + halves[1];
#else
  // -0 and 0 are equal, so they have to land in the same bucket.
  if (value == 0) value = 0;

  uint64_t bits;
  memcpy(&bits, &value, sizeof(bits));

  // The MurmurHash3 finalizer, which spreads the high bits down to the low ones.
  bits ^= bits >> 33;
  bits *= 0xff51afd7ed558ccdULL;
  bits ^= bits >> 33;
  bits *= 0xc4ceb9fe1a85ec53ULL;
  bits ^= bits >> 33;
  return (uint32_t)bits;
#endif
}

uint32_t hashValue(Value value) {
  switch (value.type) {
    case VAL_BOOL:   return AS_BOOL(value) ? 3 : 5;
    case VAL_NIL:    return 7;
    case VAL_NUMBER: return hashNumber(AS_NUMBER(value));
    case VAL_OBJ:    return AS_STRING(value)->hash;
    case VAL_EMPTY:  return 0;
  }
  return 0;
}
