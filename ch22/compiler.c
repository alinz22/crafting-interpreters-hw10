#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "compiler.h"
#include "debug.h"
#include "memory.h"
#include "object.h"
#include "scanner.h"
#include "table.h"
#include "vm.h"

typedef struct {
  Token current;
  Token previous;
  bool hadError;
  bool panicMode;
} Parser;

typedef enum {
  PREC_NONE,
  PREC_ASSIGNMENT,  // =
  PREC_CONDITIONAL, // ?:
  PREC_OR,          // or
  PREC_AND,         // and
  PREC_EQUALITY,    // == !=
  PREC_COMPARISON,  // < > <= >=
  PREC_TERM,        // + -
  PREC_FACTOR,      // * /
  PREC_UNARY,       // ! -
  PREC_CALL,        // . ()
  PREC_PRIMARY
} Precedence;

static const char* precedenceNames[] = {
  "PREC_NONE", "PREC_ASSIGNMENT", "PREC_CONDITIONAL", "PREC_OR", "PREC_AND",
  "PREC_EQUALITY", "PREC_COMPARISON", "PREC_TERM", "PREC_FACTOR",
  "PREC_UNARY", "PREC_CALL", "PREC_PRIMARY"
};

typedef void (*ParseFn)(bool canAssign);

typedef struct {
  ParseFn prefix;
  ParseFn infix;
  Precedence precedence;
} ParseRule;

typedef struct {
  Token name;
  int depth;
  bool isConst;
} Local;

typedef struct {
  // Grows as needed, since a 16-bit slot allows up to 65,536 locals and a fixed
  // array that big would be too large to keep on the C stack.
  Local* locals;
  int localCount;
  int localCapacity;
  int scopeDepth;
} Compiler;

Parser parser;
Compiler* current = NULL;
Chunk* compilingChunk;
bool traceParser = false;
// Identifier name to its slot in the current chunk's constant table.
static Table stringConstants;
static int traceDepth = 0;

static void traceEnter(const char* name, const char* detail) {
  if (!traceParser) return;
  for (int i = 0; i < traceDepth; i++) printf("| ");
  printf("%s%s\n", name, detail);
  traceDepth++;
}

static void traceExit(void) {
  if (traceParser) traceDepth--;
}

static Chunk* currentChunk(void) {
  return compilingChunk;
}

static void errorAt(Token* token, const char* message) {
  if (parser.panicMode) return;
  parser.panicMode = true;
  fprintf(stderr, "[line %d] Error", token->line);

  if (token->type == TOKEN_EOF) {
    fprintf(stderr, " at end");
  } else if (token->type == TOKEN_ERROR) {
  } else {
    fprintf(stderr, " at '%.*s'", token->length, token->start);
  }

  fprintf(stderr, ": %s\n", message);
  parser.hadError = true;
}

static void error(const char* message) {
  errorAt(&parser.previous, message);
}

static void errorAtCurrent(const char* message) {
  errorAt(&parser.current, message);
}

static void advance(void) {
  parser.previous = parser.current;

  for (;;) {
    parser.current = scanToken();
    if (parser.current.type != TOKEN_ERROR) break;

    errorAtCurrent(parser.current.start);
  }
}

static void consume(TokenType type, const char* message) {
  if (parser.current.type == type) {
    advance();
    return;
  }

  errorAtCurrent(message);
}

static bool check(TokenType type) {
  return parser.current.type == type;
}

static bool match(TokenType type) {
  if (!check(type)) return false;
  advance();
  return true;
}

static void emitByte(uint8_t byte) {
  writeChunk(currentChunk(), byte, parser.previous.line);
}

static void emitReturn(void) {
  emitByte(OP_RETURN);
}

static void emitConstant(Value value) {
  writeConstant(currentChunk(), value, parser.previous.line);
}

static void initCompiler(Compiler* compiler) {
  compiler->locals = NULL;
  compiler->localCount = 0;
  compiler->localCapacity = 0;
  compiler->scopeDepth = 0;
  current = compiler;
}

static void freeCompiler(Compiler* compiler) {
  FREE_ARRAY(Local, compiler->locals, compiler->localCapacity);
  initCompiler(compiler);
}

// Uses the one byte form when the slot fits, and the two byte form otherwise.
static void emitLocal(uint8_t shortOp, uint8_t longOp, int slot) {
  if (slot <= UINT8_MAX) {
    emitByte(shortOp);
    emitByte((uint8_t)slot);
  } else {
    emitByte(longOp);
    emitByte((slot >> 8) & 0xff);
    emitByte(slot & 0xff);
  }
}

static void endCompiler(void) {
  emitReturn();
  if (traceParser && !parser.hadError) {
    disassembleChunk(currentChunk(), "code");
  }
}

static void expression(void);
static void statement(void);
static void declaration(void);
static ParseRule* getRule(TokenType type);
static void parsePrecedence(Precedence precedence);

static void varDeclaration(bool isConst);

static void beginScope(void) {
  current->scopeDepth++;
}

static void endScope(void) {
  current->scopeDepth--;

  while (current->localCount > 0 &&
         current->locals[current->localCount - 1].depth >
            current->scopeDepth) {
    emitByte(OP_POP);
    current->localCount--;
  }
}

static uint8_t makeConstant(Value value) {
  int constant = addConstant(currentChunk(), value);
  if (constant > UINT8_MAX) {
    error("Too many constants in one chunk.");
    return 0;
  }
  return (uint8_t)constant;
}

static uint8_t identifierConstant(Token* name) {
  ObjString* string = copyString(name->start, name->length);

  Value index;
  if (tableGet(&stringConstants, OBJ_VAL(string), &index)) {
    return (uint8_t)AS_NUMBER(index);
  }

  uint8_t constant = makeConstant(OBJ_VAL(string));
  tableSet(&stringConstants, OBJ_VAL(string), NUMBER_VAL((double)constant));
  return constant;
}

static bool identifiersEqual(Token* a, Token* b) {
  if (a->length != b->length) return false;
  return memcmp(a->start, b->start, a->length) == 0;
}

static int resolveLocal(Compiler* compiler, Token* name) {
  for (int i = compiler->localCount - 1; i >= 0; i--) {
    Local* local = &compiler->locals[i];
    if (identifiersEqual(name, &local->name)) {
      if (local->depth == -1) {
        error("Can't read local variable in its own initializer.");
      }
      return i;
    }
  }

  return -1;
}

static bool isConstGlobal(Token* name) {
  Value unused;
  ObjString* string = copyString(name->start, name->length);
  return tableGet(&vm.constGlobals, OBJ_VAL(string), &unused);
}

static void namedVariable(Token name, bool canAssign) {
  int slot = resolveLocal(current, &name);

  if (canAssign && match(TOKEN_EQUAL)) {
    bool isConst = slot != -1 ? current->locals[slot].isConst
                              : isConstGlobal(&name);
    if (isConst) error("Can't assign to a constant.");

    expression();
    if (slot != -1) {
      emitLocal(OP_SET_LOCAL, OP_SET_LOCAL_LONG, slot);
    } else {
      emitByte(OP_SET_GLOBAL);
      emitByte(identifierConstant(&name));
    }
  } else if (slot != -1) {
    emitLocal(OP_GET_LOCAL, OP_GET_LOCAL_LONG, slot);
  } else {
    emitByte(OP_GET_GLOBAL);
    emitByte(identifierConstant(&name));
  }
}

static void variable(bool canAssign) {
  namedVariable(parser.previous, canAssign);
}

static void binary(bool canAssign) {
  TokenType operatorType = parser.previous.type;
  char detail[32];
  snprintf(detail, sizeof(detail), " for \"%.*s\"", parser.previous.length, parser.previous.start);
  traceEnter("binary", detail);
  ParseRule* rule = getRule(operatorType);
  parsePrecedence((Precedence)(rule->precedence + 1));

  switch (operatorType) {
    case TOKEN_BANG_EQUAL:    emitByte(OP_NOT_EQUAL); break;
    case TOKEN_EQUAL_EQUAL:   emitByte(OP_EQUAL); break;
    case TOKEN_GREATER:       emitByte(OP_GREATER); break;
    case TOKEN_GREATER_EQUAL: emitByte(OP_GREATER_EQUAL); break;
    case TOKEN_LESS:          emitByte(OP_LESS); break;
    case TOKEN_LESS_EQUAL:    emitByte(OP_LESS_EQUAL); break;
    case TOKEN_PLUS:          emitByte(OP_ADD); break;
    case TOKEN_MINUS:         emitByte(OP_SUBTRACT); break;
    case TOKEN_STAR:          emitByte(OP_MULTIPLY); break;
    case TOKEN_SLASH:         emitByte(OP_DIVIDE); break;
    default: break;
  }
  traceExit();
}

static void literal(bool canAssign) {
  switch (parser.previous.type) {
    case TOKEN_FALSE: emitByte(OP_FALSE); break;
    case TOKEN_NIL:   emitByte(OP_NIL); break;
    case TOKEN_TRUE:  emitByte(OP_TRUE); break;
    default: break;
  }
}

static void conditional(bool canAssign) {
  traceEnter("conditional", "");
  parsePrecedence(PREC_ASSIGNMENT);
  consume(TOKEN_COLON, "Expect ':' after then branch of conditional.");
  parsePrecedence(PREC_CONDITIONAL);
  emitByte(OP_CONDITIONAL);
  traceExit();
}

static void grouping(bool canAssign) {
  traceEnter("grouping", "");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
  traceExit();
}

static void number(bool canAssign) {
  char detail[64];
  snprintf(detail, sizeof(detail), " %.*s", parser.previous.length, parser.previous.start);
  traceEnter("number", detail);
  double value = strtod(parser.previous.start, NULL);
  if (value == 0 && !signbit(value)) {
    emitByte(OP_ZERO);
  } else if (value == 1) {
    emitByte(OP_ONE);
  } else {
    emitConstant(NUMBER_VAL(value));
  }
  traceExit();
}

static void string(bool canAssign) {
  emitConstant(OBJ_VAL(copyString(parser.previous.start + 1,
                                  parser.previous.length - 2)));
}

static void unary(bool canAssign) {
  TokenType operatorType = parser.previous.type;
  char detail[32];
  snprintf(detail, sizeof(detail), " for \"%.*s\"", parser.previous.length, parser.previous.start);
  traceEnter("unary", detail);
  parsePrecedence(PREC_UNARY);

  switch (operatorType) {
    case TOKEN_BANG:  emitByte(OP_NOT); break;
    case TOKEN_MINUS: emitByte(OP_NEGATE); break;
    default: break;
  }
  traceExit();
}

ParseRule rules[] = {
  [TOKEN_LEFT_PAREN]    = {grouping, NULL,        PREC_NONE},
  [TOKEN_RIGHT_PAREN]   = {NULL,     NULL,        PREC_NONE},
  [TOKEN_LEFT_BRACE]    = {NULL,     NULL,        PREC_NONE},
  [TOKEN_RIGHT_BRACE]   = {NULL,     NULL,        PREC_NONE},
  [TOKEN_COMMA]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_DOT]           = {NULL,     NULL,        PREC_NONE},
  [TOKEN_MINUS]         = {unary,    binary,      PREC_TERM},
  [TOKEN_PLUS]          = {NULL,     binary,      PREC_TERM},
  [TOKEN_SEMICOLON]     = {NULL,     NULL,        PREC_NONE},
  [TOKEN_SLASH]         = {NULL,     binary,      PREC_FACTOR},
  [TOKEN_STAR]          = {NULL,     binary,      PREC_FACTOR},
  [TOKEN_QUESTION]      = {NULL,     conditional, PREC_CONDITIONAL},
  [TOKEN_COLON]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_BANG]          = {unary,    NULL,        PREC_NONE},
  [TOKEN_BANG_EQUAL]    = {NULL,     binary,      PREC_EQUALITY},
  [TOKEN_EQUAL]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_EQUAL_EQUAL]   = {NULL,     binary,      PREC_EQUALITY},
  [TOKEN_GREATER]       = {NULL,     binary,      PREC_COMPARISON},
  [TOKEN_GREATER_EQUAL] = {NULL,     binary,      PREC_COMPARISON},
  [TOKEN_LESS]          = {NULL,     binary,      PREC_COMPARISON},
  [TOKEN_LESS_EQUAL]    = {NULL,     binary,      PREC_COMPARISON},
  [TOKEN_IDENTIFIER]    = {variable, NULL,        PREC_NONE},
  [TOKEN_STRING]        = {string,   NULL,        PREC_NONE},
  [TOKEN_NUMBER]        = {number,   NULL,        PREC_NONE},
  [TOKEN_AND]           = {NULL,     NULL,        PREC_NONE},
  [TOKEN_CLASS]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_CONST]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_ELSE]          = {NULL,     NULL,        PREC_NONE},
  [TOKEN_FALSE]         = {literal,  NULL,        PREC_NONE},
  [TOKEN_FOR]           = {NULL,     NULL,        PREC_NONE},
  [TOKEN_FUN]           = {NULL,     NULL,        PREC_NONE},
  [TOKEN_IF]            = {NULL,     NULL,        PREC_NONE},
  [TOKEN_NIL]           = {literal,  NULL,        PREC_NONE},
  [TOKEN_OR]            = {NULL,     NULL,        PREC_NONE},
  [TOKEN_PRINT]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_RETURN]        = {NULL,     NULL,        PREC_NONE},
  [TOKEN_SUPER]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_THIS]          = {NULL,     NULL,        PREC_NONE},
  [TOKEN_TRUE]          = {literal,  NULL,        PREC_NONE},
  [TOKEN_VAR]           = {NULL,     NULL,        PREC_NONE},
  [TOKEN_WHILE]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_ERROR]         = {NULL,     NULL,        PREC_NONE},
  [TOKEN_EOF]           = {NULL,     NULL,        PREC_NONE},
};

static void parsePrecedence(Precedence precedence) {
  char detail[32];
  snprintf(detail, sizeof(detail), "(%s)", precedenceNames[precedence]);
  traceEnter("parsePrecedence", detail);

  advance();
  ParseFn prefixRule = getRule(parser.previous.type)->prefix;
  if (prefixRule == NULL) {
    error("Expect expression.");
    traceExit();
    return;
  }

  bool canAssign = precedence <= PREC_ASSIGNMENT;
  prefixRule(canAssign);

  while (precedence <= getRule(parser.current.type)->precedence) {
    advance();
    ParseFn infixRule = getRule(parser.previous.type)->infix;
    infixRule(canAssign);
  }

  if (canAssign && match(TOKEN_EQUAL)) {
    error("Invalid assignment target.");
  }
  traceExit();
}

static ParseRule* getRule(TokenType type) {
  return &rules[type];
}

static void expression(void) {
  traceEnter("expression", "");
  parsePrecedence(PREC_ASSIGNMENT);
  traceExit();
}

static void block(void) {
  while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF)) {
    declaration();
  }

  consume(TOKEN_RIGHT_BRACE, "Expect '}' after block.");
}

static void addLocal(Token name, bool isConst) {
  if (current->localCount == UINT16_COUNT) {
    error("Too many local variables in function.");
    return;
  }

  if (current->localCount == current->localCapacity) {
    int oldCapacity = current->localCapacity;
    current->localCapacity = GROW_CAPACITY(oldCapacity);
    current->locals = GROW_ARRAY(Local, current->locals, oldCapacity,
                                 current->localCapacity);
  }

  Local* local = &current->locals[current->localCount++];
  local->name = name;
  local->depth = -1;
  local->isConst = isConst;
}

static void declareVariable(bool isConst) {
  Token* name = &parser.previous;

  if (current->scopeDepth == 0) {
    // Globals are late bound, but the compiler still remembers which names are
    // constant. A later var with the same name makes it assignable again.
    ObjString* string = copyString(name->start, name->length);
    if (isConst) {
      tableSet(&vm.constGlobals, OBJ_VAL(string), BOOL_VAL(true));
    } else {
      tableDelete(&vm.constGlobals, OBJ_VAL(string));
    }
    return;
  }

  for (int i = current->localCount - 1; i >= 0; i--) {
    Local* local = &current->locals[i];
    if (local->depth != -1 && local->depth < current->scopeDepth) {
      break;
    }

    if (identifiersEqual(name, &local->name)) {
      error("Already a variable with this name in this scope.");
    }
  }

  addLocal(*name, isConst);
}

static uint8_t parseVariable(const char* errorMessage, bool isConst) {
  consume(TOKEN_IDENTIFIER, errorMessage);

  declareVariable(isConst);
  if (current->scopeDepth > 0) return 0;

  return identifierConstant(&parser.previous);
}

static void markInitialized(void) {
  current->locals[current->localCount - 1].depth = current->scopeDepth;
}

static void defineVariable(uint8_t global) {
  if (current->scopeDepth > 0) {
    markInitialized();
    return;
  }

  emitByte(OP_DEFINE_GLOBAL);
  emitByte(global);
}

static void varDeclaration(bool isConst) {
  uint8_t global = parseVariable(isConst ? "Expect constant name."
                                         : "Expect variable name.", isConst);

  if (match(TOKEN_EQUAL)) {
    expression();
  } else if (isConst) {
    // A constant with no value would be nil forever, which is surely a mistake.
    errorAtCurrent("Expect '=' after constant name.");
  } else {
    emitByte(OP_NIL);
  }
  consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");

  defineVariable(global);
}

static void printStatement(void) {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after value.");
  emitByte(OP_PRINT);
}

static void expressionStatement(void) {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after expression.");
  emitByte(OP_POP);
}

static void synchronize(void) {
  parser.panicMode = false;

  while (parser.current.type != TOKEN_EOF) {
    if (parser.previous.type == TOKEN_SEMICOLON) return;
    switch (parser.current.type) {
      case TOKEN_CLASS:
      case TOKEN_FUN:
      case TOKEN_VAR:
      case TOKEN_CONST:
      case TOKEN_FOR:
      case TOKEN_IF:
      case TOKEN_WHILE:
      case TOKEN_PRINT:
      case TOKEN_RETURN:
        return;

      default:
        ; // Do nothing.
    }

    advance();
  }
}

static void declaration(void) {
  if (match(TOKEN_VAR)) {
    varDeclaration(false);
  } else if (match(TOKEN_CONST)) {
    varDeclaration(true);
  } else {
    statement();
  }

  if (parser.panicMode) synchronize();
}

static void statement(void) {
  if (match(TOKEN_PRINT)) {
    printStatement();
  } else if (match(TOKEN_LEFT_BRACE)) {
    beginScope();
    block();
    endScope();
  } else {
    expressionStatement();
  }
}

bool compile(const char* source, Chunk* chunk) {
  initScanner(source);
  Compiler compiler;
  initCompiler(&compiler);
  compilingChunk = chunk;
  traceDepth = 0;

  parser.hadError = false;
  parser.panicMode = false;

  initTable(&stringConstants);

  advance();
  while (!match(TOKEN_EOF)) {
    declaration();
  }
  endCompiler();
  freeTable(&stringConstants);
  freeCompiler(&compiler);
  return !parser.hadError;
}
