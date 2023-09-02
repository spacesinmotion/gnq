#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uintptr_t ptr_size;

typedef struct Location {
  const char *file;
  uint16_t line;
  uint16_t column;
} Location;

typedef struct State {
  const char *c;
  Location location;
} State;

void State_skip(State *st) {
  if (*st->c == '\0')
    return;
  if (*st->c == '\n') {
    st->location.line++;
    st->location.column = 1;
  } else
    ++st->location.column;
  ++st->c;
}

void skip_whitespace(State *st) {
  State old = *st;
  while (*st->c && *st->c != '\n' && isspace(*st->c))
    State_skip(st);
}

bool check_op(State *st, const char *op) {
  skip_whitespace(st);
  State old = *st;
  while (st->c[0] && op[0] && op[0] == st->c[0]) {
    State_skip(st);
    ++op;
  }
  if (op[0] == 0)
    return true;
  *st = old;
  return false;
}

typedef struct Program {
} Program;

typedef struct Module {
} Module;

typedef struct Expression Expression;
typedef struct Expression {
  Expression *o1;
  Expression *o2;
} Expression;

enum { ASSOC_NONE = 0, ASSOC_LEFT, ASSOC_RIGHT };
typedef struct BinOp {
  const char *op;
  int prec;
  int assoc;
  bool returns_bool;
} BinOp;
BinOp ops[] = {
    {">>=", 100 - 14, ASSOC_RIGHT, false}, //
    {"<<=", 100 - 14, ASSOC_RIGHT, false}, //
                                           //
    {"==", 100 - 7, ASSOC_LEFT, true},     //
    {"!=", 100 - 7, ASSOC_LEFT, true},     //
    {"<=", 100 - 6, ASSOC_LEFT, true},     //
    {">=", 100 - 6, ASSOC_LEFT, true},     //
    {"+=", 100 - 14, ASSOC_RIGHT, false},  //
    {"-=", 100 - 14, ASSOC_RIGHT, false},  //
    {"*=", 100 - 14, ASSOC_RIGHT, false},  //
    {"/=", 100 - 14, ASSOC_RIGHT, false},  //
    {"%=", 100 - 14, ASSOC_RIGHT, false},  //
    {"&=", 100 - 14, ASSOC_RIGHT, false},  //
    {"^=", 100 - 14, ASSOC_RIGHT, false},  //
    {"|=", 100 - 14, ASSOC_RIGHT, false},  //
    {"&&", 100 - 11, ASSOC_LEFT, true},    //
    {"||", 100 - 12, ASSOC_LEFT, true},    //
    {"<<", 100 - 5, ASSOC_LEFT, false},    //
    {">>", 100 - 5, ASSOC_LEFT, false},    //
                                           //
    {"*", 100 - 3, ASSOC_LEFT, false},     //
    {"/", 100 - 3, ASSOC_LEFT, false},     //
    {"%", 100 - 3, ASSOC_LEFT, false},     //
    {"+", 100 - 4, ASSOC_LEFT, false},     //
    {"-", 100 - 4, ASSOC_LEFT, false},     //
    {"<", 100 - 6, ASSOC_LEFT, true},      //
    {">", 100 - 6, ASSOC_LEFT, true},      //
    {"&", 100 - 8, ASSOC_LEFT, false},     //
    {"^", 100 - 9, ASSOC_LEFT, false},     //
    {"|", 100 - 10, ASSOC_LEFT, false},    //
                                           //
    {"=", 100 - 14, ASSOC_RIGHT, false},   //
};
BinOp *getop(const char *ch) {
  for (size_t i = 0; i < sizeof(ops) / sizeof(ops[0]); ++i)
    if (strcmp(ops[i].op, ch) == 0)
      return ops + i;
  return NULL;
}

typedef struct ShuntYard {
  Expression *op_stack[128];
  int op_stack_size;
  Expression *val_stack[128];
  int val_stack_size;
} ShuntYard;

ShuntYard ShuntYard_create() {
  return (ShuntYard){.op_stack_size = 0, .val_stack_size = 0};
}

void ShuntYard_push_val(ShuntYard *y, Expression *e) {
  y->val_stack[y->val_stack_size] = e;
  y->val_stack_size++;
}

void ShuntYard_push_op(ShuntYard *y, Expression *e) {
  y->op_stack[y->op_stack_size] = e;
  y->op_stack_size++;
}

void ShuntYard_shunt(ShuntYard *y) {
  Expression *pop = y->op_stack[y->op_stack_size - 1];
  y->op_stack_size--;

  assert(y->val_stack_size >= 2);
  // if (y->val_stack_size < 2)
  //   FATALX("not enough parameter for binary operation '%s'",
  //          pop->binop->op->op);

  pop->o2 = y->val_stack[y->val_stack_size - 1];
  y->val_stack_size--;
  pop->o1 = y->val_stack[y->val_stack_size - 1];
  y->val_stack[y->val_stack_size - 1] = pop;
}

// Expression *Program_parse_bin_operator(Program *p, State *st) {
//   // if (check_whitespace_for_nl(st))
//   //   return NULL;

//   for (size_t i = 0; i < sizeof(ops) / sizeof(BinOp); ++i) {
//     if (check_op(st, ops[i].op)) {
//       Expression *bin = Program_new_Expression(p, BinaryOperationE,
//                                                back(st, strlen(ops[i].op)));
//       bin->binop->op = &ops[i];
//       return bin;
//     }
//   }
//   return NULL;
// }

// Expression *Program_parse_unary_operand(Program *p, Module *m, State *st) {
//   Expression *prefix = NULL;
//   const char *un_pre_ops[] = {"++", "--", "*", "~", "!", "-", "+", "&"};
//   for (size_t i = 0; i < sizeof(un_pre_ops) / sizeof(const char *); ++i) {
//     if (check_op(st, un_pre_ops[i])) {
//       prefix = Program_new_Expression(p, UnaryPrefixE, back(st, i < 2 ? 2 :
//       1)); prefix->unpre->op = un_pre_ops[i]; break;
//     }
//   }

//   Expression *e = NULL;
//   if (check_op(st, "(")) {
//     e = Program_new_Expression(p, BraceE, back(st, 1));
//     e->brace->o = Program_parse_expression(p, m, st);
//     if (!e->brace->o)
//       FATAL(&st->location, "missing '(' content");
//     if (!check_op(st, ")"))
//       FATAL(&st->location, "missing closing ')'");
//   } else if ((e = Program_parse_construction(p, m, st))) {
//     ;
//   } else if ((e = Program_parse_array_construction(p, m, st))) {
//     ;
//   } else if ((e = Program_parse_auto_declaration_(p, m, st))) {
//     ;
//   } else
//     e = Program_parse_atom(p, st);

//   if (!e && prefix)
//     FATAL(&st->location, "prefix operation without expression '%s'",
//           prefix->unpre->op);
//   if (!e)
//     return NULL;

//   e = Program_parse_suffix_expression(p, m, st, e);
//   if (prefix) {
//     prefix->unpre->o = e;
//     return prefix;
//   }
//   return e;
// }

// Expression *Program_parse_expression(Program *p, Module *m, State *st) {
//   //   Expression *ev = Program_parse_unary_operand(p, m, st);
//   //   if (!ev)
//   //     return NULL;
//   ShuntYard yard = ShuntYard_create();
//   //   ShuntYard_push_val(&yard, ev);

//   Expression *eop;
//   for (;;) {
//     // if (check_whitespace_for_nl(st))
//     //   break;
//     State old = *st;
//     eop = Program_parse_bin_operator(p, st);
//     if (!eop)
//       break;
//     ev = Program_parse_unary_operand(p, m, st);
//     if (!ev) {
//       *st = old;
//       break;
//     }
//     if (eop->binop->op->assoc == ASSOC_RIGHT) {
//       while (yard.op_stack_size > 0 &&
//              eop->binop->op->prec <
//                  yard.op_stack[yard.op_stack_size - 1]->binop->op->prec)
//         ShuntYard_shunt(&yard);
//     } else {
//       while (yard.op_stack_size > 0 &&
//              eop->binop->op->prec <=
//                  yard.op_stack[yard.op_stack_size - 1]->binop->op->prec)
//         ShuntYard_shunt(&yard);
//     }
//     ShuntYard_push_op(&yard, eop);
//     ShuntYard_push_val(&yard, ev);
//   }

//   //   while (yard.op_stack_size > 0) {
//   //     ShuntYard_shunt(&yard);
//   //   }
//   //   if (yard.val_stack_size != 1)
//   //     FATALX("Expression parsing failed with too many values (%d)",
//   //            yard.val_stack_size);

//   //   State old = *st;
//   //   if (check_op(st, "?")) {
//   //     Expression *e = Program_new_Expression(p, TernaryOperationE,
//   //     old.location); e->ternop->condition = yard.val_stack[0]; if
//   //     (!(e->ternop->if_e = Program_parse_expression(p, m, st)))
//   //       FATAL(&old.location, "expect 1st expression for ternary
//   operation");
//   //     if (!check_op(st, ":"))
//   //       FATAL(&old.location, "expect ':' for ternary operation");
//   //     if (!(e->ternop->else_e = Program_parse_expression(p, m, st)))
//   //       FATAL(&old.location, "expect 2nd expression for ternary
//   operation");
//   //     if (e->ternop->condition->type == BinaryOperationE &&
//   //         e->ternop->condition->binop->op->prec < 100 - 13) {
//   //       Expression *cond = e->ternop->condition->binop->o2;
//   //       e->ternop->condition->binop->o2 = e;
//   //       TernaryOperation *ternop = e->ternop;
//   //       e = e->ternop->condition;
//   //       ternop->condition = cond;
//   //     }
//   //     return e;
//   //   }

//   //   return yard.val_stack[0];
// }

typedef struct Node Node;

typedef enum ValueType {
  Pair = 0,
  NumberInt = 1,
  NumberFloat = 3,
  ShortString = 5,
  LongString = 7,
} ValueType;

typedef union Value {
  Node *o;
  ValueType t;
  int64_t ni;
  double nf;
  char ss[8];
  char *ls;
} Value;

struct Node {
  Value car, cdr;
};

ValueType Node_type(Node *n) { return (n->car.t & 0x1) ? n->car.t : Pair; }

typedef struct Arena {
  Node *memory;
  size_t len;
  size_t cap;
} Arena;

Arena Arena_create(size_t nb_nodes) {
  return (Arena){(Node *)malloc(nb_nodes * sizeof(Node)), 0, nb_nodes};
}

Arena Arena_free(Arena *a) {
  free(a->memory);
  a->memory = NULL;
  a->cap = a->len = 0;
}

Node *Arena_node(Arena *a, ValueType vt) {
  assert(a->len < a->cap);
  a->memory[a->len].car.t = vt;
  return &a->memory[a->len++];
}

char *Arena_str(Arena *a, size_t len) {
  len = (len / sizeof(Node)) + 1;
  assert(a->len + len < a->cap);
  char *t = (char *)&a->memory[a->len];
  a->len += len;
  return t;
}

Node *gnq_int(Arena *a, int64_t i) {
  Node *n = Arena_node(a, NumberInt);
  n->cdr.ni = i;
  return n;
}
int64_t gnq_toint(Node *n) {
  assert(n && Node_type(n) == NumberInt);
  return n->cdr.ni;
}

Node *gnq_float(Arena *a, double f) {
  Node *n = Arena_node(a, NumberFloat);
  n->cdr.nf = f;
  return n;
}
double gnq_tofloat(Node *n) {
  assert(n && Node_type(n) == NumberFloat);
  return n->cdr.nf;
}

Node *gnq_string(Arena *a, const char *t) {
  size_t len = strlen(t);
  if (len < 8) {
    Node *n = Arena_node(a, ShortString);
    strncpy(n->cdr.ss, t, 7);
    return n;
  }

  Node *n = Arena_node(a, LongString);
  n->cdr.ls = Arena_str(a, len);
  strcpy(n->cdr.ls, t);
  return n;
}
const char *gnq_tostring(Node *n) {
  assert(n && (Node_type(n) == ShortString || Node_type(n) == LongString));

  return (Node_type(n) == ShortString) ? n->cdr.ss : n->cdr.ls;
}

// fe_Object* fe_cons(fe_Context *ctx, fe_Object *car, fe_Object *cdr);
// fe_Object* fe_bool(fe_Context *ctx, int b);
// fe_Object* fe_string(fe_Context *ctx, const char *str);
// fe_Object* fe_symbol(fe_Context *ctx, const char *name);
// fe_Object* fe_cfunc(fe_Context *ctx, fe_CFunc fn);
// fe_Object* fe_ptr(fe_Context *ctx, void *ptr);
// fe_Object* fe_list(fe_Context *ctx, fe_Object **objs, int n);
// fe_Object* fe_car(fe_Context *ctx, fe_Object *obj);
// fe_Object* fe_cdr(fe_Context *ctx, fe_Object *obj);

Node *Lisp_parse(const char *code) { return NULL; }

void arena_test() {
  printf("arena_test\n");

  Arena a = Arena_create(256);
  assert(a.cap == 256);
  assert(a.len == 0);

  Node *n = gnq_int(&a, 42);
  assert(a.cap == 256);
  assert(a.len == 1);
  assert(NumberInt == Node_type(n));
  assert(42 == gnq_toint(n));

  n = gnq_float(&a, 4.2);
  assert(a.cap == 256);
  assert(a.len == 2);
  assert(NumberFloat == Node_type(n));
  assert(4.2 == gnq_tofloat(n));

  n = gnq_string(&a, "id");
  assert(a.cap == 256);
  assert(a.len == 3);
  assert(ShortString == Node_type(n));
  assert(strcmp("id", gnq_tostring(n)) == 0);

  n = gnq_string(&a, "a way longer string ");
  assert(a.cap == 256);
  assert(a.len == 6);
  assert(LongString == Node_type(n));
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);

  Node *n2 = gnq_int(&a, -84);
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);
  assert(a.cap == 256);
  assert(a.len == 7);
  assert(NumberInt == Node_type(n2));
  assert(-84 == gnq_toint(n2));

  Arena_free(&a);
}

int main() {
  assert(sizeof(ptr_size) == sizeof(void *));

  arena_test();

  printf("ok\n");
  return 0;
}