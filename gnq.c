#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uintptr_t ptr_size;

typedef struct Location {
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
void State_skipi(State *st, int i) {
  while (i > 0) {
    State_skip(st);
    i--;
  }
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
//     if (eop->assoc == ASSOC_RIGHT) {
//       while (yard.op_stack_size > 0 &&
//              eop->prec <
//                  yard.op_stack[yard.op_stack_size - 1]->binop->op->prec)
//         ShuntYard_shunt(&yard);
//     } else {
//       while (yard.op_stack_size > 0 &&
//              eop->prec <=
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
  StringShort = 5,
  StringLong = 7,
  SymbolShort = 9,
  SymbolLong = 11,
} ValueType;

typedef union Value {
  Node *n;
  ValueType t;
  int64_t ni;
  double nf;
  char ss[8];
  char *ls;
} Value;

struct Node {
  Value car, cdr;
};

ValueType gnq_type(Node *n) {
  assert(n);
  return (n->car.t & 0x1) ? n->car.t : Pair;
}

typedef struct Arena {
  Node *memory;
  size_t len;
  size_t cap;
} Arena;

Arena Arena_create(size_t nb_nodes) { return (Arena){(Node *)malloc(nb_nodes * sizeof(Node)), 0, nb_nodes}; }

void Arena_free(Arena *a) {
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
  assert(n && gnq_type(n) == NumberInt);
  return n->cdr.ni;
}

Node *gnq_float(Arena *a, double f) {
  Node *n = Arena_node(a, NumberFloat);
  n->cdr.nf = f;
  return n;
}
double gnq_tofloat(Node *n) {
  assert(n && gnq_type(n) == NumberFloat);
  return n->cdr.nf;
}

Node *gnq_string(Arena *a, const char *t) {
  size_t len = strlen(t);
  if (len < 8) {
    Node *n = Arena_node(a, StringShort);
    strncpy(n->cdr.ss, t, 7);
    return n;
  }

  Node *n = Arena_node(a, StringLong);
  n->cdr.ls = Arena_str(a, len);
  strcpy(n->cdr.ls, t);
  return n;
}
const char *gnq_tostring(Node *n) {
  assert(n && (gnq_type(n) == StringShort || gnq_type(n) == StringLong));

  return (gnq_type(n) == StringShort) ? n->cdr.ss : n->cdr.ls;
}

Node *gnq_sym(Arena *a, const char *s) {
  Node *n = gnq_string(a, s);
  n->car.t = n->car.t == StringShort ? SymbolShort : SymbolLong;
  return n;
}
const char *gnq_tosym(Node *n) {
  assert(n && (gnq_type(n) == SymbolShort || gnq_type(n) == SymbolLong));

  return (gnq_type(n) == SymbolShort) ? n->cdr.ss : n->cdr.ls;
}

Node *gnq_cons(Arena *a, Node *n1, Node *n2) {
  Node *n = Arena_node(a, Pair);
  n->car.n = n1;
  n->cdr.n = n2;
  return n;
}
Node *gnq_car(Node *n) {
  assert(gnq_type(n) == Pair);
  return n->car.n;
}
Node *gnq_cdr(Node *n) {
  assert(gnq_type(n) == Pair);
  return n->cdr.n;
}

Node nil = (Node){NULL, NULL};
bool gnq_isnil(Node *n) { return n == &nil; }

Node *gnq_list(Arena *a, int count, ...) {
  Node *nodes[16];

  va_list argp;
  va_start(argp, count);
  for (int i = 0; i < count; ++i)
    nodes[i] = va_arg(argp, Node *);
  va_end(argp);

  Node *n = &nil;
  for (int i = count - 1; i >= 0; --i)
    n = gnq_cons(a, nodes[i], n);
  return n;
}
Node *gnq_next(Node **list) {
  Node *n = gnq_car(*list);
  *list = gnq_cdr(*list);
  return n;
}

void arena_test() {
  printf("arena_test\n");

  Arena a = Arena_create(256);
  assert(a.cap == 256);
  assert(a.len == 0);

  Node *n = gnq_int(&a, 42);
  assert(a.cap == 256);
  assert(a.len == 1);
  assert(NumberInt == gnq_type(n));
  assert(42 == gnq_toint(n));

  n = gnq_float(&a, 4.2);
  assert(a.cap == 256);
  assert(a.len == 2);
  assert(NumberFloat == gnq_type(n));
  assert(4.2 == gnq_tofloat(n));

  n = gnq_string(&a, "id");
  assert(a.cap == 256);
  assert(a.len == 3);
  assert(StringShort == gnq_type(n));
  assert(strcmp("id", gnq_tostring(n)) == 0);

  n = gnq_string(&a, "a way longer string ");
  assert(a.cap == 256);
  assert(a.len == 6);
  assert(StringLong == gnq_type(n));
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);

  Node *n2 = gnq_int(&a, -84);
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);
  assert(a.cap == 256);
  assert(a.len == 7);
  assert(NumberInt == gnq_type(n2));
  assert(-84 == gnq_toint(n2));

  Node *nc = gnq_cons(&a, n, n2);
  assert(a.len == 8);
  assert(gnq_car(nc) == n);
  assert(gnq_cdr(nc) == n2);

  n = gnq_sym(&a, "id");
  assert(a.cap == 256);
  assert(a.len == 9);
  assert(SymbolShort == gnq_type(n));
  assert(strcmp("id", gnq_tosym(n)) == 0);

  n = gnq_sym(&a, "a_way_longer_symbol");
  assert(a.cap == 256);
  assert(a.len == 12);
  assert(SymbolLong == gnq_type(n));
  assert(strcmp("a_way_longer_symbol", gnq_tosym(n)) == 0);

  Arena_free(&a);
}

void list_test() {
  printf("list_test\n");

  Arena a = Arena_create(256);

  Node *n1 = gnq_int(&a, 42);
  Node *n2 = gnq_float(&a, 4.2);
  Node *n3 = gnq_string(&a, "id");

  Node *list = gnq_list(&a, 3, n1, n2, n3);
  assert(n1 == gnq_next(&list) && list != NULL);
  assert(n2 == gnq_next(&list) && list != NULL);
  assert(n3 == gnq_next(&list));
  assert(list == &nil);
  assert(gnq_isnil(list));

  Arena_free(&a);
}

void gnq_skip_white(State *st) {
  while (*st->c && *st->c != '\n' && isspace(*st->c))
    State_skip(st);
}

Node *gnq_parse_string(Arena *a, State *st) {
  if (*st->c == '"') {
    const char *start = st->c;
    do {
      State_skip(st);
      assert(*st->c);
    } while (*st->c != '"');
    *(char *)(st->c) = '\0';
    Node *ns = gnq_string(a, start + 1);
    *(char *)(st->c) = '"';
    State_skip(st);
    return ns;
  }
  return NULL;
}

Node *gnq_parse_number(Arena *a, State *st) {
  char *ef = (char *)st->c;
  double f = strtod(st->c, &ef);
  char *ei = (char *)st->c;
  int64_t i = strtol(st->c, &ei, 10);
  if (ei > st->c) {
    State_skipi(st, ((ef > ei) ? ef : ei) - st->c);
    return ((ef > ei) ? gnq_float(a, f) : gnq_int(a, i));
  }
  return NULL;
}

Node *gnq_parse_id(Arena *a, State *st) {
  const char *start = st->c;
  if (isalpha(*st->c) || *st->c == '_') {
    State_skip(st);
    while (isalnum(*st->c) || *st->c == '_')
      State_skip(st);
    char old = *st->c;
    *(char *)st->c = '\0';
    Node *id = gnq_list(a, 2, gnq_sym(a, "id"), gnq_sym(a, start));
    *(char *)st->c = old;
    return id;
  }
  return NULL;
}

Node *lisp_parse_(Arena *a, State *st) {

  gnq_skip_white(st);

  if (*st->c == '(') {
    State_skip(st);
    Node *list = &nil;
    Node *last = &nil;
    while (*st->c && *st->c != ')') {
      State sub_st = *st;
      Node *sub = lisp_parse_(a, &sub_st);
      if (*sub_st.c) {
        if (last != &nil) {
          last->cdr.n = gnq_cons(a, sub, &nil);
          last = gnq_cdr(last);
        } else {
          last = gnq_cons(a, sub, &nil);
          list = last;
        }
      }
      *st = sub_st;
      gnq_skip_white(st);
    }

    assert(*st->c && *st->c == ')');
    State_skip(st);
    return list;
  }

  Node *string = gnq_parse_string(a, st);
  if (string)
    return string;
  Node *number = gnq_parse_number(a, st);
  if (number)
    return number;

  char *es = (char *)st->c;
  while (*es && !isspace(*es) && *es != '(' && *es != ')')
    ++es;
  if (es > st->c) {
    char x = *es;
    *es = '\0';
    Node *s = gnq_sym(a, st->c);
    *es = x;
    State_skipi(st, es - st->c);
    return s;
  }

  return &nil;
}

Node *lisp_parse(Arena *a, const char *c) {
  State st = (State){c, {1, 1}};
  return lisp_parse_(a, &st);
}

void parser_atom_test() {
  printf("parser_atom_test\n");

  Arena a = Arena_create(256);

  Node *ni = lisp_parse(&a, "  42");
  assert(ni && gnq_type(ni) == NumberInt && gnq_toint(ni) == 42);

  Node *nf = lisp_parse(&a, " -4.2  ");
  assert(nf && gnq_type(nf) == NumberFloat && gnq_tofloat(nf) == -4.2);

  Node *nstr = lisp_parse(&a, "  \"str\"");
  assert(nstr && gnq_type(nstr) == StringShort && strcmp(gnq_tostring(nstr), "str") == 0);

  Node *nsym = lisp_parse(&a, "  sym");
  assert(nsym && gnq_type(nsym) == SymbolShort && strcmp(gnq_tosym(nsym), "sym") == 0);

  const char *a_row = "  sym 4 sym";
  State st = (State){a_row};
  nsym = lisp_parse_(&a, &st);
  assert(nsym && gnq_type(nsym) == SymbolShort && strcmp(gnq_tosym(nsym), "sym") == 0);
  assert(st.c > a_row);
  a_row = st.c;
  nsym = lisp_parse_(&a, &st);
  assert(nsym && gnq_type(nsym) == NumberInt);
  assert(nsym && gnq_type(nsym) == NumberInt && gnq_toint(nsym) == 4);
  assert(st.c > a_row);
  a_row = st.c;
  nsym = lisp_parse_(&a, &st);
  assert(nsym && gnq_type(nsym) == SymbolShort && strcmp(gnq_tosym(nsym), "sym") == 0);

  Arena_free(&a);
}

void parser_list_test() {
  printf("parser_list_test\n");

  Arena a = Arena_create(256);

  Node *n = lisp_parse(&a, "");
  assert(n && gnq_isnil(n));
  n = lisp_parse(&a, "()");
  assert(n && gnq_isnil(n));

  n = lisp_parse(&a, "(a)");
  assert(n && gnq_type(n) == Pair);
  Node *nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == SymbolShort && gnq_isnil(n));

  n = lisp_parse(&a, "(1 2 3)");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 2 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 3 && gnq_isnil(n));

  n = lisp_parse(&a, "(1 (2 3))");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == Pair && gnq_isnil(n));
  n = nn;
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 2 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 3 && gnq_isnil(n));

  n = lisp_parse(&a, "(1 () 3.2  gg)");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(gnq_isnil(nn) && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberFloat && gnq_tofloat(nn) == 3.2 && !gnq_isnil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == SymbolShort && strcmp(gnq_tosym(nn), "gg") == 0 && gnq_isnil(n));

  Arena_free(&a);
}

bool gnq_equal(Node *a, Node *b) {
  if (gnq_type(a) != gnq_type(b))
    return false;

  if (gnq_type(a) == NumberInt)
    return gnq_toint(a) == gnq_toint(b);
  if (gnq_type(a) == NumberFloat)
    return gnq_tofloat(a) == gnq_tofloat(b);
  if (gnq_type(a) == StringShort || gnq_type(a) == StringLong)
    return strcmp(gnq_tostring(a), gnq_tostring(b)) == 0;
  if (gnq_type(a) == SymbolShort || gnq_type(a) == SymbolLong)
    return strcmp(gnq_tosym(a), gnq_tosym(b)) == 0;

  if (gnq_type(a) == Pair) {
    while (!gnq_isnil(a) && !gnq_isnil(b))
      if (!gnq_equal(gnq_next(&a), gnq_next(&b)))
        return false;
    return gnq_isnil(a) && gnq_isnil(b);
  }

  return false;
}

void parser_lisp_compare() {
  printf("parser_lisp_compare\n");

  Arena a = Arena_create(256);

  assert(gnq_equal(lisp_parse(&a, "42"), lisp_parse(&a, "42")));
  assert(!gnq_equal(lisp_parse(&a, "2"), lisp_parse(&a, "4")));
  assert(gnq_equal(lisp_parse(&a, "4.2"), lisp_parse(&a, "4.2")));
  assert(!gnq_equal(lisp_parse(&a, "2.0"), lisp_parse(&a, "4.4")));
  assert(gnq_equal(lisp_parse(&a, "sym"), lisp_parse(&a, "sym")));
  assert(!gnq_equal(lisp_parse(&a, "sym1"), lisp_parse(&a, "sym4")));
  assert(gnq_equal(lisp_parse(&a, "\"str\""), lisp_parse(&a, "\"str\"")));
  assert(!gnq_equal(lisp_parse(&a, "\"str\""), lisp_parse(&a, "\"no_str\"")));

  assert(!gnq_equal(lisp_parse(&a, "42"), lisp_parse(&a, "4.2")));
  assert(!gnq_equal(lisp_parse(&a, "sym"), lisp_parse(&a, "4.2")));
  assert(!gnq_equal(lisp_parse(&a, "sym"), lisp_parse(&a, "42")));

  assert(gnq_equal(lisp_parse(&a, "(sym 1 2.2)"), lisp_parse(&a, "(sym 1 2.2)")));
  assert(!gnq_equal(lisp_parse(&a, "(sym 1 2.2)"), lisp_parse(&a, "(sym 1 2.3)")));
  assert(!gnq_equal(lisp_parse(&a, "(sym 1 2.2)"), lisp_parse(&a, "(sym 1)")));
  assert(!gnq_equal(lisp_parse(&a, "(sym 1)"), lisp_parse(&a, "(sym 1 2.2)")));
  assert(gnq_equal(lisp_parse(&a, "()"), lisp_parse(&a, "")));

  assert(gnq_equal(lisp_parse(&a, "(fn 1)"), lisp_parse(&a, "(fn 1 )")));
  assert(gnq_equal(lisp_parse(&a, "(fn (a b c) 1 2)"), lisp_parse(&a, "(fn (a b c) 1 2)")));

  assert(!gnq_equal(lisp_parse(&a, "(fn 1)"), lisp_parse(&a, "(fn 1 1)")));
  assert(!gnq_equal(lisp_parse(&a, "(fn 1 1 1)"), lisp_parse(&a, "(fn 1 1)")));

  Arena_free(&a);
}

size_t lisp_str(char *b, size_t s, Node *a) {
  if (gnq_type(a) == NumberInt)
#ifdef WIN32
    return snprintf(b, s, "%lld", gnq_toint(a));
#else
    return snprintf(b, s, "%ld", gnq_toint(a));
#endif
  if (gnq_type(a) == NumberFloat)
    return snprintf(b, s, "%g", gnq_tofloat(a));
  if (gnq_type(a) == StringShort || gnq_type(a) == StringLong)
    return snprintf(b, s, "\"%s\"", gnq_tostring(a));
  if (gnq_type(a) == SymbolShort || gnq_type(a) == SymbolLong)
    return snprintf(b, s, "%s", gnq_tosym(a));

  if (gnq_type(a) == Pair) {
    size_t i = snprintf(b, s, "(");
    while (!gnq_isnil(a)) {
      if (i > 1)
        i += snprintf(b + i, s - i, " ");
      i += lisp_str(b + i, s - i, gnq_next(&a));
    }
    i += snprintf(b + i, s - i, ")");
    return i;
  }

  return 0;
}

void parser_lisp_out() {
  printf("parser_lisp_out\n");

  Arena a = Arena_create(256);
  char b[256];

  assert(lisp_str(b, 256, lisp_parse(&a, "42")) == 2);
  assert(strcmp("42", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, "4.2")) == 3);
  assert(strcmp("4.2", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, " \"str\" ")) == 5);
  assert(strcmp("\"str\"", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, " symysy")) == 6);
  assert(strcmp("symysy", b) == 0);

  assert(lisp_str(b, 256, lisp_parse(&a, "(s)")) == 3);
  assert(strcmp("(s)", b) == 0);

  assert(lisp_str(b, 256, lisp_parse(&a, "(fn 3)")) == 6);
  assert(strcmp("(fn 3)", b) == 0);

  assert(lisp_str(b, 256, lisp_parse(&a, " (  fn  ( a   b  ) 3 xxx )")) == 16);
  assert(strcmp("(fn (a b) 3 xxx)", b) == 0);

  assert(lisp_str(b, 256, lisp_parse(&a, "(+ 1 (* 2 3))")) == 13);
  assert(strcmp("(+ 1 (* 2 3))", b) == 0);

  Arena_free(&a);
}

Node *gnq_parse(Arena *a, State *st);

Node *gnq_parse_unary_operand(Arena *a, State *st) {
  gnq_skip_white(st);

  Node *atom = NULL;
  if ((atom = gnq_parse_string(a, st)))
    return atom;
  if ((atom = gnq_parse_number(a, st)))
    return atom;
  if ((atom = gnq_parse_id(a, st)))
    return atom;

  const char *un_pre_ops[] = {"++", "--", "*", "~", "!", "-", "+", "&"};
  for (size_t i = 0; i < sizeof(un_pre_ops) / sizeof(const char *); ++i) {
    if (check_op(st, un_pre_ops[i])) {
      Node *op = gnq_parse_unary_operand(a, st);
      assert(op);
      return gnq_list(a, 2, gnq_sym(a, un_pre_ops[i]), op);
    }
  }

  if (check_op(st, "(")) {
    Node *brace = gnq_parse(a, st);
    assert(brace);
    bool expect_closing_brace = check_op(st, ")");
    assert(expect_closing_brace);
    return gnq_list(a, 2, gnq_sym(a, "BR"), brace);
  }

  return &nil;
}

BinOp *gnq_parse_bin_operator(State *st) {
  for (size_t i = 0; i < sizeof(ops) / sizeof(BinOp); ++i) {
    if (check_op(st, ops[i].op))
      return &ops[i];
  }
  return NULL;
}

typedef struct ShuntYard {
  BinOp *op_stack[128];
  int op_stack_size;
  Node *val_stack[128];
  int val_stack_size;
} ShuntYard;

ShuntYard ShuntYard_create() { return (ShuntYard){.op_stack_size = 0, .val_stack_size = 0}; }

void ShuntYard_push_val(ShuntYard *y, Node *e) {
  y->val_stack[y->val_stack_size] = e;
  y->val_stack_size++;
}

void ShuntYard_push_op(ShuntYard *y, BinOp *op) {
  y->op_stack[y->op_stack_size] = op;
  y->op_stack_size++;
}

void ShuntYard_shunt(ShuntYard *y, Arena *a) {
  BinOp *pop = y->op_stack[y->op_stack_size - 1];
  y->op_stack_size--;

  assert(y->val_stack_size >= 2);

  Node *o2 = y->val_stack[y->val_stack_size - 1];
  y->val_stack_size--;
  Node *o1 = y->val_stack[y->val_stack_size - 1];
  y->val_stack[y->val_stack_size - 1] = gnq_list(a, 3, gnq_sym(a, pop->op), o1, o2);
}

Node *gnq_parse(Arena *a, State *st) {
  const char *cc = st->c;
  Node *ev = gnq_parse_unary_operand(a, st);
  if (!ev)
    return NULL;
  ShuntYard yard = ShuntYard_create();
  ShuntYard_push_val(&yard, ev);

  BinOp *op = NULL;
  for (;;) {
    gnq_skip_white(st);
    State old = *st;
    op = gnq_parse_bin_operator(st);
    if (!op)
      break;
    // printf(" op '%s'\n", op->op);
    ev = gnq_parse_unary_operand(a, st);
    if (!ev) {
      *st = old;
      break;
    }
    if (op->assoc == ASSOC_RIGHT) {
      while (yard.op_stack_size > 0 && op->prec < yard.op_stack[yard.op_stack_size - 1]->prec)
        ShuntYard_shunt(&yard, a);
    } else {
      while (yard.op_stack_size > 0 && op->prec <= yard.op_stack[yard.op_stack_size - 1]->prec)
        ShuntYard_shunt(&yard, a);
    }
    ShuntYard_push_op(&yard, op);
    ShuntYard_push_val(&yard, ev);
  }

  while (yard.op_stack_size > 0)
    ShuntYard_shunt(&yard, a);

  assert(yard.val_stack_size == 1);
  // if (yard.val_stack_size != 1)
  //   FATALX("Expression parsing failed with too many values (%d)", yard.val_stack_size);

  // State old = *st;
  // if (check_op(st, "?")) {
  //   Expression *e = Program_new_Expression(p, TernaryOperationE, old.location);
  //   e->ternop->condition = yard.val_stack[0];
  //   if (!(e->ternop->if_e = Program_parse_expression(p, m, st)))
  //     FATAL(&old.location, "expect 1st expression for ternary operation ");
  //   if (!check_op(st, ":"))
  //     FATAL(&old.location, "expect ':' for ternary operation");
  //   if (!(e->ternop->else_e = Program_parse_expression(p, m, st)))
  //           FATAL(&old.location, "expect 2nd expression for ternary
  //     operation ");
  //     if (e->ternop->condition->type == BinaryOperationE &&
  //         e->ternop->condition->binop->op->prec < 100 - 13) {
  //       Expression *cond = e->ternop->condition->binop->o2;
  //       e->ternop->condition->binop->o2 = e;
  //       TernaryOperation *ternop = e->ternop;
  //       e = e->ternop->condition;
  //       ternop->condition = cond;
  //     }
  //     return e;
  // }

  return yard.val_stack[0];
}

bool parse_as_(Arena *a, const char *gnq, const char *lisp) {
  State s = (State){gnq, {0, 0}};
  Node *from_lisp = lisp_parse(a, lisp);
  Node *from_gnq = gnq_parse(a, &s);
  if (gnq_equal(from_gnq, from_lisp))
    return true;

  char b1[256] = {0};
  lisp_str(b1, sizeof(b1), from_lisp);
  char b2[256] = {0};
  lisp_str(b2, sizeof(b2), from_gnq);
  printf("expect '%s' got '%s'\n", b1, b2);
  return false;
}

void parser_gnq_test() {
  printf("parser_gnq_test\n");

  Arena a = Arena_create(512);

  assert(parse_as_(&a, "42", "42"));
  assert(parse_as_(&a, "-42", "-42"));
  assert(parse_as_(&a, "-4.21b", "-4.21"));
  assert(parse_as_(&a, "\"str\"", "\"str\""));
  assert(parse_as_(&a, "  \"str\"", "\"str\""));

  assert(parse_as_(&a, "var", "(id var)"));
  assert(parse_as_(&a, "_var2", "(id _var2)"));

  assert(parse_as_(&a, "a + 1", "(+ (id a) 1)"));
  assert(parse_as_(&a, "1 + 2 * 3", "(+ 1 (* 2 3))"));
  assert(parse_as_(&a, "1 * 2 + 3", "(+ (* 1 2) 3)"));
  assert(parse_as_(&a, "1 - 2 % 3", "(- 1 (% 2 3))"));
  assert(parse_as_(&a, "1 | 2 & 3", "(| 1 (& 2 3))"));
  assert(parse_as_(&a, "1 || 2 && 3", "(|| 1 (&& 2 3))"));

  assert(parse_as_(&a, "(1 + 2) * 3", "(* (BR (+ 1 2)) 3)"));
  assert(parse_as_(&a, "1 * (2) * 3", "(* (* 1 (BR 2)) 3)"));
  assert(parse_as_(&a, "1 * (2 + c)", "(* 1 (BR (+ 2 (id c))))"));

  assert(parse_as_(&a, "!a", "(! (id a))"));
  assert(parse_as_(&a, "~a", "(~ (id a))"));
  assert(parse_as_(&a, "++a", "(++ (id a))"));

  assert(parse_as_(&a, "1 * *c", "(* 1 (* (id c)))"));
  assert(parse_as_(&a, "!a + *c", "(+ (! (id a)) (* (id c)))"));

  Arena_free(&a);
}

int main() {
  assert(sizeof(ptr_size) == sizeof(void *));

  arena_test();
  list_test();
  parser_atom_test();
  parser_list_test();
  parser_lisp_compare();
  parser_lisp_out();
  parser_gnq_test();

  printf("ok\n");
  return 0;
}