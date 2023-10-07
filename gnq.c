#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <libtcc.h>

typedef uintptr_t ptr_size;

#ifdef _WIN32
#define SLD "%lld"
#else
#define SLD "%ld"
#endif

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
  while (*st->c && /* *st->c != '\n' && */ isspace(*st->c))
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

bool check_word(State *st, const char *word) {
  skip_whitespace(st);
  State old = *st;
  while (st->c[0] && *word && *word == st->c[0]) {
    State_skip(st);
    ++word;
  }
  if (*word == 0 && !isalnum(st->c[0]) && st->c[0] != '_')
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
    {":=", 100 - 14, ASSOC_RIGHT, false},  //
    {"=", 100 - 14, ASSOC_RIGHT, false},   //
};
BinOp *getop(const char *ch) {
  for (size_t i = 0; i < sizeof(ops) / sizeof(ops[0]); ++i)
    if (strcmp(ops[i].op, ch) == 0)
      return ops + i;
  return NULL;
}

typedef struct Node Node;

typedef enum ValueType {
  Pair = 0,
  NumberInt = 1,
  NumberFloat = 3,
  Bool = 5,
  StringShort = 7,
  StringLong = 9,
  SymbolShort = 11,
  SymbolLong = 13,
} ValueType;

typedef union Value {
  Node *n;
  ValueType t;
  bool b;
  int64_t ni;
  double nf;
  char ss[8];
  char *ls;
} Value;

struct Node {
  Value car, cdr;
};

void lisp_dbg(const char *t, Node *a);

ValueType gnq_type(Node *n) {
  assert(n);
  return (n->car.t & 0x1) ? n->car.t : Pair;
}
bool gnq_is_sym(Node *n) {
  ValueType t = gnq_type(n);
  return t == SymbolShort || t == SymbolLong;
}
bool gnq_is_str(Node *n) {
  ValueType t = gnq_type(n);
  return t == StringShort || t == StringLong;
}
bool gnq_is_pair(Node *n) { return gnq_type(n) == Pair; }

typedef struct Arena {
  Node *memory;
  size_t len;
  size_t cap;

  Node *arrays;
  Node *structs;
  Node *functions;
} Arena;

Node nil = (Node){NULL, NULL};
Node *SYM_ARR = &(Node){.car = {.t = SymbolShort}, .cdr = {.ss = "[_]"}};
Node *SYM_STRUCT = &(Node){.car = {.t = SymbolShort}, .cdr = {.ss = "{_}"}};

Arena Arena_create(size_t nb_nodes) {
  return (Arena){(Node *)malloc(nb_nodes * sizeof(Node)), 0, nb_nodes, &nil, &nil, &nil};
}

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

Node *gnq_bool(Arena *a, bool b) {
  Node *n = Arena_node(a, Bool);
  n->cdr.b = b;
  return n;
}
bool gnq_tobool(Node *n) {
  assert(n && gnq_type(n) == Bool);
  return n->cdr.b;
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
  assert(n && gnq_is_str(n));

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

bool gnq_is_call(Node *n, const char *sym) {
  return gnq_is_pair(n) && gnq_is_sym(gnq_car(n)) && strcmp(sym, gnq_tosym(gnq_car(n))) == 0;
}

bool gnq_is_nil(Node *n) { return n == &nil; }

Node *gnq_as_list(Arena *a, int count, Node *nodes[]) {
  Node *n = &nil;
  for (int i = count - 1; i >= 0; --i)
    n = gnq_cons(a, nodes[i], n);
  return n;
}
Node *gnq_list(Arena *a, int count, ...) {
  Node *nodes[16];

  va_list argp;
  va_start(argp, count);
  for (int i = 0; i < count; ++i) {
    assert(i < 16);
    nodes[i] = va_arg(argp, Node *);
  }
  va_end(argp);

  return gnq_as_list(a, count, nodes);
}

Node *gnq_next(Node **list) {
  Node *n = gnq_car(*list);
  *list = gnq_cdr(*list);
  return n;
}
int gnq_list_len(Node *n) {
  int len = 0;
  while (!gnq_is_nil(n)) {
    gnq_next(&n);
    ++len;
  }
  return len;
}

Node *gnq_create_array_type_for(Arena *a, Node *sub) {
  Node *arr = a->arrays;
  while (!gnq_is_nil(arr)) {
    Node *x = gnq_next(&arr);
    assert(gnq_is_pair(x));
    assert(SYM_ARR == gnq_car(x));
    assert(gnq_is_pair(gnq_cdr(x)));
    if (gnq_car(gnq_cdr(x)) == sub)
      return x;
  }

  Node *next = gnq_list(a, gnq_is_nil(sub) ? 1 : 2, SYM_ARR, sub);
  a->arrays = gnq_cons(a, next, a->arrays);
  return next;
}

bool gnq_equal(Node *a, Node *b);

Node *find_struct_type_for(Arena *a, Node *sub) {
  Node *stru = a->structs;

  while (!gnq_is_nil(stru)) {
    Node *x = gnq_next(&stru);
    // lisp_dbg("- a ", sub);
    // lisp_dbg("- b ", x);
    if (gnq_equal(x, sub))
      return x;
  }
  return NULL;
}

Node unparsed_return = (Node){.car = {.t = SymbolShort}, .cdr = {.ss = "<UNPAR>"}};
Node parsing_return = (Node){.car = {.t = SymbolShort}, .cdr = {.ss = "<PARSI>"}};

Node *gnq_fn_find_deduced(Node *fn, Node *param_types[], int param_len) {
  Node *a_deduced = gnq_cdr(gnq_cdr(gnq_cdr(fn)));
  while (!gnq_is_nil(a_deduced)) {
    Node *pl_head = gnq_next(&a_deduced);
    Node *d = pl_head;
    gnq_next(&d);
    if (gnq_list_len(d) != param_len)
      continue;
    bool equal = true;
    for (int i = 0; i < param_len && equal; ++i)
      equal = gnq_next(&d) == param_types[i];
    if (equal)
      return pl_head;
  }
  return NULL;
}

Node *gnq_fn_find_return_type(Node *fn, Node *param_types[], int param_len) {
  Node *deduced_types = gnq_fn_find_deduced(fn, param_types, param_len);
  if (deduced_types)
    return gnq_next(&deduced_types);
  return NULL;
}

Node *gnq_add_deduced_function(Arena *a, Node *fn, Node *param_types[], int param_len) {
  Node *return_type = gnq_fn_find_return_type(fn, param_types, param_len);
  if (return_type)
    return return_type;

  Node *a_deduced = gnq_cdr(gnq_cdr(gnq_cdr(fn)));
  Node *deduced_param = gnq_cons(a, &unparsed_return, gnq_as_list(a, param_len, param_types));
  Node *a_deduced_head = gnq_cdr(gnq_cdr(fn));
  a_deduced_head->cdr.n = gnq_cons(a, deduced_param, a_deduced_head->cdr.n);

  Node *fns = a->functions;
  while (!gnq_is_nil(fns)) {
    if (gnq_next(&fns) == fn)
      return &unparsed_return;
  }

  a->functions = gnq_cons(a, fn, a->functions);
  return &unparsed_return;
}

void gnq_replace_deduced_function_return(Node *fn, Node *param_types[], int param_len, Node *return_type) {
  Node *deduced_types = gnq_fn_find_deduced(fn, param_types, param_len);
  assert(deduced_types);
  assert(deduced_types->car.n == &unparsed_return || deduced_types->car.n == &parsing_return);
  deduced_types->car.n = return_type;
}

char name_buff[256];
const char *gnq_fn_c_name(Arena *a, Node *fn, Node *param_types[], int param_len) {
  int h = 0;
  Node *fns = a->functions;
  while (!gnq_is_nil(fns)) {
    ++h;
    if (gnq_next(&fns) != fn)
      continue;

    int t = 0;
    Node *a_deduced = gnq_cdr(gnq_cdr(gnq_cdr(fn)));
    while (!gnq_is_nil(a_deduced)) {
      ++t;
      Node *d = gnq_next(&a_deduced);
      gnq_next(&d);
      if (gnq_list_len(d) != param_len)
        continue;
      bool equal = true;
      for (int i = 0; i < param_len && equal; ++i)
        equal = gnq_next(&d) == param_types[i];
      if (equal) {
        snprintf(name_buff, sizeof(name_buff), "f%x%x", h, t);
        return name_buff;
      }
    }
  }

  assert(false);
  return "";
}

const char *gnq_fn_c_name_(Arena *a, Node *fn, Node *paraml) {
  Node *param[128];
  int param_len = 0;
  while (!gnq_is_nil(paraml)) {
    assert(param_len < 128);
    param[param_len++] = gnq_next(&paraml);
  }
  return gnq_fn_c_name(a, fn, param, param_len);
}

int gnq_list_entry(Node *l, Node *n) {
  int h = 0;
  while (!gnq_is_nil(l)) {
    ++h;
    if (gnq_next(&l) == n)
      return h;
  }
  return -1;
}

const char *gnq_struct_c_name(Arena *a, Node *st) {
  name_buff[0] = '\0';
  int entry = gnq_list_entry(a->structs, st);
  assert(entry >= 0);
  snprintf(name_buff, sizeof(name_buff), "s%x", entry);
  return name_buff;
}

const char *gnq_array_c_name(Arena *a, Node *st) {
  name_buff[0] = '\0';
  int entry = gnq_list_entry(a->arrays, st);
  assert(entry >= 0);
  snprintf(name_buff, sizeof(name_buff), "a%x", entry);
  return name_buff;
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

  n = gnq_bool(&a, true);
  assert(a.cap == 256);
  assert(a.len == 3);
  assert(Bool == gnq_type(n));
  assert(gnq_tobool(n));

  n = gnq_string(&a, "id");
  assert(a.cap == 256);
  assert(a.len == 4);
  assert(StringShort == gnq_type(n));
  assert(strcmp("id", gnq_tostring(n)) == 0);

  n = gnq_string(&a, "a way longer string ");
  assert(a.cap == 256);
  assert(a.len == 7);
  assert(StringLong == gnq_type(n));
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);

  Node *n2 = gnq_int(&a, -84);
  assert(strcmp("a way longer string ", gnq_tostring(n)) == 0);
  assert(a.cap == 256);
  assert(a.len == 8);
  assert(NumberInt == gnq_type(n2));
  assert(-84 == gnq_toint(n2));

  Node *nc = gnq_cons(&a, n, n2);
  assert(a.len == 9);
  assert(gnq_car(nc) == n);
  assert(gnq_cdr(nc) == n2);

  n = gnq_sym(&a, "id");
  assert(a.cap == 256);
  assert(a.len == 10);
  assert(SymbolShort == gnq_type(n));
  assert(strcmp("id", gnq_tosym(n)) == 0);

  n = gnq_sym(&a, "a_way_longer_symbol");
  assert(a.cap == 256);
  assert(a.len == 13);
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
  assert(gnq_is_nil(list));

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

Node *gnq_parse_boolean(Arena *a, State *st) {
  if (check_word(st, "true"))
    return gnq_bool(a, true);
  if (check_word(st, "false"))
    return gnq_bool(a, false);
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
  Node *boole = gnq_parse_boolean(a, st);
  if (boole)
    return boole;

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

  Node *nb = lisp_parse(&a, "  true");
  assert(nb && gnq_type(nb) == Bool && gnq_tobool(nb));

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
  assert(n && gnq_is_nil(n));
  n = lisp_parse(&a, "()");
  assert(n && gnq_is_nil(n));

  n = lisp_parse(&a, "(a)");
  assert(n && gnq_type(n) == Pair);
  Node *nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == SymbolShort && gnq_is_nil(n));

  n = lisp_parse(&a, "(1 2 3)");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 2 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 3 && gnq_is_nil(n));

  n = lisp_parse(&a, "(1 (2 3))");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == Pair && gnq_is_nil(n));
  n = nn;
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 2 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 3 && gnq_is_nil(n));

  n = lisp_parse(&a, "(1 () 3.2  gg)");
  assert(n && gnq_type(n) == Pair);
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberInt && gnq_toint(nn) == 1 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(gnq_is_nil(nn) && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == NumberFloat && gnq_tofloat(nn) == 3.2 && !gnq_is_nil(n));
  nn = gnq_next(&n);
  assert(nn && gnq_type(nn) == SymbolShort && strcmp(gnq_tosym(nn), "gg") == 0 && gnq_is_nil(n));

  Arena_free(&a);
}

bool gnq_equal(Node *a, Node *b) {
  assert(a);
  assert(b);

  if (gnq_type(a) != gnq_type(b))
    return false;

  if (gnq_type(a) == NumberInt)
    return gnq_toint(a) == gnq_toint(b);
  if (gnq_type(a) == NumberFloat)
    return gnq_tofloat(a) == gnq_tofloat(b);
  if (gnq_type(a) == Bool)
    return gnq_tobool(a) == gnq_tobool(b);
  if (gnq_is_str(a))
    return strcmp(gnq_tostring(a), gnq_tostring(b)) == 0;
  if (gnq_is_sym(a))
    return strcmp(gnq_tosym(a), gnq_tosym(b)) == 0;

  if (gnq_type(a) == Pair) {
    while (!gnq_is_nil(a) && !gnq_is_nil(b))
      if (!gnq_equal(gnq_next(&a), gnq_next(&b)))
        return false;
    return gnq_is_nil(a) && gnq_is_nil(b);
  }

  return false;
}

void parser_lisp_compare() {
  printf("parser_lisp_compare\n");

  Arena a = Arena_create(256);

  assert(gnq_equal(lisp_parse(&a, "42"), lisp_parse(&a, "42")));
  assert(gnq_equal(lisp_parse(&a, "true"), lisp_parse(&a, "true")));
  assert(gnq_equal(lisp_parse(&a, "false"), lisp_parse(&a, "false")));
  assert(!gnq_equal(lisp_parse(&a, "true"), lisp_parse(&a, "false")));
  assert(!gnq_equal(lisp_parse(&a, "false"), lisp_parse(&a, "true")));
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
  assert(a);

  if (gnq_type(a) == NumberInt)
    return snprintf(b, s, SLD, gnq_toint(a));
  if (gnq_type(a) == NumberFloat)
    return snprintf(b, s, "%g", gnq_tofloat(a));
  if (gnq_type(a) == Bool)
    return snprintf(b, s, "%s", gnq_tobool(a) ? "true" : "false");
  if (gnq_type(a) == StringShort || gnq_type(a) == StringLong)
    return snprintf(b, s, "\"%s\"", gnq_tostring(a));
  if (gnq_type(a) == SymbolShort || gnq_type(a) == SymbolLong)
    return snprintf(b, s, "%s", gnq_tosym(a));

  if (gnq_type(a) == Pair) {
    size_t i = snprintf(b, s, "(");
    while (!gnq_is_nil(a)) {
      if (i > 1)
        i += snprintf(b + i, s - i, " ");
      i += lisp_str(b + i, s - i, gnq_next(&a));
    }
    i += snprintf(b + i, s - i, ")");
    return i;
  }

  return 0;
}

void lisp_dbg(const char *t, Node *a) {
  char b[256];
  lisp_str(b, 256, a);
  printf("%s%s\n", t, b);
}

void parser_lisp_out() {
  printf("parser_lisp_out\n");

  Arena a = Arena_create(256);
  char b[256];

  assert(lisp_str(b, 256, lisp_parse(&a, "42")) == 2);
  assert(strcmp("42", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, "4.2")) == 3);
  assert(strcmp("4.2", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, "true")) == 4);
  assert(strcmp("true", b) == 0);
  assert(lisp_str(b, 256, lisp_parse(&a, "false")) == 5);
  assert(strcmp("false", b) == 0);
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

Node *gnq_parse_expression(Arena *a, State *st);

Node *gnq_parse_expression_list(Arena *a, State *st) {
  Node *arg = &nil;
  Node *last = NULL;
  Node *x = NULL;
  while ((x = gnq_parse_expression(a, st))) {
    if (!last)
      arg = last = gnq_cons(a, x, &nil);
    else {
      last->cdr.n = gnq_cons(a, x, &nil);
      last = last->cdr.n;
    }
    if (!check_op(st, ","))
      break;
  }
  return arg;
}

Node *gnq_parse_suffix_expression(Arena *a, State *st, Node *e) {
  skip_whitespace(st);
  State old = *st;

  Node *suffix = NULL;
  // if (check_whitespace_for_nl(st))
  //   return e;

  const char *un_post_ops[] = {">++", ">--"};
  for (size_t i = 0; !suffix && i < sizeof(un_post_ops) / sizeof(const char *); ++i) {
    if (check_op(st, un_post_ops[i] + 1)) {
      suffix = gnq_list(a, 2, gnq_sym(a, un_post_ops[i]), e);
      break;
    }
  }

  const char *member_access[] = {"->", "."};
  for (size_t i = 0; !suffix && i < sizeof(member_access) / sizeof(const char *); ++i) {
    if (check_op(st, member_access[i])) {
      Node *member = gnq_parse_id(a, st);
      assert(member);
      suffix = gnq_list(a, 3, gnq_sym(a, member_access[i]), e, member);
    }
  }

  if (!suffix && check_op(st, "[")) {
    Node *index = gnq_parse_expression(a, st);
    bool expect_closing_square_brace = check_op(st, "]");
    assert(expect_closing_square_brace);
    suffix = gnq_list(a, index ? 3 : 2, gnq_sym(a, "[]"), e, index);
  }

  if (!suffix && check_op(st, "(")) {
    Node *arg = gnq_parse_expression_list(a, st);
    bool expect_closing_parameter_list = check_op(st, ")");
    assert(expect_closing_parameter_list);
    suffix = gnq_list(a, 3, gnq_sym(a, "call"), e, arg);
  }

  // if (check_word(st, "as")) {
  //   Expression *cast = Program_new_Expression(p, AsCast, old.location);
  //   cast->cast->o = e;
  //   cast->cast->type = Program_parse_declared_type(p, m, st);
  //   return cast;
  // }

  if (suffix) {
    Node *inner_suffix = gnq_parse_suffix_expression(a, st, suffix);
    if (inner_suffix)
      suffix = inner_suffix;
  }

  return suffix;
}

Node *gnq_parse_statement(Arena *a, State *st);

Node *gnq_parse_unary_operand(Arena *a, State *st) {
  gnq_skip_white(st);

  if (check_word(st, "fn")) {
    bool expect_fn_brace = check_op(st, "(");
    assert(expect_fn_brace);
    Node *arg = gnq_parse_expression_list(a, st);
    bool expect_closing_parameter_list = check_op(st, ")");
    assert(expect_closing_parameter_list);
    Node *fn_scope = gnq_parse_statement(a, st);
    assert(fn_scope);
    return gnq_list(a, 3, gnq_sym(a, "fn"), arg, fn_scope);
  }

  Node *unary = NULL;
  if ((unary = gnq_parse_string(a, st)))
    ;
  else if ((unary = gnq_parse_number(a, st)))
    ;
  else if ((unary = gnq_parse_boolean(a, st)))
    ;
  else if ((unary = gnq_parse_id(a, st)))
    ;

  const char *un_pre_ops[] = {"++", "--", "*", "~", "!", "-", "+", "&"};
  for (size_t i = 0; !unary && i < sizeof(un_pre_ops) / sizeof(const char *); ++i) {
    if (check_op(st, un_pre_ops[i])) {
      Node *op = gnq_parse_unary_operand(a, st);
      assert(op);
      unary = gnq_list(a, 2, gnq_sym(a, un_pre_ops[i]), op);
    }
  }

  if (!unary && check_op(st, "(")) {
    Node *brace = gnq_parse_expression(a, st);
    assert(brace);
    bool expect_closing_brace = check_op(st, ")");
    assert(expect_closing_brace);
    unary = gnq_list(a, 2, gnq_sym(a, "BR"), brace);
  }

  if (!unary && check_op(st, "{")) {
    Node *arg = gnq_parse_expression_list(a, st);
    bool expect_closing_construction = check_op(st, "}");
    assert(expect_closing_construction);
    unary = gnq_cons(a, SYM_STRUCT, arg);
  }

  if (!unary && check_op(st, "[")) {
    Node *arg = gnq_parse_expression_list(a, st);
    bool expect_closing_array = check_op(st, "]");
    assert(expect_closing_array);
    unary = gnq_cons(a, SYM_ARR, arg);
  }

  Node *suffix = gnq_parse_suffix_expression(a, st, unary);
  if (suffix)
    unary = suffix;

  return unary;
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

Node *gnq_parse_expression(Arena *a, State *st) {
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

  if (check_op(st, "?")) {
    Node *ternary_if = gnq_parse_expression(a, st);
    assert(ternary_if);
    bool expect_ternary_colon = check_op(st, ":");
    assert(expect_ternary_colon);
    Node *ternary_else = gnq_parse_expression(a, st);
    assert(ternary_else);
    yard.val_stack[0] = gnq_list(a, 4, gnq_sym(a, "?:"), yard.val_stack[0], ternary_if, ternary_else);
  }

  return yard.val_stack[0];
}

Node *gnq_parse_statement(Arena *a, State *st) {
  if (check_op(st, "{")) {
    Node *stat = &nil;
    Node *last = NULL;
    Node *x = NULL;
    while ((x = gnq_parse_statement(a, st))) {
      if (!last)
        stat = last = gnq_cons(a, x, &nil);
      else {
        last->cdr.n = gnq_cons(a, x, &nil);
        last = last->cdr.n;
      }
    }
    bool expect_closing_scope = check_op(st, "}");
    assert(expect_closing_scope);
    return gnq_cons(a, gnq_sym(a, "{}"), stat);
  }

  if (check_word(st, "return")) {
    Node *e = gnq_parse_expression(a, st);
    return gnq_list(a, e ? 2 : 1, gnq_sym(a, "return"), e);
  }

  if (check_word(st, "break"))
    return gnq_list(a, 1, gnq_sym(a, "break"));
  if (check_word(st, "continue"))
    return gnq_list(a, 1, gnq_sym(a, "continue"));

  if (check_word(st, "if")) {
    bool expect_if_brace = check_op(st, "(");
    assert(expect_if_brace);
    Node *if_condition = gnq_parse_expression(a, st);
    assert(if_condition);
    bool expect_if_brace_close = check_op(st, ")");
    assert(expect_if_brace_close);
    Node *if_branch = gnq_parse_statement(a, st);
    assert(if_branch);
    if (!check_word(st, "else"))
      return gnq_list(a, 3, gnq_sym(a, "if"), if_condition, if_branch);
    Node *else_branch = gnq_parse_statement(a, st);
    assert(else_branch);
    return gnq_list(a, 4, gnq_sym(a, "if"), if_condition, if_branch, else_branch);
  }

  if (check_word(st, "while")) {
    bool expect_while_brace = check_op(st, "(");
    assert(expect_while_brace);
    Node *while_condition = gnq_parse_expression(a, st);
    assert(while_condition);
    bool expect_while_brace_close = check_op(st, ")");
    assert(expect_while_brace_close);
    Node *while_scope = gnq_parse_statement(a, st);
    assert(while_scope);
    return gnq_list(a, 3, gnq_sym(a, "while"), while_condition, while_scope);
  }

  if (check_word(st, "do")) {
    Node *do_while_scope = gnq_parse_statement(a, st);
    assert(do_while_scope);
    bool while_in_do_while = check_word(st, "while");
    assert(while_in_do_while);
    bool expect_do_while_brace = check_op(st, "(");
    assert(expect_do_while_brace);
    Node *while_condition = gnq_parse_expression(a, st);
    assert(while_condition);
    bool expect_do_while_brace_close = check_op(st, ")");
    assert(expect_do_while_brace_close);
    return gnq_list(a, 3, gnq_sym(a, "dowhile"), do_while_scope, while_condition);
  }

  if (check_word(st, "for")) {
    bool expect_for_brace = check_op(st, "(");
    assert(expect_for_brace);
    Node *for_init = gnq_parse_expression(a, st);
    bool expect_for_init_break = check_op(st, ";");
    assert(expect_for_init_break);
    Node *for_condition = gnq_parse_expression(a, st);
    bool expect_for_condition_break = check_op(st, ";");
    assert(expect_for_condition_break);
    Node *for_increment = gnq_parse_expression(a, st);
    bool expect_for_brace_close = check_op(st, ")");
    assert(expect_for_init_break);
    Node *for_scope = gnq_parse_statement(a, st);
    return gnq_list(a, 5, gnq_sym(a, "for"), for_init ? for_init : &nil, for_condition ? for_condition : &nil,
                    for_increment ? for_increment : &nil, for_scope);
  }

  if (check_word(st, "case")) {
    Node *case_condition = gnq_parse_expression(a, st);
    assert(case_condition);
    bool expect_colon_after_case = check_op(st, ":");
    assert(expect_colon_after_case);
    Node *case_scope = gnq_parse_statement(a, st);
    assert(case_scope);
    return gnq_list(a, 3, gnq_sym(a, "case"), case_condition, case_scope);
  }

  if (check_word(st, "default")) {
    bool expect_colon_after_default = check_op(st, ":");
    assert(expect_colon_after_default);
    Node *default_scope = gnq_parse_statement(a, st);
    assert(default_scope);
    return gnq_list(a, 2, gnq_sym(a, "default"), default_scope);
  }

  if (check_word(st, "switch")) {
    bool expect_switch_brace = check_op(st, "(");
    assert(expect_switch_brace);
    Node *switch_condition = gnq_parse_expression(a, st);
    assert(switch_condition);
    bool expect_switch_brace_close = check_op(st, ")");
    assert(expect_switch_brace_close);
    Node *switch_scope = gnq_parse_statement(a, st);
    assert(switch_scope);
    return gnq_list(a, 3, gnq_sym(a, "switch"), switch_condition, switch_scope);
  }

  if (check_word(st, "fn")) {
    skip_whitespace(st);
    Node *fn_name = gnq_parse_id(a, st);
    assert(fn_name);
    bool expect_fn_parameter_brace = check_op(st, "(");
    assert(expect_fn_parameter_brace);
    Node *fn_args = gnq_parse_expression_list(a, st);
    assert(fn_args);
    bool expect_fn_brace_close = check_op(st, ")");
    assert(expect_fn_brace_close);
    Node *fn_scope = gnq_parse_statement(a, st);
    assert(fn_scope);
    return gnq_list(a, 3, gnq_sym(a, ":="), fn_name, gnq_list(a, 3, gnq_sym(a, "fn"), fn_args, fn_scope));
  }

  return gnq_parse_expression(a, st);
}

bool parse_as_(Arena *a, const char *gnq, const char *lisp) {
  State s = (State){gnq, {0, 0}};
  Node *from_lisp = lisp_parse(a, lisp);
  Node *from_gnq = gnq_parse_statement(a, &s);
  if (gnq_equal(from_gnq, from_lisp))
    return true;

  char b1[256] = {0};
  lisp_str(b1, sizeof(b1), from_lisp);
  char b2[256] = {0};
  lisp_str(b2, sizeof(b2), from_gnq);
  printf("expect '%s' got '%s'\n", b1, b2);
  return false;
}

void parser_gnq_expression_test() {
  printf("parser_gnq_expression_test\n");

  Arena a = Arena_create(2048);

  assert(parse_as_(&a, "42", "42"));
  assert(parse_as_(&a, "-42", "-42"));
  assert(parse_as_(&a, "-4.21b", "-4.21"));
  assert(parse_as_(&a, "\"str\"", "\"str\""));
  assert(parse_as_(&a, "  \"str\"", "\"str\""));

  assert(parse_as_(&a, "true", "true"));
  assert(parse_as_(&a, "false", "false"));

  assert(parse_as_(&a, "var", "(id var)"));
  assert(parse_as_(&a, "_var2", "(id _var2)"));

  assert(parse_as_(&a, "a + 1", "(+ (id a) 1)"));
  assert(parse_as_(&a, "1 + 2 * 3", "(+ 1 (* 2 3))"));
  assert(parse_as_(&a, "1 * 2 + 3", "(+ (* 1 2) 3)"));
  assert(parse_as_(&a, "1 - 2 % 3", "(- 1 (% 2 3))"));
  assert(parse_as_(&a, "1 | 2 & 3", "(| 1 (& 2 3))"));
  assert(parse_as_(&a, "1 || 2 && 3", "(|| 1 (&& 2 3))"));

  assert(parse_as_(&a, "a.b->c", "(-> (. (id a) (id b)) (id c))"));
  assert(parse_as_(&a, "a->b.c", "(. (-> (id a) (id b)) (id c))"));
  assert(parse_as_(&a, "a + b.c", "(+ (id a) (. (id b) (id c)))"));

  assert(parse_as_(&a, "(1 + 2) * 3", "(* (BR (+ 1 2)) 3)"));
  assert(parse_as_(&a, "1 * (2) * 3", "(* (* 1 (BR 2)) 3)"));
  assert(parse_as_(&a, "1 * (2 + c)", "(* 1 (BR (+ 2 (id c))))"));

  assert(parse_as_(&a, "!a", "(! (id a))"));
  assert(parse_as_(&a, "~a", "(~ (id a))"));
  assert(parse_as_(&a, "++a", "(++ (id a))"));

  assert(parse_as_(&a, "1 * *c", "(* 1 (* (id c)))"));
  assert(parse_as_(&a, "!a + *c", "(+ (! (id a)) (* (id c)))"));

  assert(parse_as_(&a, "a++", "(>++ (id a))"));
  assert(parse_as_(&a, "b--", "(>-- (id b))"));

  assert(parse_as_(&a, "b[1]", "([] (id b) 1)"));
  assert(parse_as_(&a, "b[1][2]", "([] ([] (id b) 1) 2)"));

  assert(parse_as_(&a, "b[1]++", "(>++ ([] (id b) 1))"));
  assert(parse_as_(&a, "b++[1]", "([] (>++ (id b)) 1)"));
  assert(parse_as_(&a, "b++[1]--", "(>-- ([] (>++ (id b)) 1))"));

  assert(parse_as_(&a, "b()", "(call (id b) ())"));
  assert(parse_as_(&a, "b(1)", "(call (id b) (1))"));
  assert(parse_as_(&a, "b(1, 2, 3)", "(call (id b) (1 2 3))"));
  assert(parse_as_(&a, "b(1, 2, k[1])", "(call (id b) (1 2 ([] (id k) 1)))"));
  assert(parse_as_(&a, "b(1)(2)(3)", "(call (call (call (id b) (1)) (2)) (3))"));

  assert(parse_as_(&a, "a.b + c", "(+ (. (id a) (id b)) (id c))"));
  assert(parse_as_(&a, "a + b.c", "(+ (id a) (. (id b) (id c)))"));

  assert(parse_as_(&a, "a + b()", "(+ (id a) (call (id b) ()))"));
  assert(parse_as_(&a, "a.b()", "(call (. (id a) (id b)) ())"));
  assert(parse_as_(&a, "a.b->c()", "(call (-> (. (id a) (id b)) (id c)) ())"));

  assert(parse_as_(&a, "++b()", "(++ (call (id b) ()))"));
  assert(parse_as_(&a, "b()++", "(>++ (call (id b) ()))"));

  assert(parse_as_(&a, "1 ? 2 : 3", "(?: 1 2 3)"));
  assert(parse_as_(&a, "1 ? 2 + 3 : 4 * 5", "(?: 1 (+ 2 3) (* 4 5))"));
  assert(parse_as_(&a, "1 + 2 ? 3 : 4", "(?: (+ 1 2) 3 4)"));

  assert((1 ? 2 ? 3 : 4 : 5) == 3);
  assert((1 ? 0 ? 3 : 4 : 5) == 4);
  assert((0 ? 0 ? 3 : 4 : 5) == 5);
  assert((0 ? 1 ? 3 : 4 : 5) == 5);
  assert(parse_as_(&a, "1 ? 2 ? 3 : 4 : 5", "(?: 1 (?: 2 3 4) 5)"));

  Arena_free(&a);
}

void parser_gnq_statements_test() {
  printf("parser_gnq_statements_test\n");

  Arena a = Arena_create(2048);

  assert(parse_as_(&a, "return 42", "(return 42)"));
  assert(parse_as_(&a, "return", "(return)"));

  assert(parse_as_(&a, "break", "(break)"));
  assert(parse_as_(&a, "continue", "(continue)"));

  assert(parse_as_(&a, "if (1) 2", "(if 1 2)"));
  assert(parse_as_(&a, "if (0) 1 else 2", "(if 0 1 2)"));

  assert(parse_as_(&a, "if (0) 1 else if (2) 3", "(if 0 1 (if 2 3))"));

  assert(parse_as_(&a, "while (1) 2", "(while 1 2)"));

  assert(parse_as_(&a, "for (1; 2; 3) 4", "(for 1 2 3 4)"));
  assert(parse_as_(&a, "for (; 2; 3) 4", "(for () 2 3 4)"));
  assert(parse_as_(&a, "for (;; 3) 4", "(for () () 3 4)"));
  assert(parse_as_(&a, "for (;;) 4", "(for () () () 4)"));

  assert(parse_as_(&a, "do 1 while (2)", "(dowhile 1 2)"));

  assert(parse_as_(&a, "case 1: 2", "(case 1 2)"));
  assert(parse_as_(&a, "default: 1", "(default 1)"));
  assert(parse_as_(&a, "switch (1) 2", "(switch 1 2)"));

  assert(parse_as_(&a, "{}", "({})"));
  assert(parse_as_(&a, "{1}", "({} 1)"));
  assert(parse_as_(&a, "{1 2}", "({} 1 2)"));
  assert(parse_as_(&a, "{1+2}", "({} (+ 1 2))"));
  assert(parse_as_(&a, "{1+2 3 4}", "({} (+ 1 2) 3 4)"));

  assert(parse_as_(&a, "if (0) { 1 2 } else { 3 4 }", "(if 0 ({} 1 2) ({} 3 4))"));
  assert(parse_as_(&a, "while (0) { 1 2 }", "(while 0 ({} 1 2))"));
  assert(parse_as_(&a, "for (;;) { 1 2 }", "(for () () () ({} 1 2))"));
  assert(parse_as_(&a, "do { 1 2 } while (3)", "(dowhile ({} 1 2) 3)"));

  Arena_free(&a);
}

void parser_gnq_functions_test() {
  printf("parser_gnq_functions_test\n");

  Arena a = Arena_create(2048);

  assert(parse_as_(&a, "fn func() {}", "(:= (id func) (fn () ({})))"));
  assert(parse_as_(&a, "fn func(a) {}", "(:= (id func) (fn ((id a)) ({})))"));
  assert(parse_as_(&a, "fn func(a, b, c) {}", "(:= (id func) (fn ((id a) (id b) (id c)) ({})))"));
  assert(parse_as_(&a, "fn func(a) { a+=2 return a }", //
                   "(:= (id func) (fn ((id a)) ({} (+= (id a) 2) (return (id a)))))"));

  Arena_free(&a);
}

void parser_gnq_construction_test() {
  printf("parser_gnq_construction_test\n");

  Arena a = Arena_create(2048);

  assert(parse_as_(&a, "a := 1", "(:= (id a) 1)"));
  assert(parse_as_(&a, "a.b := 1", "(:= (. (id a) (id b)) 1)"));

  assert(parse_as_(&a, "a := {}", "(:= (id a) ({_}))"));
  assert(parse_as_(&a, "a := {1}", "(:= (id a) ({_} 1))"));
  assert(parse_as_(&a, "a := {1, 2, 3}", "(:= (id a) ({_} 1 2 3))"));
  assert(parse_as_(&a, "a := {b = 1}", "(:= (id a) ({_} (= (id b) 1)))"));

  assert(parse_as_(&a, "a := []", "(:= (id a) ([_]))"));
  assert(parse_as_(&a, "a := [1]", "(:= (id a) ([_] 1))"));
  assert(parse_as_(&a, "a := [1, 2, 3]", "(:= (id a) ([_] 1 2 3))"));

  assert(parse_as_(&a, "a := fn () {}", "(:= (id a) (fn () ({})))"));

  Arena_free(&a);
}

Node *gnq_parse_all(Arena *a, State *st) {
  Node *stat = &nil;
  Node *last = NULL;
  Node *x = NULL;
  while ((x = gnq_parse_statement(a, st))) {
    if (!last)
      stat = last = gnq_cons(a, x, &nil);
    else {
      last->cdr.n = gnq_cons(a, x, &nil);
      last = last->cdr.n;
    }
  }
  return stat;
}

Node SYM_MOD = (Node){{.t = SymbolShort}, {.ss = "mod"}};
Node *gnq_parse_mod(Arena *a, State *st) {
  Node *all = gnq_parse_all(a, st);
  return gnq_cons(a, &SYM_MOD, all);
}

void some_func(int v, const char *t) { printf("- %d '%s'\n", v, t); }

void execute_c(const char *code, int argc, char **argv) {
  TCCState *tcc = tcc_new();
  tcc_set_output_type(tcc, TCC_OUTPUT_MEMORY);
  tcc_add_include_path(tcc, "/usr/lib/tcc/include");
  tcc_set_lib_path(tcc, "/usr/lib/tcc/");

  tcc_add_symbol(tcc, "some_func", some_func);
  tcc_compile_string(tcc, code);
  tcc_run(tcc, argc, argv);

  tcc_delete(tcc);
}

typedef struct TypeStackEntry {
  Node *n;
  const char *id;
} TypeStackEntry;

typedef struct TypeStack {
  TypeStackEntry stack[1024];
  int len, cap;
} TypeStack;

void TypeStack_push(TypeStack *ts, const char *id, Node *n) {
  // printf("push '%s'\n", id);
  ts->stack[ts->len] = (TypeStackEntry){n, id};
  ts->len++;
}
Node *TypeStack_find(TypeStack *ts, const char *id) {
  // printf("find '%s'\n", id);
  for (int i = ts->len - 1; i >= 0; --i)
    if (strcmp(ts->stack[i].id, id) == 0)
      return ts->stack[i].n;
  return NULL;
}
int TypeStack_state(TypeStack *ts) { return ts->len; }
void TypeStack_revert(TypeStack *ts, int l) { ts->len = l; }

Node *gnq_deduce_types(Arena *a, TypeStack *ts, Node *n, Node **rt);

Node *gnq_struct_member(Arena *a, TypeStack *ts, Node *n) {
  Node *sub = &nil;
  while (!gnq_is_nil(n)) {
    Node *sn = gnq_next(&n);
    assert(gnq_type(sn) == Pair);
    assert(gnq_is_sym(gnq_car(sn)));
    assert(strcmp(gnq_tosym(gnq_car(sn)), "=") == 0);
    assert(gnq_type(gnq_cdr(sn)) == Pair);
    assert(gnq_type(gnq_car(gnq_cdr(sn))) == Pair);
    assert(gnq_is_sym(gnq_car(gnq_car(gnq_cdr(sn)))));
    assert(strcmp("id", gnq_tosym(gnq_car(gnq_car(gnq_cdr(sn))))) == 0);
    // list_dbg("{_}: ", gnq_car(gnq_cdr(gnq_car(gnq_cdr(sn)))));
    assert(gnq_is_sym(gnq_car(gnq_cdr(gnq_car(gnq_cdr(sn))))));
    Node *mem = gnq_car(gnq_cdr(gnq_car(gnq_cdr(sn))));
    Node *val = gnq_car(gnq_cdr(gnq_cdr(sn)));
    assert(val && !gnq_is_nil(val));
    Node *type = gnq_deduce_types(a, ts, val, NULL);
    assert(type && !gnq_is_nil(type));
    sub = gnq_cons(a, gnq_list(a, 2, mem, type), sub);
  }
  return gnq_cons(a, SYM_STRUCT, sub);
}

const char *gnq_id_sym(Node *id) {
  Node *var = gnq_next(&id);
  assert(gnq_is_sym(var));
  return gnq_tosym(gnq_next(&id));
}

Node i32 = (Node){{.t = SymbolShort}, {.ss = "i32"}};
Node f64 = (Node){{.t = SymbolShort}, {.ss = "f64"}};
Node str = (Node){{.t = SymbolShort}, {.ss = "str"}};
Node boolean = (Node){{.t = SymbolShort}, {.ss = "bool"}};

Node *gnq_deduce_types(Arena *a, TypeStack *ts, Node *n, Node **rt) {
  if (gnq_type(n) == NumberInt)
    return &i32;
  if (gnq_type(n) == NumberFloat)
    return &f64;
  if (gnq_type(n) == Bool)
    return &boolean;
  if (gnq_is_str(n))
    return &str;

  Node *head = n;
  if (gnq_type(n) == Pair) {
    Node *sym = gnq_next(&n);
    assert(gnq_is_sym(sym));
    const char *syms = gnq_tosym(sym);
    if (strcmp(syms, "id") == 0) {
      Node *var = gnq_next(&n);
      assert(gnq_is_sym(var));
      Node *type_of_id = TypeStack_find(ts, gnq_tosym(var));
      assert(type_of_id);
      return type_of_id;
    }

    if (strcmp(syms, ":=") == 0) {
      Node *var = gnq_next(&n);
      assert(gnq_is_call(var, "id"));
      Node *t = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      assert(!gnq_is_nil(t));
      TypeStack_push(ts, gnq_id_sym(var), t);
      return t;
    }

    if (strcmp(syms, "{}") == 0) {
      int te_state = TypeStack_state(ts);
      while (!gnq_is_nil(n))
        gnq_deduce_types(a, ts, gnq_next(&n), rt);
      TypeStack_revert(ts, te_state);
      return &nil;
    }
    if (sym == SYM_ARR) {
      Node *sub = &nil;
      while (!gnq_is_nil(n))
        sub = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      return gnq_create_array_type_for(a, sub);
    }

    if (strcmp(syms, "BR") == 0) {
      return gnq_deduce_types(a, ts, gnq_next(&n), rt);
    }

    if (strcmp(syms, "[]") == 0) {
      Node *array_type = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      assert(gnq_is_call(array_type, "[_]"));
      return gnq_car(gnq_cdr(array_type));
    }

    if (sym == SYM_STRUCT) {
      Arena aa = Arena_create(128);
      int ts_state = TypeStack_state(ts);
      // deduce twice to not leak memory
      Node *struct_type = gnq_struct_member(&aa, ts, n);
      TypeStack_revert(ts, ts_state);
      if ((struct_type = find_struct_type_for(a, struct_type)))
        return struct_type;
      struct_type = gnq_struct_member(a, ts, n);
      a->structs = gnq_cons(a, struct_type, a->structs);
      return struct_type;
    }

    if (strcmp(syms, ".") == 0) {
      Node *struct_type = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      assert(gnq_is_call(struct_type, "{_}"));
      gnq_next(&struct_type);
      Node *mem_look = gnq_next(&n);
      assert(gnq_is_call(mem_look, "id"));
      const char *search_id = gnq_id_sym(mem_look);
      while (!gnq_is_nil(struct_type)) {
        Node *mem = gnq_next(&struct_type);
        // lisp_dbg("test struct member ", mem);
        if (gnq_is_call(mem, search_id))
          return gnq_car(gnq_cdr(mem));
      }
#define DID_NOT_FIND_STRUCT_MEMBER false
      assert(DID_NOT_FIND_STRUCT_MEMBER);
      return &nil;
    }

    if (strcmp(syms, "break") == 0 || strcmp(syms, "continue") == 0)
      return &nil;
    if (strcmp(syms, "return") == 0) {
      if (!gnq_is_nil(n)) {
        assert(rt != NULL);
        Node *deduced_return = gnq_deduce_types(a, ts, gnq_next(&n), NULL);
        assert(deduced_return != &unparsed_return);
        if (*rt != &unparsed_return && deduced_return != &parsing_return) {
          if (*rt != deduced_return) {
            lisp_dbg("rt: ", *rt);
            lisp_dbg("dt: ", deduced_return);
#define EXPECT_EQUAL_RETURN_TYPE false
            assert(EXPECT_EQUAL_RETURN_TYPE);
          }
        }
        if (deduced_return != &parsing_return)
          *rt = deduced_return;
      }
      return &nil;
    }
    if (strcmp(syms, "if") == 0) {
      Node *if_condition = gnq_next(&n);
      assert(if_condition && !gnq_is_nil(if_condition));
      gnq_deduce_types(a, ts, if_condition, rt);
      Node *if_scope = gnq_next(&n);
      assert(if_scope && !gnq_is_nil(if_scope));
      gnq_deduce_types(a, ts, if_scope, rt);
      Node *else_scope = gnq_next(&n);
      if (else_scope && !gnq_is_nil(else_scope))
        gnq_deduce_types(a, ts, else_scope, rt);
      return &nil;
    }
    if (strcmp(syms, "for") == 0) {
      Node *for_init = gnq_next(&n);
      if (!gnq_is_nil(for_init))
        gnq_deduce_types(a, ts, for_init, rt);
      Node *for_condition = gnq_next(&n);
      if (!gnq_is_nil(for_condition))
        gnq_deduce_types(a, ts, for_condition, rt);
      Node *for_increment = gnq_next(&n);
      if (!gnq_is_nil(for_increment))
        gnq_deduce_types(a, ts, for_increment, rt);
      Node *for_scope = gnq_next(&n);
      assert(for_scope && !gnq_is_nil(for_scope));
      gnq_deduce_types(a, ts, for_scope, rt);
      return &nil;
    }
    if (strcmp(syms, "while") == 0) {
      Node *while_condition = gnq_next(&n);
      assert(while_condition && !gnq_is_nil(while_condition));
      gnq_deduce_types(a, ts, while_condition, rt);
      Node *while_scope = gnq_next(&n);
      assert(while_scope && !gnq_is_nil(while_scope));
      gnq_deduce_types(a, ts, while_scope, rt);
      return &nil;
    }
    if (strcmp(syms, "dowhile") == 0) {
      Node *do_while_scope = gnq_next(&n);
      assert(do_while_scope && !gnq_is_nil(do_while_scope));
      gnq_deduce_types(a, ts, do_while_scope, rt);
      Node *do_while_condition = gnq_next(&n);
      assert(do_while_condition && !gnq_is_nil(do_while_condition));
      gnq_deduce_types(a, ts, do_while_condition, rt);
      return &nil;
    }
    if (strcmp(syms, "case") == 0) {
      Node *case_condition = gnq_next(&n);
      assert(case_condition && !gnq_is_nil(case_condition));
      gnq_deduce_types(a, ts, case_condition, rt);
      Node *case_scope = gnq_next(&n);
      assert(case_scope && !gnq_is_nil(case_scope));
      gnq_deduce_types(a, ts, case_scope, rt);
      return &nil;
    }
    if (strcmp(syms, "default") == 0) {
      Node *default_scope = gnq_next(&n);
      assert(default_scope && !gnq_is_nil(default_scope));
      gnq_deduce_types(a, ts, default_scope, rt);
      return &nil;
    }
    if (strcmp(syms, "switch") == 0) {
      Node *switch_condition = gnq_next(&n);
      assert(switch_condition && !gnq_is_nil(switch_condition));
      gnq_deduce_types(a, ts, switch_condition, rt);
      Node *switch_scope = gnq_next(&n);
      assert(switch_scope && !gnq_is_nil(switch_scope));
      gnq_deduce_types(a, ts, switch_scope, rt);
      return &nil;
    }

    if (strcmp(syms, "fn") == 0) {
      return head;
    }

    if (strcmp(syms, "call") == 0) {
      // lisp_dbg("call ", n);
      Node *this_fn = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      // lisp_dbg(" - func ", fn);
      Node *c_param = gnq_next(&n);
      // lisp_dbg(" - parameter called ", c_param);

      assert(gnq_is_call(this_fn, "fn"));
      Node *fn = this_fn;
      Node *fn_sym = gnq_next(&fn);
      Node *fn_param = gnq_next(&fn);
      // lisp_dbg(" - parameter expect ", fn_param);
      Node *fn_scope = gnq_next(&fn);
      assert(gnq_is_call(fn_scope, "{}"));

      int ts_state = TypeStack_state(ts);

      Node *param_types[128];
      int param_len = 0;
      while (!gnq_is_nil(fn_param) && !gnq_is_nil(c_param)) {
        Node *p_id = gnq_next(&fn_param);
        assert(gnq_is_call(p_id, "id"));
        Node *c_type = gnq_deduce_types(a, ts, gnq_next(&c_param), rt);
        assert(!gnq_is_nil(c_type));
        TypeStack_push(ts, gnq_id_sym(p_id), c_type);

        assert(param_len < 128);
        param_types[param_len++] = c_type;
      }
      // expect the same number of parameter
      assert(gnq_is_nil(fn_param) && gnq_is_nil(c_param));

      assert(!gnq_is_nil(this_fn));
      Node *return_type = gnq_add_deduced_function(a, this_fn, param_types, param_len);
      if (return_type == &unparsed_return) {
        gnq_replace_deduced_function_return(this_fn, param_types, param_len, &parsing_return);

        gnq_deduce_types(a, ts, fn_scope, &return_type);
        if (return_type == &unparsed_return)
          return_type = &nil;
        gnq_replace_deduced_function_return(this_fn, param_types, param_len, return_type);
      }

      TypeStack_revert(ts, ts_state);

      return return_type;
    }

    const BinOp *op = NULL;
    for (size_t i = 0; i < sizeof(ops) / sizeof(ops[0]); ++i)
      if (strcmp(ops[i].op, syms) == 0)
        op = &ops[i];
    if (op) {
      Node *t1 = gnq_deduce_types(a, ts, gnq_next(&n), rt);
      Node *t2 = gnq_deduce_types(a, ts, gnq_next(&n), rt);

      assert(gnq_equal(t1, t2));
      if (op->returns_bool)
        return &boolean;
      return t1;
    }
  }

  lisp_dbg("unknown way to deduce type ", head);
#define DEDUCE_TYPE_CONSTRUCT_MISSING false
  assert(DEDUCE_TYPE_CONSTRUCT_MISSING);
  return NULL;
}

bool deduce_as__(Arena *a, TypeStack *ts, const char *gnq, const char *lisp) {
  Node *from_lisp = lisp_parse(a, lisp);
  Node *all = gnq_parse_all(a, &(State){gnq, {0, 0}});
  Node *deduced_gnq = NULL;
  Node *return_type = &unparsed_return;
  while (!gnq_is_nil(all))
    deduced_gnq = gnq_deduce_types(a, ts, gnq_next(&all), &return_type);
  assert(deduced_gnq);
  if (gnq_equal(deduced_gnq, from_lisp))
    return true;

  char b1[256] = {0};
  lisp_str(b1, sizeof(b1), from_lisp);
  char b2[256] = {0};
  lisp_str(b2, sizeof(b2), deduced_gnq);
  printf("expect '%s' got '%s'\n", b1, b2);
  return false;
}

bool deduce_as_(Arena *a, const char *gnq, const char *lisp) {
  TypeStack ts = (TypeStack){{}, 0, 0};
  return deduce_as__(a, &ts, gnq, lisp);
}

void gnq_deduce_types_test() {
  printf("gnq_deduce_types_test\n");

  Arena a = Arena_create(2048);

  assert(deduce_as_(&a, "42", "i32"));
  assert(deduce_as_(&a, "4.2", "f64"));
  assert(deduce_as_(&a, "\"xxx\"", "str"));
  assert(deduce_as_(&a, "true", "bool"));
  assert(deduce_as_(&a, "false", "bool"));

  assert(deduce_as_(&a, "42 + 21", "i32"));
  assert(deduce_as_(&a, "4.2 + 2.1", "f64"));
  assert(deduce_as_(&a, "42 == 21", "bool"));
  assert(deduce_as_(&a, "42 < 21", "bool"));

  assert(deduce_as_(&a, "(42 + 21)", "i32"));
  assert(deduce_as_(&a, "(2 + 1) * 4", "i32"));

  assert(deduce_as_(&a, "a := 21", "i32"));
  assert(deduce_as_(&a, "a := 2.1\n a", "f64"));

  assert(deduce_as_(&a, "{ a:=4.2 }", "()"));
  assert(deduce_as_(&a, "a := 21 \n { a:=4.2 } \n a", "i32"));

  assert(deduce_as_(&a, "if (true) { }", "()"));
  assert(deduce_as_(&a, "if (true) { } else {}", "()"));

  assert(deduce_as_(&a, "while (false) { }", "()"));

  assert(deduce_as_(&a, "do {} while (false)", "()"));

  assert(deduce_as_(&a, "for (;;) {}", "()"));

  assert(deduce_as_(&a, "break", "()"));
  assert(deduce_as_(&a, "continue", "()"));
  assert(deduce_as_(&a, "return", "()"));
  assert(deduce_as_(&a, "return 42", "()"));

  assert(deduce_as_(&a, "case 1: 2", "()"));
  assert(deduce_as_(&a, "default: 3", "()"));
  assert(deduce_as_(&a, "switch (1) 2", "()"));

  assert(deduce_as_(&a, "a := []", "([_])"));
  assert(deduce_as_(&a, "a := [1]", "([_] i32)"));
  assert(deduce_as_(&a, "a := [[1]]", "([_] ([_] i32))"));

  assert(deduce_as_(&a, "a := fn() {}", "(fn () ({}))"));
  assert(deduce_as_(&a, "fn a() {}", "(fn () ({}))"));
  assert(deduce_as_(&a, "fn a() {} a", "(fn () ({}))"));

  assert(deduce_as_(&a, "a := {}", "({_})"));
  assert(deduce_as_(&a, "a := { b = 42 }", "({_} (b i32))"));
  assert(deduce_as_(&a, "a := { b = 42, c = 2.3 }", "({_} (c f64) (b i32))"));

  assert(deduce_as_(&a, "a := { b = [42], c = { x = 2.3} }", "({_} (c ({_} (x f64))) (b ([_] i32)))"));

  Arena_free(&a);
}

void gnq_deduce_types_advanced_test() {
  printf("gnq_deduce_types_advanced_test\n");

  Node *rt;
  Arena a = Arena_create(128);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "a := 42", "i32"));
  assert(deduce_as__(&a, &ts, "b := a", "i32"));
  assert(deduce_as__(&a, &ts, "c := b", "i32"));
  Arena_free(&a);

  a = Arena_create(128);
  ts = (TypeStack){{}, 0, 0};
  Node *int_type_1 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"32", {0, 0}}), &rt);
  Node *int_type_2 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"32", {0, 0}}), &rt);
  assert(int_type_1 == int_type_2);
  Arena_free(&a);

  a = Arena_create(128);
  ts = (TypeStack){{}, 0, 0};
  Node *vec_type_1 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"[32]", {0, 0}}), &rt);
  Node *vec_type_2 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"[32]", {0, 0}}), &rt);
  assert(vec_type_1 == vec_type_2);
  Arena_free(&a);

  a = Arena_create(128);
  ts = (TypeStack){{}, 0, 0};
  vec_type_1 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"x := [[2]]", {0, 0}}), &rt);
  vec_type_2 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"d := [[3]]", {0, 0}}), &rt);
  assert(vec_type_1 == vec_type_2);
  Arena_free(&a);

  a = Arena_create(128);
  ts = (TypeStack){{}, 0, 0};
  Node *struct_type_1 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"a := {}", {0, 0}}), &rt);
  Node *struct_type_2 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"b := {}", {0, 0}}), &rt);
  assert(struct_type_1 == struct_type_2);
  Arena_free(&a);

  a = Arena_create(128);
  ts = (TypeStack){{}, 0, 0};
  struct_type_1 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"aa := {v=32}", {0, 0}}), &rt);
  struct_type_2 = gnq_deduce_types(&a, &ts, gnq_parse_statement(&a, &(State){"bb := { v=45 }", {0, 0}}), &rt);
  assert(struct_type_1 == struct_type_2);
  Arena_free(&a);
}

void gnq_deduce_struct_member() {
  printf("gnq_deduce_struct_member\n");

  Arena a = Arena_create(256);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "a := { b = 42 }", "({_} (b i32))"));
  assert(deduce_as__(&a, &ts, "x := { b = 4.2, z=true, a = a}", "({_} (a ({_} (b i32))) (z bool) (b f64))"));
  assert(deduce_as__(&a, &ts, "a", "({_} (b i32))"));
  assert(deduce_as__(&a, &ts, "a.b", "i32"));
  assert(deduce_as__(&a, &ts, "x.b", "f64"));
  assert(deduce_as__(&a, &ts, "x.z", "bool"));
  assert(deduce_as__(&a, &ts, "x.a", "({_} (b i32))"));
  assert(deduce_as__(&a, &ts, "x.a.b", "i32"));

  Node *st1 = gnq_car(a.structs);
  Node *st2 = gnq_car(gnq_cdr(a.structs));
  assert(gnq_equal(lisp_parse(&a, "({_} (b i32))"), st2));
  assert(gnq_equal(lisp_parse(&a, "({_} (a ({_} (b i32))) (z bool) (b f64))"), st1));
  assert(strcmp("s1", gnq_struct_c_name(&a, st1)) == 0);
  assert(strcmp("s2", gnq_struct_c_name(&a, st2)) == 0);
  Arena_free(&a);
}

void gnq_deduce_array_access() {
  printf("gnq_deduce_array_access\n");

  Arena a = Arena_create(256);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "a := [1, 2, 3]", "([_] i32)"));
  assert(deduce_as__(&a, &ts, "a", "([_] i32)"));
  assert(deduce_as__(&a, &ts, "a[0]", "i32"));

  assert(deduce_as__(&a, &ts, "b := [[1, 2, 3]]", "([_] ([_] i32))"));
  assert(deduce_as__(&a, &ts, "b", "([_] ([_] i32))"));
  assert(deduce_as__(&a, &ts, "b[0]", "([_] i32)"));
  assert(deduce_as__(&a, &ts, "b[0][1]", "i32"));

  Node *a1 = gnq_car(a.arrays);
  Node *a2 = gnq_car(gnq_cdr(a.arrays));
  assert(gnq_equal(lisp_parse(&a, "([_] ([_] i32))"), a1));
  assert(gnq_equal(lisp_parse(&a, "([_] i32)"), a2));
  assert(strcmp("a1", gnq_array_c_name(&a, a1)) == 0);
  assert(strcmp("a2", gnq_array_c_name(&a, a2)) == 0);
  Arena_free(&a);

  Arena_free(&a);
}

void gnq_deduce_function_calls() {
  printf("gnq_deduce_function_calls\n");

  Arena a = Arena_create(256);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "fn a() {}", "(fn () ({}))"));
  assert(deduce_as__(&a, &ts, "fn b() { return 42 }", "(fn () ({} (return 42)))"));
  assert(deduce_as__(&a, &ts, "a()", ""));
  assert(deduce_as__(&a, &ts, "b()", "i32"));
  Arena_free(&a);

  a = Arena_create(512);
  ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "fn fun1(x) {}", "(fn ((id x)) ({}))"));
  assert(deduce_as__(&a, &ts, "fn fun2(x) { return x }", "(fn ((id x)) ({} (return (id x))))"));
  assert(deduce_as__(&a, &ts, "fn fun3(x, y) { return x + y }", //
                     "(fn ((id x) (id y)) ({} (return (+ (id x) (id y)))))"));
  assert(deduce_as__(&a, &ts, "fun1(12)", ""));
  assert(deduce_as__(&a, &ts, "fun2(12)", "i32"));
  assert(deduce_as__(&a, &ts, "fun2(1.2)", "f64"));
  assert(deduce_as__(&a, &ts, "fun3(1, 2)", "i32"));
  assert(deduce_as__(&a, &ts, "fun3(true, false)", "bool"));
  assert(deduce_as__(&a, &ts, "fun2([12])", "([_] i32)"));
  Arena_free(&a);
}

void gnq_deduced_functions_are_listed() {
  printf("gnq_deduced_functions_are_listed\n");

  Arena a = Arena_create(512);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "fn fun1(a, b) { return a }", "(fn ((id a) (id b)) ({} (return (id a))))"));
  assert(deduce_as__(&a, &ts, "fn fun2(c) { return 2 }", "(fn ((id c)) ({} (return 2)))"));

  assert(gnq_is_nil(a.functions));
  assert(0 == gnq_list_len(a.functions));

  assert(deduce_as__(&a, &ts, "fun1(1, 2)", "i32"));
  assert(1 == gnq_list_len(a.functions));
  assert(NULL != gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&i32, &i32}, 2));
  assert(NULL == gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&i32, &f64}, 2));
  assert(&i32 == gnq_fn_find_return_type(gnq_car(a.functions), (Node *[]){&i32, &i32}, 2));
  assert(NULL == gnq_fn_find_return_type(gnq_car(a.functions), (Node *[]){&i32, &f64}, 2));

  assert(deduce_as__(&a, &ts, "fun1(3, 4)", "i32"));
  assert(1 == gnq_list_len(a.functions));
  assert(deduce_as__(&a, &ts, "fun1(3, 4.0)", "i32"));
  assert(1 == gnq_list_len(a.functions));
  assert(NULL != gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&i32, &f64}, 2));
  assert(&i32 == gnq_fn_find_return_type(gnq_car(a.functions), (Node *[]){&i32, &f64}, 2));

  assert(deduce_as__(&a, &ts, "fun2(5)", "i32"));
  assert(2 == gnq_list_len(a.functions));
  assert(NULL != gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&i32}, 1));
  assert(NULL == gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&f64}, 1));
  assert(deduce_as__(&a, &ts, "fun2(5.0)", "i32"));
  assert(2 == gnq_list_len(a.functions));
  assert(NULL != gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&i32}, 1));
  assert(NULL != gnq_fn_find_deduced(gnq_car(a.functions), (Node *[]){&f64}, 1));

  assert(deduce_as__(&a, &ts, "fun1(5, 6.0)", "i32"));
  assert(2 == gnq_list_len(a.functions));

  Node *fun2 = gnq_car(a.functions);
  Node *fun1 = gnq_car(gnq_cdr(a.functions));
  assert(strcmp("f11", gnq_fn_c_name(&a, fun2, (Node *[]){&f64}, 1)) == 0);
  assert(strcmp("f12", gnq_fn_c_name(&a, fun2, (Node *[]){&i32}, 1)) == 0);
  assert(strcmp("f21", gnq_fn_c_name(&a, fun1, (Node *[]){&i32, &f64}, 2)) == 0);
  assert(strcmp("f22", gnq_fn_c_name(&a, fun1, (Node *[]){&i32, &i32}, 2)) == 0);

  Arena_free(&a);
}

void gnq_deduced_functions_recursivly() {
  printf("gnq_deduced_functions_recursivly\n");

  Arena a = Arena_create(256);
  TypeStack ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "fn fun(a) { if (a==0) return 0 \n return fun(a-1) }", //
                     "(fn ((id a)) ({} (if (== (id a) 0) (return 0)) (return (call (id fun) ((- (id a) 1))))))"));
  assert(deduce_as__(&a, &ts, "fun(1)", "i32"));
  Arena_free(&a);

  a = Arena_create(256);
  ts = (TypeStack){{}, 0, 0};
  assert(deduce_as__(&a, &ts, "fn fun(a) { if (a>0) return fun(a-1) \n return 0 }", //
                     "(fn ((id a)) ({} (if (> (id a) 0) (return (call (id fun) ((- (id a) 1))))) (return 0)))"));
  assert(deduce_as__(&a, &ts, "fun(1)", "i32"));
  Arena_free(&a);

  // a = Arena_create(256);
  // ts = (TypeStack){{}, 0, 0};
  // assert(deduce_as__(&a, &ts, "fn fun(a) { if (a>0) return 1 + fun(a-1) \n return 0 }", //
  //                    "(fn ((id a)) ({} (if (> (id a) 0) (return (+ 1 (call (id fun) ((- (id a) 1)))))) (return
  //                    0)))"));
  // assert(deduce_as__(&a, &ts, "fun(1)", "i32"));
  // Arena_free(&a);
}

void gnq_eval_test() {
  printf("gnq_eval_test\n");

  Arena a = Arena_create(2048);

  Node *m = gnq_parse_all(&a, &(State){"fn main() { printf(\"hallo\") }", 1, 1});
  assert(m);

  char *args[] = {"xxx", "yyy", "zzz"};
  execute_c("void some_func(int, char*);"
            "void check_func(int a, char* b){"
            "  if (a<0) return; "
            "    some_func(a,b);"
            "  check_func(a-1,b); "
            "}"
            "int main(int argc, char**argv) { "
            "  for(int i=0; i<argc; ++i)"
            "    check_func(i, argv[i]);"
            "}",
            3, args);

  Arena_free(&a);
}

Node *gnq_parse_file(Arena *a, const char *filename) {

  FILE *fp = fopen(filename, "r");
  if (fp == NULL)
    return NULL;

  char buffer[1024 * 1024] = {0};
  fread(buffer, 1, sizeof(buffer), fp);
  fclose(fp);

  State st = (State){buffer, (Location){1, 1}};

  Node *stat = gnq_parse_all(a, &st);
  return gnq_list(a, 3, gnq_sym(a, "file"), gnq_string(a, filename), stat);
}

void gnq_test_files() {
  printf("gnq_test_files\n");
  DIR *d;
  struct dirent *dir;

#ifndef _WIN32
  d = opendir("tests");
  if (d) {
    while ((dir = readdir(d)) != NULL) {
      size_t l = strlen(dir->d_name);
      if (l < 4 || strcmp(&dir->d_name[l - 4], ".gnq") != 0)
        continue;

      char filename[256];
      snprintf(filename, sizeof(filename), "tests/%s", dir->d_name);
      printf(" %s...", filename);
      Arena a = Arena_create(2048);
      Node *ast = gnq_parse_file(&a, filename);
      // char buffer[4096];
      // lisp_str(buffer, sizeof(buffer), ast);
      // printf("%s\n", buffer);
      Arena_free(&a);
      printf("ok\n");
    }
    closedir(d);
  }
#endif
}

Node *gnq_mod_find(Node *mo, const char *id_name) {
  Node *sym = gnq_next(&mo);
  assert(sym == &SYM_MOD);
  while (!gnq_is_nil(mo)) {
    Node *assign = gnq_next(&mo);
    assert(gnq_is_call(assign, ":="));
    Node *id = gnq_car(gnq_cdr(assign));
    assert(gnq_is_call(id, "id"));
    if (strcmp(gnq_id_sym(id), id_name) == 0)
      return gnq_car(gnq_cdr(gnq_cdr(assign)));
  }
  return NULL;
}

size_t gnq_to_c_expression(Arena *a, Node *expr, char *b, size_t s) {
  size_t p = 0;

  if (gnq_type(expr) == NumberInt) {
    p += snprintf(b + p, s - p, SLD, gnq_toint(expr));
  } else if (gnq_type(expr) == NumberFloat) {
    p += snprintf(b + p, s - p, "%g", gnq_tofloat(expr));
  } else if (gnq_type(expr) == Bool) {
    p += snprintf(b + p, s - p, "%s", gnq_tobool(expr) ? "true" : "false");
  } else {
    for (size_t i = 0; i < sizeof(ops) / sizeof(ops[0]); ++i)
      if (gnq_is_call(expr, ops[i].op)) {
        gnq_next(&expr);
        p += gnq_to_c_expression(a, gnq_next(&expr), b + p, s - p);
        p += snprintf(b + p, s - p, "%s", ops[i].op);
        p += gnq_to_c_expression(a, gnq_next(&expr), b + p, s - p);
        return p;
      }

#define UNKNWON_C_EXPRESSION false
    assert(UNKNWON_C_EXPRESSION);
  }

  return p;
}

size_t gnq_to_c_statement(Arena *a, Node *stat, char *b, size_t s) {
  size_t p = 0;

  if (gnq_is_call(stat, "{}")) {
    gnq_next(&stat);
    p += snprintf(b + p, s - p, "{");
    while (!gnq_is_nil(stat))
      p += gnq_to_c_statement(a, gnq_next(&stat), b + p, s - p);
    p += snprintf(b + p, s - p, "}");
  } else if (gnq_is_call(stat, "return")) {
    gnq_next(&stat);
    p += snprintf(b + p, s - p, "return");
    if (!gnq_is_nil(stat)) {
      p += snprintf(b + p, s - p, " ");
      p += gnq_to_c_expression(a, gnq_next(&stat), b + p, s - p);
    }
    p += snprintf(b + p, s - p, ";");
  } else {
#define UNKNWON_C_STATEMENT false
    assert(UNKNWON_C_STATEMENT);
  }

  return p;
}

size_t gnq_to_c_fn(Arena *a, Node *fn, char *b, size_t s) {
  assert(gnq_is_call(fn, "fn"));

  Node *scope = gnq_car(gnq_cdr(gnq_cdr(fn)));
  Node *a_deduced = gnq_cdr(gnq_cdr(gnq_cdr(fn)));
  size_t p = 0;
  while (!gnq_is_nil(a_deduced)) {
    Node *fnd = gnq_next(&a_deduced);
    Node *rt = gnq_next(&fnd);
    assert(gnq_is_sym(rt));
    Node *param = fnd;
    const char *fn_name = gnq_fn_c_name_(a, fn, param);
    assert(fn_name && *fn_name);

    p += snprintf(b + p, s - p, "%s %s()", gnq_tosym(rt), fn_name);
    p += gnq_to_c_statement(a, scope, b + p, s - p);
  }
  return 0;
}

size_t gnq_to_c(Arena *a, char *b, size_t s) {
  Node *fns = a->functions;
  size_t p = 0;
  while (!gnq_is_nil(fns))
    p += gnq_to_c_fn(a, gnq_next(&fns), b + p, s - p);
  return p;
}

bool write_c_(Arena *a, const char *gnq, const char *c) {
  Node *mod = gnq_parse_mod(a, &(State){gnq, {0, 0}});
  Node *main = gnq_mod_find(mod, "main");
  assert(main && gnq_is_call(main, "fn"));

  TypeStack ts = (TypeStack){{}, 0, 0};
  TypeStack_push(&ts, "main", main);
  Node *dummy_main_call = gnq_parse_statement(a, &(State){"main()", {0, 0}});

  Node *return_type = &unparsed_return;
  Node *main_return_type = gnq_deduce_types(a, &ts, dummy_main_call, &return_type);
  assert(main_return_type == &i32);
  assert(!gnq_is_nil(a->functions));

  char code[256] = {0};
  gnq_to_c(a, code, sizeof(code));
  if (strcmp(code, c) == 0)
    return true;

  printf("expect '%s' got '%s'\n", c, code);
  return false;
}

void gnq_convert_to_c() {
  printf("gnq_convert_to_c\n");

  Arena a = Arena_create(256);
  assert(write_c_(&a, "fn main() {return 0}", "i32 f11(){return 0;}"));
  Arena_free(&a);

  a = Arena_create(256);
  assert(write_c_(&a, "fn main() {return 1+3*4}", "i32 f11(){return 1+3*4;}"));
  Arena_free(&a);
}

int main() {
  assert(sizeof(ptr_size) == sizeof(void *));

  gnq_test_files();

  arena_test();
  list_test();
  parser_atom_test();
  parser_list_test();
  parser_lisp_compare();
  parser_lisp_out();
  parser_gnq_expression_test();
  parser_gnq_statements_test();
  parser_gnq_functions_test();
  parser_gnq_construction_test();
  gnq_eval_test();
  gnq_deduce_types_test();
  gnq_deduce_types_advanced_test();
  gnq_deduce_struct_member();
  gnq_deduce_array_access();
  gnq_deduce_function_calls();
  gnq_deduced_functions_are_listed();
  gnq_deduced_functions_recursivly();

  gnq_convert_to_c();

  printf("ok\n");
  return 0;
}