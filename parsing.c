#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <editline/readline.h>

#include "mpc.h"

#define LASSERT(args, cond, fmt, ...) \
  if (!(cond)) { \
    lval* err = lval_err(fmt, ##__VA_ARGS__); \
    lval_del(args); return err; }

#define LASSERT_TYPE(func, args, index, expect) \
  LASSERT(args, args->cell[index]->type == expect, \
    "Function '%s' passed incorrect type for argument %i. Got %s, Expected %s.", \
    func, index, ltype_name(args->cell[index]->type), ltype_name(expect))

#define LASSERT_NUM(func, args, num) \
  LASSERT(args, args->count == num, \
    "Function '%s' passed incorrect number of arguments. Got %i, Expected %i.", \
    func, args->count, num)


/* Forward declarations. */

struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

/* Enum for lval type. */
enum { LVAL_ERR,
       LVAL_NUM, LVAL_SYM,
       LVAL_FUN,
       LVAL_SEXPR, LVAL_QEXPR };

typedef lval*(*lbuiltin)(lenv*, lval*);

/* lval type represents a value or an error. */
struct lval {
  int type;

  /* Basic types. */
  long num;
  char* err;
  char* sym;

  /* Functions. */
  lbuiltin builtin;
  lenv* env;
  lval* formals;
  lval* body;
    
  /* Expressions. */
  int count;
  lval** cell;
};

struct lenv {
  lenv* par;
  int count;
  char** syms;
  lval** vals;
};

lenv* lenv_new(void) {
  lenv* e = malloc(sizeof(lenv));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

void lval_del(lval* v);

void lenv_del(lenv* e) {
  for (int i = 0 ; i < e->count; i++) {
    free(e->syms[i]);
    lval_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

lval* lval_copy(lval* v);
lval* lval_err(char* fmt, ...);
lval* lenv_get(lenv* e, lval *k) {
  /* Iterate over the environment looking for key 'k'. */
  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->syms[i], k->sym) == 0) {
      return lval_copy(e->vals[i]);
    }
  }
  /* If symbol not found, return error. */
  if (e->par) {
    return lenv_get(e->par, k);
  } else {
    return lval_err("Unbound symbol '%s'.", k->sym);
  }
}

void lenv_put(lenv* e, lval* k, lval* v) {
  /* Check for pre-existing symbol name. */
  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->syms[i], k->sym) == 0) {
      lval_del(e->vals[i]);
      e->vals[i] = lval_copy(v);
      return;
    }
  }
  /* No pre-existing symbol found, create space for new one.  */
  e->count++;
  e->syms = realloc(e->syms, sizeof(char*) * e->count);
  e->vals = realloc(e->vals, sizeof(lval*) * e->count);

  e->syms[e->count-1] = malloc(strlen(k->sym)+1);
  strcpy(e->syms[e->count-1], k->sym);
  e->vals[e->count-1] = lval_copy(v);
}

void lenv_def(lenv* e, lval* k, lval* v) {
  /* Iterate until we get to the parent (global). */
  while (e->par) { e = e->par; }
  lenv_put(e, k, v);
}

lenv* lenv_copy(lenv* e) {
  lenv* n = malloc(sizeof(lenv));
  n->par = e->par;
  n->count = e->count;
  n->syms = malloc(sizeof(char*) * n->count);
  n->vals = malloc(sizeof(lval*) * n->count);
  for (int i = 0; i < n->count; i++) {
    n->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(n->syms[i], e->syms[i]);
    n->vals[i] = lval_copy(e->vals[i]);
  }
  return n;
}  

/* Create lval containg a function pointer. */
lval* lval_fun(lbuiltin func) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = func;
  return v;
}

lval* lval_lambda(lval* formals, lval* body) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;

  /* This is a user-defined function, not a built-in. */
  v->builtin = NULL;

  /* We'll need somewhere to store the values. */
  v->env = lenv_new();

  /* Function formals and body. */
  v->formals = formals;
  v->body = body;
  return v;
}

/* Create lval containing a number value. */
lval* lval_num(long x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;
  return v;
}

/* Create lval containing an error. */
lval* lval_err(char* fmt, ...) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;

  /* Create a va list and init it. */
  va_list va;
  va_start(va, fmt);

  v->err = malloc(512);

  vsnprintf(v->err, 511, fmt, va);

  v->err = realloc(v->err, strlen(v->err) + 1);

  va_end(va);
  
  return v;
}

/* Construct a pointer to a new Symbol lval. */
lval* lval_sym(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);
  return v;
}

/* Create a new empty sexpr lval. */
lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

/* Create a new empty qexpr lval. */
lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

void lval_del(lval* v) {
  switch (v->type) {
    /* Do nothing! */
  case LVAL_NUM: break;
  case LVAL_ERR: free(v->err); break;
  case LVAL_SYM: free(v->sym); break;
  case LVAL_FUN:
    if (!v->builtin) {
      free(v->env);
      free(v->formals);
      free(v->body);
    }
    break;

  case LVAL_QEXPR:
  case LVAL_SEXPR:
    for (int i = 0; i < v->count; i++ ){
      lval_del(v->cell[i]);
    }
    /* Also free the memory allocated to contain the pointers */
    free(v->cell);
    break;
  }

  free(v);
}

/* Try to intern a lval into an int; return as lval. */
lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  long x = strtol(t->contents, NULL, 10);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number: '%s'", t->contents);
}

/* Add the 2nd arg to the 1st's cells (children). */
lval* lval_add(lval* v, lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(v->cell) * v->count);
  v->cell[v->count - 1] = x;
  return v;
}

lval* lval_read(mpc_ast_t* t) {
  if (strstr(t->tag, "number")) { return lval_read_num(t); }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }

  /* If root or sexpr/qexpr then create empty list. */
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); }
  if (strstr(t->tag, "sexpr"))  { x = lval_sexpr(); }
  if (strstr(t->tag, "qexpr"))  { x = lval_qexpr(); }

  /* Fill the list with any valid expressions contained within. */
  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) { continue; }
    if (strcmp(t->children[i]->contents, ")") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "}") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "{") == 0) { continue; }
    if (strcmp(t->children[i]->tag,  "regex") == 0) { continue; }
    x = lval_add(x, lval_read(t->children[i]));
  }

  return x;
}

void lval_print(lval* v);

void lval_expr_print(lval* v, char open, char close) {
  putchar(open);
  for (int i = 0; i < v->count; i++) {
    /* Print value contained within. */
    lval_print(v->cell[i]);

    /* Don't print trailing space, if last element. */
    if (i != (v->count - 1)) {
      putchar(' ');
    }
  }
  putchar(close);
}
    

/* Print value or error from lval. */
void lval_print(lval* v) {
  switch (v->type) {
  case LVAL_NUM:   printf("%li", v->num); break;
  case LVAL_ERR:   printf("Error: %s", v->err); break;
  case LVAL_SYM:   printf("%s", v->sym); break;
  case LVAL_FUN:
    if (v->builtin) {
      printf("<builtin>");
    } else {
      printf("(\\ "); lval_print(v->formals);
      putchar(' '); lval_print(v->body); putchar(')');
    }
    break;
  case LVAL_SEXPR: lval_expr_print(v, '(', ')'); break;
  case LVAL_QEXPR: lval_expr_print(v, '{', '}'); break;
  }
}

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "Function";
    case LVAL_NUM: return "Number";
    case LVAL_ERR: return "Error";
    case LVAL_SYM: return "Symbol";
    case LVAL_SEXPR: return "S-Expression";
    case LVAL_QEXPR: return "Q-Expression";
    default: return "Unknown";
  }
}

lval* lval_copy(lval* v) {
  lval *x = malloc(sizeof(lval));
  x->type = v->type;

  switch(v->type) {
  case LVAL_FUN:
    if (v->builtin) {
      x->builtin = v->builtin;
    } else {
      x->builtin = NULL;
      x->env = lenv_copy(v->env);
      x->formals = lval_copy(v->formals);
      x->body = lval_copy(v->body);
    }
    break;
  case LVAL_NUM: x->num = v->num; break;
  case LVAL_ERR:
    x->err = malloc(strlen(v->err) + 1);
    strcpy(x->err, v->err);
    break;
  case LVAL_SYM:
    x->sym = malloc(strlen(v->sym) + 1);
    strcpy(x->sym, v->sym);
    break;
  case LVAL_SEXPR:
  case LVAL_QEXPR:
    /* Perform a deep copy of lvals which might contain other lvals. */
    x->count = v->count;
    x->cell = malloc(sizeof(lval*) * x->count);
    for (int i = 0; i < x->count; i++) {
      x->cell[i] = lval_copy(v->cell[i]);
    }
    break;
  }
  return x;
}

/* Print an "lval" followed by a newline */
void lval_println(lval* v) { lval_print(v); putchar('\n'); }

lval* lval_pop(lval* v, int i) {
  /* Find the item at i. */
  lval* x = v->cell[i];

  /* Shift the memory over. */
  memmove(&v->cell[i], &v->cell[i+1], sizeof(lval*) * (v->count - i - 1));

  v->count--;

  /* Fixup the amount of allocated memory. */
  v->cell = realloc(v->cell, sizeof(lval) * v->count);
  return x;
}

lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);
  return x;
}

lval* builtin_var(lenv* e, lval* a, char* func) {
  LASSERT_TYPE(func, a, 0, LVAL_QEXPR);
  
  lval* syms = a->cell[0];
  for (int i = 0; i < syms->count; i++) {
    LASSERT(a, (syms->cell[i]->type == LVAL_SYM),
            "Function '%s' cannot define non-symbol. "
            "Got: %s; expected: %s", func,
            ltype_name(syms->cell[i]->type),
            ltype_name(LVAL_SYM));
  }

  /* Check correct number of symbols and values */
  LASSERT(a, (syms->count == a->count-1),
          "Function '%s' passed too many arguments for symbols "
          "Got %i; expected: %d",
          func, syms->count, a->count - 1);

  for (int i = 0; i < syms->count; i++) {
    if (strcmp(func, "def") == 0) {
      lenv_def(e, syms->cell[i], a->cell[i+1]);
    }
    if (strcmp(func, "=") == 0) {
      lenv_put(e, syms->cell[i], a->cell[i+1]);
    }
  }

  lval_del(a);
  return lval_sexpr();
}

lval* builtin_def(lenv* e, lval* a) {
  return builtin_var(e, a, "def");
}

lval* builtin_put(lenv* e, lval* a) {
  return builtin_var(e, a, "=");
}

lval* builtin_head(lenv* e, lval* a) {
  LASSERT(a, a->count == 1,
          "Function 'head' passed too many args!");
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
          "Function 'head' passed incorrect type!");
  LASSERT(a, a->cell[0]->count != 0,
          "Function 'head' passed {}!");

  lval* v = lval_take(a, 0);
  while (v->count > 1) { lval_del(lval_pop(v, 1)); }
  return v;
}

lval* builtin_tail(lenv* e, lval* a) {
  LASSERT(a, a->count == 1,
          "Function 'head' passed too many args!");
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
          "Function 'head' passed incorrect type!");
  LASSERT(a, a->cell[0]->count != 0,
          "Function 'head' passed {}!");

  lval* v = lval_take(a, 0);
  lval_del(lval_pop(v, 0));
  return v;
}

lval* builtin_list(lenv* e, lval* a) {
  a->type = LVAL_QEXPR;
  return a;
}

lval* lval_eval(lenv* e, lval* a);

lval* builtin_eval(lenv* e, lval* a) {
  LASSERT(a, a->count == 1,
          "Function 'eval' passed too many args!");
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
          "Function 'eval' passed incorrect type!");

  lval* x = lval_take(a, 0);
  x->type = LVAL_SEXPR;
  return lval_eval(e, x);
}

lval* lval_join(lval* x, lval* y);

lval* builtin_join(lenv* e, lval* a) {
  for (int i = 0; i < a->count; i++) {
    LASSERT(a, a->cell[i]->type == LVAL_QEXPR,
            "Function 'join' passed incorrect type!");
  }

  lval* x = lval_pop(a, 0);

  while (a->count) {
    x = lval_join(x, lval_pop(a, 0));
  }

  lval_del(a);
  return x;
}

lval* builtin_ord(lenv* e, lval* a, char* op) {
  LASSERT_NUM(op, a, 2);
  LASSERT_TYPE(op, a, 0, LVAL_NUM);
  LASSERT_TYPE(op, a, 1, LVAL_NUM);

  int r;
  if (strcmp(op, ">") == 0) {
    r = a->cell[0]->num > a->cell[1]->num;
  }
  if (strcmp(op, "<") == 0) {
    r = a->cell[0]->num < a->cell[1]->num;
  }
  if (strcmp(op, ">=") == 0) {
    r = a->cell[0]->num >= a->cell[1]->num;
  }
  if (strcmp(op, "<=") == 0) {
    r = a->cell[0]->num <= a->cell[1]->num;
  }
  lval_del(a);
  return lval_num(r);
}

lval* builtin_gt(lenv* e, lval* a) {
  return builtin_ord(e, a, ">");
}

lval* builtin_lt(lenv* e, lval* a) {
  return builtin_ord(e, a, "<");
}

lval* builtin_gte(lenv* e, lval* a) {
  return builtin_ord(e, a, ">=");
}

lval* builtin_lte(lenv* e, lval* a) {
  return builtin_ord(e, a, "<=");
}

/* Verify all aspects of two lvals are equal. */
int lval_eq(lval* x, lval* y) {
  if (x->type != y->type) { return false; }

  /* Compare based on type. */

  switch (x->type) {
  case LVAL_NUM:
    return (x->num == y->num);
  case LVAL_ERR:
    return strcmp(x->err, y->err);
  case LVAL_SYM:
    return strcmp(x->sym, y->sym);
  case LVAL_FUN:
    if (x->builtin || y->builtin) {
      return x->builtin == y->builtin;
    } else {
      return lval_eq(x->formals, y->formals) &&
        lval_eq(x->body, y->body);
    }

  case LVAL_QEXPR:
  case LVAL_SEXPR:
    if (x->count != y->count) { return false; }
    for (int i = 0; i < x->count; i++) {
      if (!lval_eq(x->cell[i], y->cell[i])) { return false; }
    }
    return true;
    break;
  }
  return false;
}

lval* builtin_cmp(lenv* e, lval* a, char* op) {
  LASSERT_NUM(op, a, 2);
  
  int r;
  if (strcmp(op, "==") == 0) {
    r = lval_eq(a->cell[0], a->cell[1]);
  }
  if (strcmp(op, "!=") == 0) {
    r = !lval_eq(a->cell[0], a->cell[1]);
  }
  lval_del(a);
  return lval_num(r);
}

lval* builtin_eq(lenv* e, lval* a) {
  return builtin_cmp(e, a, "==");
}

lval* builtin_ne(lenv* e, lval* a) {
  return builtin_cmp(e, a, "!=");
}

lval* builtin_if(lenv* e, lval* a) {
  LASSERT_NUM("if", a, 3);
  LASSERT_TYPE("if", a, 0, LVAL_NUM);
  LASSERT_TYPE("if", a, 1, LVAL_QEXPR);
  LASSERT_TYPE("if", a, 2, LVAL_QEXPR);

  lval* x;
  a->cell[1]->type = LVAL_SEXPR;
  a->cell[2]->type = LVAL_SEXPR;
  
  if (a->cell[0]->num) {
    /* If condition is true evaluate first expression */
    x = lval_eval(e, lval_pop(a, 1));
  } else {
    /* Otherwise evaluate second expression */
    x = lval_eval(e, lval_pop(a, 2));
  }
  
  /* Delete argument list and return */
  lval_del(a);
  return x;
}

lval* builtin_op(lenv* e, lval* a, char* op) {
  /* Ensure all args are numbers. */
  for (int i = 0; i < a->count; i++) {
    if (a->cell[i]->type != LVAL_NUM) {
      lval_del(a);
      return lval_err("Cannot operate on non-number.");
    }
  }

  lval* x = lval_pop(a, 0);

  /* If no arguments and sub then perform unary negation. */
  if ((strcmp(op, "-") == 0) && a->count == 0) {
    x->num = -x->num;
  }

  while (a->count > 0) {
    lval* y = lval_pop(a, 0);

    if (strcmp(op, "+") == 0) { x->num += y->num; }
    if (strcmp(op, "-") == 0) { x->num -= y->num; }
    if (strcmp(op, "*") == 0) { x->num *= y->num; }
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        lval_del(x); lval_del(y);
        x = lval_err("Div by zero!"); break;
      }
      x->num /= y->num;
    }

    lval_del(y);
  }
  lval_del(a); return x;
}

lval* builtin_add(lenv* e, lval* a) {
  return builtin_op(e, a, "+");
}

lval* builtin_sub(lenv* e, lval* a) {
  return builtin_op(e, a, "-");
}

lval* builtin_mul(lenv* e, lval* a) {
  return builtin_op(e, a, "*");
}

lval* builtin_div(lenv* e, lval* a) {
  return builtin_op(e, a, "/");
}

lval* builtin_lambda(lenv* e, lval* a) {
  /* Check args. */
  LASSERT_NUM("\\", a, 2);
  LASSERT_TYPE("\\", a, 0, LVAL_QEXPR);
  LASSERT_TYPE("\\", a, 1, LVAL_QEXPR);

  /* Check first qexpr contains only symbols. */
  for (int i = 0; i < a->cell[0]->count; i++) {
    LASSERT(a, (a->cell[0]->cell[i]->type == LVAL_SYM),
            "Can't define non-symbol. Got %s; expected: %s",
            ltype_name(a->cell[0]->cell[i]->type),ltype_name(LVAL_SYM));
  }

  lval* formals = lval_pop(a, 0);
  lval* body = lval_pop(a, 0);
  lval_del(a);

  return lval_lambda(formals, body);
}

void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name);
  lval* v = lval_fun(func);

  lenv_put(e, k, v);
  lval_del(k);
  lval_del(v);
}

void lenv_add_builtins(lenv* e) {
  /* List Functions. */
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "head", builtin_head);
  lenv_add_builtin(e, "tail", builtin_tail);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "join", builtin_join);
  lenv_add_builtin(e, "def",  builtin_def);
  lenv_add_builtin(e, "=",    builtin_put);
  lenv_add_builtin(e, "\\",   builtin_lambda);

  /* Mathematical Functions. */
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);

  /* Ordering Functions. */
  lenv_add_builtin(e, ">",  builtin_gt);
  lenv_add_builtin(e, "<",  builtin_lt);
  lenv_add_builtin(e, ">=", builtin_gte);
  lenv_add_builtin(e, "<=", builtin_lte);

  /* Comparators. */
  lenv_add_builtin(e, "==", builtin_eq);
  lenv_add_builtin(e, "!=", builtin_ne);

  /* If. */
  lenv_add_builtin(e, "if", builtin_if);
}


lval* lval_join(lval* x, lval* y) {

  while (y->count) {
    x = lval_add(x, lval_pop(y, 0));
  }

  /* Delete empty 'y' and return 'x'. */
  lval_del(y);
  return x;
}

lval* builtin_list(lenv* e, lval* a);

/* Call a defined function. Builtin or user-defined. */
lval* lval_call(lenv* e, lval* f, lval* a) {
  /* If this is a builtin, just call it. */
  if (f->builtin) { return f->builtin(e, a); }

  /* Record argument counts. */
  int given = a->count;
  int total = f->formals->count;

  /* Iterate over the given arguments. May be < than formal count. */
  while (a->count) {
    /* Test if we've run out of formals to bind. */
    if (f->formals->count == 0) {
      lval_del(a);
      return lval_err("Function passed too many arguments. "
                      "Got %d; expected %d", given, total);
    }

    lval* sym = lval_pop(f->formals, 0);
    if (strcmp(sym->sym, "&") == 0) {
      /* Ensure '&' is followed by another symbol. */
      if (f->formals->count != 1) {
        lval_del(a);
        return lval_err("Function format invalid "
                        "Symbol '&' not followed "
                        "by a single symbol.");
      }

      /* Next formal should be bound to remaining arguments. */
      lval* nsym = lval_pop(f->formals, 0);
      lenv_put(f->env, nsym, builtin_list(e, a));
      lval_del(sym); lval_del(nsym);
      break;
    }
    
    lval* val = lval_pop(a, 0);

    lenv_put(f->env, sym, val);

    lval_del(sym); lval_del(val);
  }

  /* argument list should be empty at this point. */
  lval_del(a);

  /* Check if the user didn't give us any values for the vararg. */
  if(f->formals->count > 0 &&
     strcmp(f->formals->cell[0]->sym, "&") == 0) {

    if (f->formals->count != 2) {
      return lval_err("Function format invalid. "
                      "Symbol '&' not followed by single symbol.");
    }

    /* We don't need the '&'. */
    lval_del(lval_pop(f->formals, 0));

    /* Pop the last formal and bind an empty list to it. */
    lval* sym = lval_pop(f->formals, 0);
    lval* val = lval_qexpr();

    lenv_put(f->env, sym, val);
    lval_del(sym); lval_del(val);
  }

  /* If the formals are consumed, evaluate the function. */
  if (f->formals->count == 0) {
    f->env->par = e;

    return builtin_eval(f->env,
                        lval_add(lval_sexpr(),
                                 lval_copy(f->body)));
  } else {
    /* Return a partially evaluated function. A "partial". */
    return lval_copy(f);
  }
}


lval* lval_eval(lenv* e, lval* v);

lval* lval_eval_sexpr(lenv* e, lval* v) {
  /* Eval children. */
  for (int i = 0; i < v->count; i++) {
    v->cell[i] = lval_eval(e, v->cell[i]);
  }

  /* Error checking. */
  for (int i = 0; i < v->count; i++) {
    if (v->cell[i]->type == LVAL_ERR) { return lval_take(v, i); }
  }

  /* Empty expression. */
  if (v->count == 0) { return v; }

  /* Single expression. */
  if (v->count == 1) { return lval_eval(e, lval_take(v, 0)); }

  /* Ensure first element is a symbol. */
  lval* f = lval_pop(v, 0);
  if (f->type != LVAL_FUN) {
    lval* err = lval_err("First element of S-Expression is not a function."
                         "Got %s; expected %s.",
                         ltype_name(f->type), ltype_name(LVAL_FUN));
    lval_del(f); lval_del(v);
    return err;
  }

  /* Call function to get a result. */
  lval* result = lval_call(e, f, v);
  lval_del(f);
  return result;
}

lval* lval_eval(lenv *e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval* x = lenv_get(e, v);
    lval_del(v);
    return x;
  }
  /* Evaluate sexpressions. */
  if (v->type == LVAL_SEXPR) { return lval_eval_sexpr(e, v); }
  /* All others pass go. */
  return v;
}


/* Main func */
int main(int argc, char** argv) {
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr = mpc_new("sexpr");
  mpc_parser_t* Qexpr = mpc_new("qexpr");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
      "number : /-?[0-9]+/ ;                  \
       symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;         \
       sexpr  : '(' <expr>* ')' ;             \
       qexpr  : '{' <expr>* '}' ;             \
       expr   : <number> | <symbol> | <sexpr> | <qexpr> ; \
       lispy  : /^/ <expr>* /$/ ;   \
      ",
            Number, Symbol, Sexpr, Qexpr, Expr, Lispy);
  
  /* Print version info and instructions. */
  puts("Lispy version 0.0.0.0.1 ");
  puts("Press ctrl-c to exit\n");

  lenv* e = lenv_new();
  lenv_add_builtins(e);

  while (1) {
    char* input = readline("lispy> ");
    add_history(input);
    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Lispy, &r)) {
      lval* x = lval_eval(e, lval_read(r.output));
      lval_println(x);
      lval_del(x);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    free(input);
  }
  
  lenv_del(e);
  
  mpc_cleanup(5, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);
  return 0;
}
