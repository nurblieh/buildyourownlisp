#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>

#include "mpc.h"

/* lval type represents a value or an error. */
typedef struct lval {
  int type;
  long num;
  char* err;
  char *sym;
  /* Count and pointer to a list of lval* */
  int count;
  struct lval** cell;
} lval;

/* Enum for lval type. */
enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_SEXPR };

/* Create lval containing a number value. */
lval* lval_num(long x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;
  return v;
}

/* Create lval containing an error. */
lval* lval_err(char* msg) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  v->err = malloc(strlen(msg) + 1);
  strcpy(v->err, msg);
  return v;
}

/* Construct a point to a new Symbol lval. */
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

void lval_del(lval* v) {
  switch (v->type) {
    /* Do nothing! */
  case LVAL_NUM: break;
  case LVAL_ERR: free(v->err); break;
  case LVAL_SYM: free(v->sym); break;

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

lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  long x = strtol(t->contents, NULL, 10);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number");
}


lval* lval_add(lval* v, lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(v->cell) * v->count);
  v->cell[v->count - 1] = x;
  return v;
}

lval* lval_read(mpc_ast_t* t) {
  if (strstr(t->tag, "number")) { return lval_read_num(t); }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }

  /* If root or sexpr then create empty list. */
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); }
  if (strstr(t->tag, "sexpr"))  { x = lval_sexpr(); }

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
  case LVAL_SEXPR: lval_expr_print(v, '(', ')'); break;
  }
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

lval* builtin_op(lval* a, char* op) {
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

lval* lval_eval(lval* v);

lval* lval_eval_sexpr(lval* v) {
  /* Eval children. */
  for (int i = 0; i < v->count; i++) {
    v->cell[i] = lval_eval(v->cell[i]);
  }

  /* Error checking. */
  for (int i = 0; i < v->count; i++) {
    if (v->cell[i]->type == LVAL_ERR) { return lval_take(v, i); }
  }

  /* Empty expression. */
  if (v->count == 0) { return v; }

  /* Single expression. */
  if (v->count == 1) { return lval_take(v, 0); }

  /* Ensure first element is a symbol. */
  lval* f = lval_pop(v, 0);
  if (f->type != LVAL_SYM) {
    lval_del(f); lval_del(v);
    return lval_err("S-expression does not start with a symbol.");
  }

  /* Call builtin with operator. */
  lval* result = builtin_op(v, f->sym);
  lval_del(f);
  return result;
}

lval* lval_eval(lval* v) {
  /* Evaluate sexpressions. */
  if (v->type == LVAL_SEXPR) { return lval_eval_sexpr(v); }
  /* All others pass go. */
  return v;
}


/* Perform an operation, given a known operator. */
/* lval eval_op(lval x, char* op, lval y) { */
/*   if (x.type == LVAL_ERR) { return x; } */
/*   if (y.type == LVAL_ERR) { return y; } */
  
/*   if (strcmp(op, "+") == 0) { return lval_num(x.num + y.num); } */
/*   if (strcmp(op, "-") == 0) { return lval_num(x.num - y.num); } */
/*   if (strcmp(op, "*") == 0) { return lval_num(x.num * y.num); } */
/*   if (strcmp(op, "/") == 0) { */
/*     return y.num == 0 */
/*       ? lval_err(LERR_DIV_ZERO) */
/*       : lval_num(x.num / y.num); */
/*   } */
/*   if (strcmp(op, "^") == 0) { return lval_num(pow(x.num, y.num)); } */
/*   if (strcmp(op, "max") == 0) { */
/*     return lval_num(x.num > y.num ? x.num : y.num); } */
/*   if (strcmp(op, "min") == 0) { */
/*     return lval_num(x.num < y.num ? x.num : y.num); } */

/*   return lval_err(LERR_BAD_OP); */
/* } */


/* /\* Statement eval func; recursive. *\/ */
/* lval eval(mpc_ast_t* t) { */
/*   /\* If tagged as a number return it immediately. *\/ */
/*   if(strstr(t->tag, "number")) { */
/*     errno = 0; */
/*     long x = strtol(t->contents, NULL, 10); */
/*     return errno != ERANGE ? */
/*       lval_num(x) : */
/*       lval_err(LERR_BAD_NUM); */
/*   } */

/*   /\* The operator is always the second child. *\/ */
/*   char* op = t->children[1]->contents; */

/*   /\* Store the 3rd child... *\/ */
/*   lval x = eval(t->children[2]); */

/*   /\* Iterate across the remaining children. *\/ */
/*   int i = 3; */
/*   while (strstr(t->children[i]->tag, "expr")) { */
/*     x = eval_op(x, op, eval(t->children[i])); */
/*     i++; */
/*   } */

/*   return x; */
/* } */


/* Main func */
int main(int argc, char** argv) {
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr = mpc_new("sexpr");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
      "number : /-?[0-9]+/ ;                  \
       symbol : '+' | '-' | '*' | '/' | '^' ; \
       sexpr  : '(' <expr>* ')' ;             \
       expr : <number> | <symbol> | <sexpr> ; \
       lispy : /^/ <expr>* /$/ ;   \
      ",
            Number, Symbol, Sexpr, Expr, Lispy);
  
  /* Print version info and instructions. */
  puts("Lispy version 0.0.0.0.1 ");
  puts("Press ctrl-c to exit\n");

  while (1) {
    char* input = readline("lispy> ");
    add_history(input);
    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Lispy, &r)) {
      lval* x = lval_eval(lval_read(r.output));
      lval_println(x);
      lval_del(x);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    free(input);
  }
  mpc_cleanup(5, Number, Symbol, Sexpr, Expr, Lispy);
  return 0;
}
