#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>

#include "mpc.h"

/* lval type represents a value or an error. */
typedef struct {
  int type;
  long num;
  int err;
} lval;

/* Enum for lval type. */
enum { LVAL_NUM, LVAL_ERR };

/* Create Enumeration of Possible Error Types */
enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

/* Create lval containing a number value. */
lval lval_num(long x) {
  lval v;
  v.type = LVAL_NUM;
  v.num = x;
  return v;
}

/* Create lval containing an error. */
lval lval_err(int x) {
  lval v;
  v.type = LVAL_ERR;
  v.err = x;
  return v;
}

/* Print value or error from lval. */
void lval_print(lval v) {
  switch (v.type) {
  case LVAL_NUM:
    printf("%li", v.num);
    break;
  case LVAL_ERR:
    if (v.err == LERR_DIV_ZERO) {
      printf("Error: Division by zero.");
    }
    else if (v.err == LERR_BAD_OP) {
      printf("Error: Invalid operator.");
    }
    else if (v.err == LERR_BAD_NUM) {
      printf("Error: Bad number.");
    }
    break;
  }
}

/* Print an "lval" followed by a newline */
void lval_println(lval v) { lval_print(v); putchar('\n'); }


/* Perform an operation, given a known operator. */
lval eval_op(lval x, char* op, lval y) {
  if (x.type == LVAL_ERR) { return x; }
  if (y.type == LVAL_ERR) { return y; }
  
  if (strcmp(op, "+") == 0) { return lval_num(x.num + y.num); }
  if (strcmp(op, "-") == 0) { return lval_num(x.num - y.num); }
  if (strcmp(op, "*") == 0) { return lval_num(x.num * y.num); }
  if (strcmp(op, "/") == 0) {
    return y.num == 0
      ? lval_err(LERR_DIV_ZERO)
      : lval_num(x.num / y.num);
  }
  if (strcmp(op, "^") == 0) { return lval_num(pow(x.num, y.num)); }
  if (strcmp(op, "max") == 0) {
    return lval_num(x.num > y.num ? x.num : y.num); }
  if (strcmp(op, "min") == 0) {
    return lval_num(x.num < y.num ? x.num : y.num); }

  return lval_err(LERR_BAD_OP);
}


/* Statement eval func; recursive. */
lval eval(mpc_ast_t* t) {
  /* If tagged as a number return it immediately. */
  if(strstr(t->tag, "number")) {
    errno = 0;
    long x = strtol(t->contents, NULL, 10);
    return errno != ERANGE ?
      lval_num(x) :
      lval_err(LERR_BAD_NUM);
  }

  /* The operator is always the second child. */
  char* op = t->children[1]->contents;

  /* Store the 3rd child... */
  lval x = eval(t->children[2]);

  /* Iterate across the remaining children. */
  int i = 3;
  while (strstr(t->children[i]->tag, "expr")) {
    x = eval_op(x, op, eval(t->children[i]));
    i++;
  }

  return x;
}


/* Main func */
int main(int argc, char** argv) {
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Operator = mpc_new("operator");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            "number : /-?[0-9]+/ ;                         \
             operator : '+' | '-' | '*' | '/' | '^' | /(max|min)/ ; \
             expr : <number> | '(' <operator> <expr>+ ')'; \
             lispy : /^/ <operator> <expr>+ /$/ ;          \
            ",
            Number, Operator, Expr, Lispy);
  
  /* Print version info and instructions. */
  puts("Lispy version 0.0.0.0.1 ");
  puts("Press ctrl-c to exit\n");

  while (1) {
    char* input = readline("lispy> ");
    add_history(input);
    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Lispy, &r)) {
      /* mpc_ast_print(r.output); */
      lval result = eval(r.output);
      lval_println(result);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    free(input);
  }
  mpc_cleanup(4, Number, Operator, Expr, Lispy);
  return 0;
}
