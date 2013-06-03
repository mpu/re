#include <assert.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void die(char *reason);

enum {
	Range,
	Jump,
	Goto,
	Accept,
};

typedef struct Op Op;
struct Op {
	union {
		unsigned int rstart;
		int jmp;
	};
	unsigned short rlen;
	short ty;
};

typedef struct Re Re;
struct Re {
	Op *nfa;
	size_t len, size;
};

typedef struct MatchState MatchState;
struct MatchState {
	unsigned char *s, *n;
	size_t pos;
	enum {
		Active,
		Match,
		/* Fail, */
	} state;
};

char *errs;


/* compiling */

static void
pushop(Re *re, short ty, ...)
{
	va_list ap;
	Op *op;

	if (re->len >= re->size) {
		re->size *= 2;
		if (re->size == 0)
			re->size = 10;
		re->nfa = realloc(re->nfa, re->size * sizeof(Op));
		if (!re->nfa)
			die("(re.c) out of memory");
	}

	op = &re->nfa[re->len++];
	op->ty = ty;

	va_start(ap, ty);
	switch (ty) {
	case Range:
		op->rstart = va_arg(ap, unsigned int);
		op->rlen = va_arg(ap, int);
		break;
	case Jump:
	case Goto:
		op->jmp = va_arg(ap, int);
		break;
	}
	va_end(ap);
}

/* Features we support:
 * - \
 * - .
 * - [x-y]
 * - [^x-y]       (not yet)
 * - |
 * - ( )
 * - *
 * - +
 * - ?
 */
static Re *pre;
static jmp_buf pboom;
static char *errloc;

static void
parse(char **ps)
{
	void parseor(char **ps); /* forward */
	int c, beg, end;
	size_t op;
	char *s;

	s = *ps;

	for (c=*s; c && c != '|' && c != ')'; c=*++s)
		switch (c) {

		case '(':
			op = pre->len;
			*ps = s+1;
			parseor(ps);
			s = *ps;
			if (*s != ')') {
				errloc = s;
				errs = "expected )";
				longjmp(pboom, 1);
			}
			break;

		case '[':
			op = pre->len;
			s++;
			if ((beg = *s++) == 0
			|| *s++ != '-'
			|| (end = *s++) == 0
			|| *s != ']') {
				errloc = s-1;
				errs = "ill formed range";
				longjmp(pboom, 1);
			}
			pushop(pre, Range, beg, end-beg+1);
			break;

		case '.':
			op = pre->len;
			pushop(pre, Range, 0, 0xffff);
			break;

		case '+':
		case '*':
			pushop(pre, Jump, op-pre->len);
			if (c == '+')
				break;
			/* fallback */

		case '?':
			pushop(pre, Accept); /* dummy push */
			memmove(&pre->nfa[op+1], &pre->nfa[op],
				(pre->len-1-op) * sizeof(Op));
			pre->nfa[op].ty = Jump;
			pre->nfa[op].jmp = pre->len-op;
			break;

		case '\\':
			c = *++s;
			/* fallback */

		default:
			op = pre->len;
			pushop(pre, Range, c, 1);
			break;

		}

	*ps = s;
}

static void
parseor(char **ps)
{
	Op *opjmp;
	size_t j, g;

	j = pre->len;
	g = 0;
	parse(ps);

	while (**ps && **ps != ')') {
		assert(**ps == '|');
		++*ps;

		pushop(pre, Accept); /* dummy push */
		opjmp = &pre->nfa[j];
		memmove(opjmp+1, opjmp, (pre->len-1-j) * sizeof(Op));
		opjmp->ty = Jump;
		opjmp->jmp = pre->len-j+1;
		g = pre->len;
		pushop(pre, Goto, 0);

		parse(ps);

		pre->nfa[g].jmp = pre->len-g;
	}
}

int
recompile(Re *re, char *str)
{
	char *s;
	static char errmsg[512];

	s = str;
	re->nfa = 0;
	re->len = 0;
	re->size = 0;

	if (setjmp(pboom)) {
		sprintf(errmsg, "%s at character %td", errs, errloc-s);
		errs = errmsg;
		free(re->nfa);
		return 0;
	}

	pre = re;
	parseor(&str);
	if (*str != 0) {
		errloc = str;
		errs = "spurious character";
		longjmp(pboom, 1);
	}
	pushop(re, Accept);
	return 1;
}

void
refree(Re *re)
{
	free(re->nfa);
	re->nfa = 0;
}


/* matching */

static int
step(unsigned char *n, Re *re, size_t i)
{
	int acc;

	switch (re->nfa[i].ty) {

	case Range:
		n[i/8] |= 1 << i%8;
		acc = 0;
		break;

	case Accept:
		acc = 1;
		break;

	case Goto:
	case Jump:
		acc = step(n, re, i+re->nfa[i].jmp);
		if (re->nfa[i].ty == Jump)
			acc |= step(n, re, i+1);
		break;

	}

	return acc;
}

void
rebegin(MatchState *m, Re *re)
{
	m->s = calloc((re->len+7) / 8, 1);
	m->n = calloc((re->len+7) / 8, 1);
	if (!m->s || !m->n)
		die("(re.c) out of memory");
	m->pos = 0;
	if (step(m->s, re, 0))
		m->state = Match;
	else
		m->state = Active;
}

void
reend(MatchState *m)
{
	free(m->s);
	free(m->n);
	m->s = m->n = 0;
}

void
refeed(MatchState *m, Re *re, char *str)
{
	unsigned char mask, *st, *t;
	int c;
	size_t i;
	Op *op;

	if (m->state != Active)
		return;

	for (; (c=*str); str++) {
		m->pos++;
		op = re->nfa;
		st = m->s;
		mask = 1;
		for (i=0; i<re->len; i++) {

			if (*st & mask) {
				assert(op->ty == Range);
				if (c >= op->rstart)
				if (c < op->rstart+op->rlen)
				if (step(m->n, re, i+1)) {
					m->state = Match;
					return;
				}
			}

			mask *= 2;
			if ((mask & 0xff) == 0) {
				mask = 1;
				st++;
			}
			op++;
		}
		t = m->s; /* swap next and current state */
		m->s = m->n;
		m->n = t;
		memset(t, 0, (re->len+7)/8);
	}
}


/* test */

void
die(char *reason)
{
	fprintf(stderr, "dying, %s\n", reason);
	exit(1);
}

void
repp(FILE *f, Re *re)
{
	size_t i;

	for (i=0; i<re->len; i++)
		switch (re->nfa[i].ty) {
		case Accept:
			fprintf(f, "%02zd: Accept\n", i);
			break;
		case Jump:
			fprintf(f, "%02zd: Jump %d\n", i,
				re->nfa[i].jmp);
			break;
		case Goto:
			fprintf(f, "%02zd: Goto %d\n", i,
				re->nfa[i].jmp);
			break;
		case Range:
			fprintf(f, "%02zd: Range %u %hu\n", i,
				re->nfa[i].rstart, re->nfa[i].rlen);
			break;
		}
}

int
main(int ac, char *av[])
{
	char line[8196];
	MatchState ms;
	Re re;

	if (ac<2)
		return 1;

	if (!recompile(&re, av[1])) {
		printf("regexp compilation error: %s\n", errs);
		return 1;
	}
	repp(stdout, &re);

	while (fgets(line, 8196, stdin)) {
		rebegin(&ms, &re);
		refeed(&ms, &re, line);
		if (ms.state == Match) {
			size_t s;

			for (s=0; s<ms.pos; s++)
				putchar(' ');
			printf("^ end of match\n");
		}
		reend(&ms);
	}

	refree(&re);
	return 0;
}

/* Copyright (c) 2013, Quentin Carbonneaux
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */
