#include "hw7.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

bst_sf* insert_bst_sf(matrix_sf *mat, bst_sf *root)
{
    if (root == NULL)
    {
        bst_sf *node = malloc(sizeof(bst_sf));
        if (node == NULL)
        {
            return NULL;
        }
        node->mat = mat;
        node->left_child = NULL;
        node->right_child = NULL;
        return node;
    }
    if (mat->name < root->mat->name)
    {
        root->left_child = insert_bst_sf(mat, root->left_child);
    }
    else if (mat->name > root->mat->name)
    {
        root->right_child = insert_bst_sf(mat, root->right_child);
    }
    return root;
}

matrix_sf* find_bst_sf(char name, bst_sf *root)
{
    if (root == NULL)
    {
        return NULL;
    }
    if (name == root->mat->name)
    {
        return root->mat;
    }
    if (name < root->mat->name)
    {
        return find_bst_sf(name, root->left_child);
    }
    return find_bst_sf(name, root->right_child);
}

static void free_bst_except_helper(bst_sf *root, matrix_sf *keep)
{
    if (root == NULL)
    {
        return;
    }
    free_bst_except_helper(root->left_child, keep);
    free_bst_except_helper(root->right_child, keep);
    if (root->mat != keep)
    {
        free(root->mat);
    }
    free(root);
}

void free_bst_sf(bst_sf *root)
{
    if (root == NULL)
    {
        return;
    }
    free_bst_except_helper(root, NULL);
}

matrix_sf* add_mats_sf(const matrix_sf *mat1, const matrix_sf *mat2)
{
    if (mat1 == NULL || mat2 == NULL)
    {
        return NULL;
    }
    if (mat1->num_rows != mat2->num_rows || mat1->num_cols != mat2->num_cols)
    {
        return NULL;
    }
    unsigned int rows = mat1->num_rows;
    unsigned int cols = mat1->num_cols;
    matrix_sf *res = malloc(sizeof(matrix_sf) + rows * cols * sizeof(int));
    if (res == NULL)
    {
        return NULL;
    }
    res->name = 0;
    res->num_rows = rows;
    res->num_cols = cols;
    for (unsigned int i = 0; i < rows * cols; i++)
    {
        res->values[i] = mat1->values[i] + mat2->values[i];
    }
    return res;
}

matrix_sf* mult_mats_sf(const matrix_sf *mat1, const matrix_sf *mat2)
{
    if (mat1 == NULL || mat2 == NULL)
    {
        return NULL;
    }
    if (mat1->num_cols != mat2->num_rows)
    {
        return NULL;
    }
    unsigned int r = mat1->num_rows;
    unsigned int c = mat2->num_cols;
    unsigned int common = mat1->num_cols;
    matrix_sf *res = malloc(sizeof(matrix_sf) + r * c * sizeof(int));
    if (res == NULL)
    {
        return NULL;
    }
    res->name = 0;
    res->num_rows = r;
    res->num_cols = c;
    for (unsigned int i = 0; i < r; i++)
    {
        for (unsigned int j = 0; j < c; j++)
        {
            int sum = 0;
            for (unsigned int k = 0; k < common; k++)
            {
                sum += mat1->values[i * common + k] * mat2->values[k * c + j];
            }
            res->values[i * c + j] = sum;
        }
    }
    return res;
}

matrix_sf* transpose_mat_sf(const matrix_sf *mat)
{
    if (mat == NULL)
    {
        return NULL;
    }
    unsigned int old_r = mat->num_rows;
    unsigned int old_c = mat->num_cols;
    unsigned int new_r = old_c;
    unsigned int new_c = old_r;
    matrix_sf *res = malloc(sizeof(matrix_sf) + new_r * new_c * sizeof(int));
    if (res == NULL)
    {
        return NULL;
    }
    res->name = 0;
    res->num_rows = new_r;
    res->num_cols = new_c;
    for (unsigned int i = 0; i < old_r; i++)
    {
        for (unsigned int j = 0; j < old_c; j++)
        {
            res->values[j * new_c + i] = mat->values[i * old_c + j];
        }
    }
    return res;
}

matrix_sf* create_matrix_sf(char name, const char *expr)
{
    if (expr == NULL)
    {
        return NULL;
    }
    const char *p = expr;
    while (*p && isspace((unsigned char)*p))
    {
        p++;
    }
    unsigned int num_rows = 0;
    unsigned int num_cols = 0;
    if (sscanf(p, "%u %u", &num_rows, &num_cols) != 2)
    {
        return NULL;
    }
    const char *br = strchr(p, '[');
    if (br == NULL)
    {
        return NULL;
    }
    p = br + 1;
    unsigned int total = num_rows * num_cols;
    matrix_sf *mat = malloc(sizeof(matrix_sf) + (total ? total * sizeof(int) : 0));
    if (mat == NULL)
    {
        return NULL;
    }
    mat->name = name;
    mat->num_rows = num_rows;
    mat->num_cols = num_cols;
    unsigned int count = 0;
    char *endptr = NULL;
    while (*p && count < total)
    {
        while (*p && (isspace((unsigned char)*p) || *p == ';'))
        {
            p++;
        }
        if (*p == ']' || *p == '\0')
        {
            break;
        }
        long v = strtol(p, &endptr, 10);
        if (endptr == p)
        {
            p++;
            continue;
        }
        mat->values[count++] = (int)v;
        p = endptr;
    }
    while (*p && isspace((unsigned char)*p))
    {
        p++;
    }
    if (count != total)
    {
        free(mat);
        return NULL;
    }
    while (*p && *p != ']')
    {
        p++;
    }
    if (*p != ']')
    {
        free(mat);
        return NULL;
    }
    return mat;
}

static int is_op_char(char c)
{
    return c == '+' || c == '*';
}

char* infix2postfix_sf(char *infix)
{
    if (infix == NULL)
    {
        return NULL;
    }
    int n = (int)strlen(infix);
    char *postfix = malloc((n * 2) + 3);
    if (postfix == NULL)
    {
        return NULL;
    }
    char *opstack = malloc(n + 3);
    if (opstack == NULL)
    {
        free(postfix);
        return NULL;
    }
    int top = -1;
    int j = 0;
    for (int i = 0; infix[i] != '\0'; i++)
    {
        char c = infix[i];
        if (isspace((unsigned char)c))
        {
            continue;
        }
        if (isalpha((unsigned char)c))
        {
            postfix[j++] = c;
            int k = i + 1;
            while (infix[k] && isspace((unsigned char)infix[k]))
            {
                k++;
            }
            while (infix[k] == '\'')
            {
                postfix[j++] = '\'';
                k++;
            }
            i = k - 1;
            continue;
        }
        if (c == '(')
        {
            opstack[++top] = c;
            continue;
        }
        if (c == ')')
        {
            while (top >= 0 && opstack[top] != '(')
            {
                postfix[j++] = opstack[top--];
            }
            if (top >= 0 && opstack[top] == '(')
            {
                top--;
            }
            int k = i + 1;
            while (infix[k] && isspace((unsigned char)infix[k]))
            {
                k++;
            }
            while (infix[k] == '\'')
            {
                postfix[j++] = '\'';
                k++;
            }
            i = k - 1;
            continue;
        }
        if (is_op_char(c))
        {
            int cur_prec = (c == '*') ? 2 : 1;
            while (top >= 0 && opstack[top] != '(')
            {
                char topc = opstack[top];
                int top_prec = (topc == '*') ? 2 : ((topc == '+') ? 1 : 0);
                if (top_prec > cur_prec || (top_prec == cur_prec))
                {
                    postfix[j++] = opstack[top--];
                    continue;
                }
                break;
            }
            opstack[++top] = c;
            continue;
        }
        if (c == '\'')
        {
            postfix[j++] = '\'';
            continue;
        }
    }
    while (top >= 0)
    {
        postfix[j++] = opstack[top--];
    }
    postfix[j] = '\0';
    free(opstack);
    return postfix;
}

matrix_sf* evaluate_expr_sf(char name, char *expr, bst_sf *root)
{
    if (expr == NULL)
    {
        return NULL;
    }
    char *postfix = infix2postfix_sf(expr);
    if (postfix == NULL)
    {
        return NULL;
    }
    int plen = (int)strlen(postfix);
    matrix_sf **stack = malloc((plen + 3) * sizeof(matrix_sf *));
    if (stack == NULL)
    {
        free(postfix);
        return NULL;
    }
    int top = -1;
    for (int i = 0; postfix[i] != '\0'; i++)
    {
        char c = postfix[i];
        if (isalpha((unsigned char)c))
        {
            matrix_sf *m = find_bst_sf(c, root);
            if (m == NULL)
            {
                free(stack);
                free(postfix);
                return NULL;
            }
            stack[++top] = m;
            continue;
        }
        if (c == '\'')
        {
            if (top < 0)
            {
                free(stack);
                free(postfix);
                return NULL;
            }
            matrix_sf *a = stack[top--];
            matrix_sf *t = transpose_mat_sf(a);
            if (t == NULL)
            {
                if (a->name == 0)
                {
                    free(a);
                }
                free(stack);
                free(postfix);
                return NULL;
            }
            stack[++top] = t;
            if (a->name == 0)
            {
                free(a);
            }
            continue;
        }
        if (is_op_char(c))
        {
            if (top < 1)
            {
                free(stack);
                free(postfix);
                return NULL;
            }
            matrix_sf *b = stack[top--];
            matrix_sf *a = stack[top--];
            matrix_sf *r = NULL;
            if (c == '+')
            {
                r = add_mats_sf(a, b);
            }
            else if (c == '*')
            {
                r = mult_mats_sf(a, b);
            }
            if (r == NULL)
            {
                if (a->name == 0)
                {
                    free(a);
                }
                if (b->name == 0)
                {
                    free(b);
                }
                free(stack);
                free(postfix);
                return NULL;
            }
            stack[++top] = r;
            if (a->name == 0)
            {
                free(a);
            }
            if (b->name == 0)
            {
                free(b);
            }
            continue;
        }
    }
    free(postfix);
    if (top != 0)
    {
        while (top >= 0)
        {
            if (stack[top]->name == 0)
            {
                free(stack[top]);
            }
            top--;
        }
        free(stack);
        return NULL;
    }
    matrix_sf *res = stack[top];
    free(stack);
    res->name = name;
    return res;
}

matrix_sf* execute_script_sf(char *filename)
{
    if (filename == NULL)
    {
        return NULL;
    }
    FILE *f = fopen(filename, "r");
    if (f == NULL)
    {
        return NULL;
    }
    bst_sf *root = NULL;
    matrix_sf *last = NULL;
    char *line = NULL;
    size_t cap = 0;
    ssize_t rl;
    while ((rl = getline(&line, &cap, f)) != -1)
    {
        if (rl > 0 && line[rl - 1] == '\n')
        {
            line[rl - 1] = '\0';
        }
        char *p = line;
        while (*p && isspace((unsigned char)*p))
        {
            p++;
        }
        if (*p == '\0')
        {
            continue;
        }
        char lhs;
        char *eq = strchr(p, '=');
        if (eq == NULL)
        {
            continue;
        }
        if (sscanf(p, " %c", &lhs) != 1)
        {
            continue;
        }
        char *rhs = eq + 1;
        while (*rhs && isspace((unsigned char)*rhs))
        {
            rhs++;
        }
        matrix_sf *newm = NULL;
        if (strchr(rhs, '[') != NULL)
        {
            newm = create_matrix_sf(lhs, rhs);
        }
        else
        {
            char *copy = malloc(strlen(rhs) + 1);
            if (copy == NULL)
            {
                continue;
            }
            strcpy(copy, rhs);
            newm = evaluate_expr_sf(lhs, copy, root);
            free(copy);
        }
        if (newm != NULL)
        {
            root = insert_bst_sf(newm, root);
            last = newm;
        }
    }
    free(line);
    fclose(f);
    if (root == NULL)
    {
        return last;
    }
    free_bst_except_helper(root, last);
    return last;
}


// This is a utility function used during testing. Feel free to adapt the code to implement some of
// the assignment. Feel equally free to ignore it.
matrix_sf *copy_matrix(unsigned int num_rows, unsigned int num_cols, int values[]) {
    matrix_sf *m = malloc(sizeof(matrix_sf)+num_rows*num_cols*sizeof(int));
    m->name = '?';
    m->num_rows = num_rows;
    m->num_cols = num_cols;
    memcpy(m->values, values, num_rows*num_cols*sizeof(int));
    return m;
}

// Don't touch this function. It's used by the testing framework.
// It's been left here in case it helps you debug and test your code.
void print_matrix_sf(matrix_sf *mat) {
    assert(mat != NULL);
    assert(mat->num_rows <= 1000);
    assert(mat->num_cols <= 1000);
    printf("%d %d ", mat->num_rows, mat->num_cols);
    for (unsigned int i = 0; i < mat->num_rows*mat->num_cols; i++) {
        printf("%d", mat->values[i]);
        if (i < mat->num_rows*mat->num_cols-1)
            printf(" ");
    }
    printf("\n");
}
