#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef struct Node {
    int key;
    int count;
    int height;
    struct Node *left, *right;
} Node;

static long long cmp_count = 0;
static long long move_count = 0;
static int track_stack = 0;
static uintptr_t stack_base = 0;
static uintptr_t stack_min = 0;
static long long avl_nodes = 0;
static long long avl_peak = 0;

static void track(void) {
    char marker;
    uintptr_t addr = (uintptr_t)&marker;
    if (addr < stack_min) stack_min = addr;
}

static int compare(int a, int b) {
    cmp_count++;
    return (a > b) - (a < b);
}

static void swap(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
    move_count += 3;
}

static int median_pivot(int a[], int lo, int hi) {
    int mid = lo + (hi - lo) / 2;
    int x = a[lo], y = a[mid], z = a[hi];
    cmp_count++;
    if (x < y) {
        cmp_count++;
        if (y < z) return mid;
        cmp_count++;
        if (x < z) return hi;
        return lo;
    } else {
        cmp_count++;
        if (x < z) return lo;
        cmp_count++;
        if (y < z) return hi;
        return mid;
    }
}

static int partition(int a[], int lo, int hi) {
    int p = median_pivot(a, lo, hi);
    swap(&a[lo], &a[p]);
    int pivot = a[lo];
    int i = lo;
    for (int j = lo + 1; j <= hi; j++) {
        cmp_count++;
        if (a[j] < pivot) swap(&a[++i], &a[j]);
    }
    swap(&a[lo], &a[i]);
    return i;
}

static void quick_sort(int a[], int lo, int hi) {
    if (track_stack) track();
    if (lo >= hi) return;
    int p = partition(a, lo, hi);
    quick_sort(a, lo, p - 1);
    quick_sort(a, p + 1, hi);
}

static void array_insert(int a[], int *size, int value) {
    int pos = 0;
    while (pos < *size && compare(a[pos], value) <= 0) pos++;
    for (int k = *size; k > pos; k--) {
        a[k] = a[k - 1];
        move_count++;
    }
    a[pos] = value;
    move_count++;
    (*size)++;
}

static void array_delete(int a[], int *size, int value) {
    int pos = 0, c = 1;
    while (pos < *size) {
        c = compare(a[pos], value);
        if (c >= 0) break;
        pos++;
    }
    if (pos >= *size || c != 0) return;
    for (int k = pos; k < *size - 1; k++) {
        a[k] = a[k + 1];
        move_count++;
    }
    (*size)--;
}

static int height(Node *n) { return n ? n->height : 0; }

static void update(Node *n) {
    int l = height(n->left), r = height(n->right);
    n->height = (l > r ? l : r) + 1;
}

static Node *rotate_right(Node *y) {
    Node *x = y->left;
    y->left = x->right;
    x->right = y;
    update(y);
    update(x);
    return x;
}

static Node *rotate_left(Node *x) {
    Node *y = x->right;
    x->right = y->left;
    y->left = x;
    update(x);
    update(y);
    return y;
}

static Node *rebalance(Node *n) {
    update(n);
    int bf = height(n->left) - height(n->right);
    if (bf > 1) {
        if (height(n->left->left) < height(n->left->right)) n->left = rotate_left(n->left);
        return rotate_right(n);
    }
    if (bf < -1) {
        if (height(n->right->right) < height(n->right->left)) n->right = rotate_right(n->right);
        return rotate_left(n);
    }
    return n;
}

static Node *avl_insert(Node *n, int v) {
    if (track_stack) track();
    if (!n) {
        Node *x = malloc(sizeof(Node));
        x->key = v;
        move_count++;
        x->count = 1;
        x->height = 1;
        x->left = x->right = NULL;
        avl_nodes++;
        if (avl_nodes > avl_peak) avl_peak = avl_nodes;
        return x;
    }
    int c = compare(v, n->key);
    if (c == 0) {
        n->count++;
        return n;
    }
    if (c < 0) n->left = avl_insert(n->left, v);
    else n->right = avl_insert(n->right, v);
    return rebalance(n);
}

static Node *remove_min(Node *n, Node **min) {
    if (track_stack) track();
    if (!n->left) {
        *min = n;
        return n->right;
    }
    n->left = remove_min(n->left, min);
    return rebalance(n);
}

static Node *avl_delete(Node *n, int v) {
    if (track_stack) track();
    if (!n) return NULL;
    int c = compare(v, n->key);
    if (c < 0) n->left = avl_delete(n->left, v);
    else if (c > 0) n->right = avl_delete(n->right, v);
    else {
        if (n->count > 1) {
            n->count--;
            return n;
        }
        if (!n->left || !n->right) {
            Node *child = n->left ? n->left : n->right;
            free(n);
            avl_nodes--;
            return child;
        }
        Node *m;
        n->right = remove_min(n->right, &m);
        n->key = m->key;
        move_count++;
        n->count = m->count;
        free(m);
        avl_nodes--;
    }
    return rebalance(n);
}

static void inorder_fill(Node *n, int *out, int *idx) {
    if (!n) return;
    inorder_fill(n->left, out, idx);
    for (int i = 0; i < n->count; i++) out[(*idx)++] = n->key;
    inorder_fill(n->right, out, idx);
}

static void free_tree(Node *n) {
    if (!n) return;
    free_tree(n->left);
    free_tree(n->right);
    free(n);
}

static int is_sorted(const int a[], int n) {
    for (int i = 1; i < n; i++) if (a[i - 1] > a[i]) return 0;
    return 1;
}

static double now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1e6;
}

static void quick_process(int work[], int n, const int op_ins[], const int op_val[], int ops, int *size, long long *peak) {
    quick_sort(work, 0, n - 1);
    *size = n;
    *peak = n;
    for (int i = 0; i < ops; i++) {
        if (op_ins[i]) array_insert(work, size, op_val[i]);
        else array_delete(work, size, op_val[i]);
        if (*size > *peak) *peak = *size;
    }
}

static Node *avl_process(const int orig[], int n, const int op_ins[], const int op_val[], int ops) {
    Node *root = NULL;
    for (int i = 0; i < n; i++) root = avl_insert(root, orig[i]);
    for (int i = 0; i < ops; i++) {
        if (op_ins[i]) root = avl_insert(root, op_val[i]);
        else root = avl_delete(root, op_val[i]);
    }
    return root;
}

int main(void) {
    int sizes[] = {1000, 2000, 4000, 8000, 16000, 20000};
    int num_sizes = sizeof(sizes) / sizeof(sizes[0]);
    const int reps = 30;
    srand(12345);

    for (int s = 0; s < num_sizes; s++) {
        int n = sizes[s];
        int ops = n / 5;
        int range = 2 * n;
        int cap = n + ops + 1;
        int *orig = malloc(sizeof(int) * n);
        int *work = malloc(sizeof(int) * cap);
        int *tmp = malloc(sizeof(int) * cap);
        int *op_ins = malloc(sizeof(int) * ops);
        int *op_val = malloc(sizeof(int) * ops);
        for (int i = 0; i < n; i++) orig[i] = rand() % range;
        for (int i = 0; i < ops; i++) {
            op_ins[i] = (rand() % 2 == 0);
            op_val[i] = rand() % range;
        }

        int qsize;
        long long qpeak;
        char base;

        memcpy(work, orig, sizeof(int) * n);
        cmp_count = 0; move_count = 0;
        track_stack = 1;
        stack_base = (uintptr_t)&base;
        stack_min = stack_base;
        quick_process(work, n, op_ins, op_val, ops, &qsize, &qpeak);
        track_stack = 0;
        long long q_cmp = cmp_count, q_move = move_count;
        long long q_mem = qpeak * (long long)sizeof(int) + (long long)(stack_base - stack_min);
        if (!is_sorted(work, qsize)) { printf("ERROR: array not sorted\n"); return 1; }

        cmp_count = 0; move_count = 0;
        avl_nodes = 0; avl_peak = 0;
        track_stack = 1;
        stack_base = (uintptr_t)&base;
        stack_min = stack_base;
        Node *root = NULL;
        for (int i = 0; i < n; i++) root = avl_insert(root, orig[i]);
        long long build_cmp = cmp_count, build_move = move_count;
        track_stack = 0;
        int idx = 0;
        inorder_fill(root, tmp, &idx);
        if (idx != n || !is_sorted(tmp, idx)) { printf("ERROR: AVL inorder not sorted\n"); return 1; }
        cmp_count = build_cmp; move_count = build_move;
        track_stack = 1;
        for (int i = 0; i < ops; i++) {
            if (op_ins[i]) root = avl_insert(root, op_val[i]);
            else root = avl_delete(root, op_val[i]);
        }
        track_stack = 0;
        long long a_cmp = cmp_count, a_move = move_count;
        long long a_mem = avl_peak * (long long)sizeof(Node) + (long long)(stack_base - stack_min);
        idx = 0;
        inorder_fill(root, tmp, &idx);
        if (idx != qsize || memcmp(tmp, work, sizeof(int) * idx) != 0) { printf("ERROR: final data mismatch\n"); return 1; }
        free_tree(root);

        double q_total = 0, a_total = 0;
        for (int r = 0; r < reps; r++) {
            memcpy(work, orig, sizeof(int) * n);
            double st = now_ms();
            quick_process(work, n, op_ins, op_val, ops, &qsize, &qpeak);
            q_total += now_ms() - st;

            st = now_ms();
            Node *rt = avl_process(orig, n, op_ins, op_val, ops);
            a_total += now_ms() - st;
            free_tree(rt);
        }

        printf("Data Size : %d\n", n);
        printf("Operations: %d\n\n", ops);
        printf("%-18s%-16s%s\n", "", "Quick Sort", "AVL Tree");
        printf("------------------------------------------------\n");
        char b1[32], b2[32];
        snprintf(b1, sizeof b1, "%.4f ms", q_total / reps);
        snprintf(b2, sizeof b2, "%.4f ms", a_total / reps);
        printf("%-18s%-16s%s\n", "Total Time", b1, b2);
        printf("%-18s%-16lld%lld\n", "Comparisons", q_cmp, a_cmp);
        printf("%-18s%-16lld%lld\n", "Data Movements", q_move, a_move);
        snprintf(b1, sizeof b1, "%lld Bytes", q_mem);
        snprintf(b2, sizeof b2, "%lld Bytes", a_mem);
        printf("%-18s%-16s%s\n\n", "Memory Usage", b1, b2);
        printf("%-18s%-16d%d\n\n", "Final Data Count", qsize, idx);

        free(orig); free(work); free(tmp); free(op_ins); free(op_val);
    }
    return 0;
}
