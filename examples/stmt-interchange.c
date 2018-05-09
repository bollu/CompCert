void stmtinterchange(int A[2]) {
    A[0] = 1;
    A[1] = 2;
}

int main() {
    int Arr[2];
    stmtinterchange(Arr);
    return Arr[0];
}
