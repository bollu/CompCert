void stmtinterchange(char A[2]) {
    {
        A[0] = 1;
        A[1] = 2;
    }
}

int main() {
    char Arr[2];
    stmtinterchange(Arr);
    return (int)Arr[0];
}
