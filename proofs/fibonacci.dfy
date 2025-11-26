lemma {:induction false} FibonacciProof(n: int)
    requires n >= 0
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        FibonacciProof(n - 1);
        FibonacciProof(n - 2);
    }
}