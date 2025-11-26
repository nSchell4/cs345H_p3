// A recursive specification and imperative implementation of Fibonacci number calculation

function {:induction false} FibonacciSpec(n: int): int {
    if n <= 0 then 0
    else if n == 1 then 1
    else FibonacciSpec(n - 1) + FibonacciSpec(n - 2)
}

method {:induction false} Fibonacci(n: int) returns (out: int)
    requires n >= 0
    ensures out == FibonacciSpec(n)
{
    out := 0;
    var b := 1;
    var i := 0;

    // loop invariants:
    assert out == FibonacciSpec(i) && b == FibonacciSpec(i + 1) && 0 <= i <= n;

    while (i < n)
        decreases n - i
        invariant 0 <= i <= n
        invariant out == FibonacciSpec(i)
        invariant b == FibonacciSpec(i + 1)
    {
        var temp := out;
        out := b;
        b := temp + b;
        i := i + 1;
    }

    // invariant holds here, too
    assert out == FibonacciSpec(i) && b == FibonacciSpec(i + 1) && 0 <= i <= n;
}

method FibonacciTest(n: int) 
    requires n >= 0
{
    var r := Fibonacci(n);
    assert r == FibonacciSpec(n) by {
        FibonacciProof(n);
    }
}
