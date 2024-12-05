function fact(n:nat) : (res:int)
    decreases n
    requires n > 0
    {
        if n==1 then 1 else n*fact(n-1)
    }


method ComputeFact(n : nat) returns (res : nat)
requires n > 0;
ensures res == fact(n)
{
  res := 1;
  var i := 2;
  while (i <= n) 
    invariant res == fact(i)
    decreases n-i
  {
    res := res * i;
    i := i + 1;
  }
}