method Abs(x : int) returns (y : int) 
  ensures 0 <= y;
  ensures 0 <= x ==> y == x;
  ensures x < 0 ==> y == -x;
{
  if (x < 0)
   {y := -x;}
  else
   {y := x;}
}