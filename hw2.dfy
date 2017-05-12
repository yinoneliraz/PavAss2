method swap(arr: array<int>, x:int, y:int) 
modifies arr;
requires arr!=null && 0<=x<arr.Length && 0<=y<arr.Length;
ensures old(arr[x])==arr[y] && old(arr[y])==arr[x];
{
  ghost var n:=arr[x];
  ghost var m:=arr[y];
  assert arr[y]==m && arr[x]==n;
  var ta:=arr[x];
  assert arr[y]==m && arr[x]==n;
  var tb:=arr[y];
  assert arr[y]==m && arr[x]==n;
  arr[x]:=tb;
  assert arr[y]==m && arr[x]==m;
  arr[y]:=ta;  
  assert arr[x]==m && arr[y]==n;
}
// An axiomatic definition of integer square root.
function Sqrt(n: int): int
  requires n >= 0;
  ensures forall m:nat :: m*m<=n && (m+1)*(m+1)>n ==> m==Sqrt(n);

// Computes the integer square root of n via a linear search from 0 to n.
method SlowSqrt(n: nat) returns (r: nat)
  ensures r == Sqrt(n)
{
  r := 0;
  while((r+1)*(r+1)<=n)
  invariant r*r<=n;
  {
    r:=r+1;
  }
}
// Computes the integer square root of n via a binary search.
method FastSqrt(n: nat) returns (r: nat)
	ensures r == Sqrt(n)
{
	var low:nat := 0;
	var high:nat := n;
	r:=(high + low)/2;
	while(r*r!=n)
	decreases if r*r<=n then n-r*r else r*r-n
	invariant 0 <= low <= high <= n
	{
		if(r*r>n){
			high:=r;
			r:=(high + low)/2;
		}
		else{
			low:=r;
			r:=(high + low)/2;
		}
	}
	assert r*r==Sqrt(n);
}
