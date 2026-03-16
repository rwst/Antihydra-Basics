\\ Base 3/2 representation
{
a(n) = if(n < 1, 0, a(n\3 * 2) * 10 + n%3);
}

\\ Print first 100 iterates of D(n+1)=ceil(3*D(n)/2), D(0)=1, in base 3/2
{
d = 1;
for(n = 1, 100,
  if(n > 1, printf(", "));
  printf("%d", a(d));
  d = ceil(3*d/2);
);
}
