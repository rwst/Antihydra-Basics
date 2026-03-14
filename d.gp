\\ Compute D(0)=7, D(n+1)=ceil(3*D(n)/2) for n=0..N-1
\\ x_n = frac(3*D(n)/2), compute discrepancy optimally

default(parisizemax, "2G");

N = 10^6;

\\ Since frac(3*D(n)/2) is always 0 or 1/2,
\\ the sup over all [u,v) is achieved at an interval boundary at 0, 1/2, or 1.
\\ Check all 3 non-trivial intervals: [0,1/2), [1/2,1), [0,1)

cnt0 = 0;  \\ count of frac = 0
cnt1 = 0;  \\ count of frac = 1/2
d = 7;
{
for(n = 1, N,
  if(d % 2 == 0, cnt0++, cnt1++);
  d = ceil(3*d/2);
);
}

printf("N = %d\n", N);
printf("count(frac=0)   = %d\n", cnt0);
printf("count(frac=1/2) = %d\n", cnt1);
printf("\n");

\\ Check all intervals [u,v) with u,v in {0, 1/2, 1}
sup_val = 0;
intervals = [[0, 1/2], [1/2, 1], [0, 1]];
{
for(i = 1, 3,
  u = intervals[i][1];
  v = intervals[i][2];
  \\ count of x_n in [u,v)
  if(u == 0 && v == 1/2, c = cnt0,
    if(u == 1/2 && v == 1, c = cnt1,
      c = cnt0 + cnt1));
  val = abs(c/N - (v - u));
  if(val > sup_val, sup_val = val);
  printf("[u,v) = [%.1f, %.1f): count = %d, count/N = %.6f, v-u = %.1f, |diff| = %.6f\n", u*1.0, v*1.0, c, c/N*1.0, (v-u)*1.0, val*1.0);
);
}

printf("\nDiscrepancy D_N = %.6f\n", sup_val*1.0);
