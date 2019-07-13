len(@x, @y) :- len_impl(@x, 0, @y).

len_impl([], @x, @x).
len_impl([@x | @y], @z, @w) :- len_impl(@y, @z + 1, @w).
