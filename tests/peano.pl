mov(@x, @x).

inc(@x, [@x]).
dec([@x | @tail], @x).

add(@x, @y, @z) :- add_(@y, @x, @z).
add_([@y | @t], [@z | @zt], @w) :- add_(@y, [[@z]], @w).
add_([], @z, @z).
add(@x, @y, [@z | @zt]) :- sub([@z], @x, @y).


eq([@x | @xtail], [@y | @ytail]) :- eq(@x, @y).
eq([], []).

neq([@x | @tail], []).
neq([], [@y | @tail]).
neq([@x | @xtail], [@y | @ytail]) :- neq(@x, @y).

sub(@x, [], @x).
sub([@x | @xtail], [@y | @ytail], @w) :- sub(@x, @y, @w).

copy([], []).
copy([@x | @xt], @out) :- copy(@x, @o), mov([@o], @out).

mul(@x, [], []).
mul([], @x, []).
mul(@x, [@y | @yt], @w) :- mul(@x, @y, @o), add(@x, @o, @w).

display(@x, @y) :- to_number(@x, @z), mov(@z, @y).
to_number(@x, @z) :- to_number_(@x, 0, @z).
to_number_([], @x, @x).
to_number_([@x | @xtail], @y, @z) :- to_number_(@x, 1 + @y, @z).

lt([], [@x | @xtail]).
lt([@x | @xt], [@y | @yt]) :- lt(@x, @y).

sqrt([], []).
sqrt(@x, @o) :- sqrt_(@x, [[]], @o).
sqrt_(@x, @y, @o) :- mul(@y, @y, @z), eq(@z, @x), mov(@y, @o).
sqrt_(@x, @y, @o) :- mul(@y, @y, @z), lt(@y, @x), sqrt_(@x, [@y], @o).
