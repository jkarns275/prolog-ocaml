mov(@x, @x).

inc(@x, [@x]).
dec([@x | @tail], @x).

add(@x, @y, @z) :- add_(@y, @x, @z).
add_([@y | @t], @z, @w) :- add_(@y, [@z], @w).
add_([], @z, @z).

eq([@x | @xtail], [@y | @ytail]) :- eq(@x, @y).
eq([], []).

neq([@x | @tail], []).
neq([], [@y | @tail]).
neq([@x | @xtail], [@y | @ytail]) :- neq(@x, @y).

sub(@x, [], @x).
sub([@x | @xtail], [@y | @ytail], @w) :- sub(@x, @y, @w).

mul(@x, [], []).
mul(@x, [@y | @ytail], @w) :- mul(@x, @y, @z), add(@z, @x, @p), mov(@p, @w).

display(@x, @y) :- to_number(@x, @z), mov(@z, @y).
to_number(@x, @z) :- to_number_(@x, 0, @z).
to_number_([], @x, @x).
to_number_([@x | @xtail], @y, @z) :- to_number_(@x, 1 + @y, @z).
