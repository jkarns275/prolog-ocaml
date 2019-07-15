mov(@x, @x).

square([@x | @tail], [@o | @otail]) :- squaren(@x, @o), square(@tail, @otail).
square([], []i).
squaren(@x, @o) :- mov(@x * @x, @o).

add([@x | @xtail], [@y | @ytail], [@o | @otail]) :- mov(@x + @y, @o), add(@xtail, @ytail, @otail).
