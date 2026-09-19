// x - y = n

struct Variable(usize);

struct Integer(isize);

struct Equality {
    x: Variable,
    y: Variable,
    n: Integer,
}
