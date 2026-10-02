use crate::{
    algebra::{Group, Monoid},
    zeroed_slice::ZeroedSlice,
};

/// `x - y = n` iff `y + n = x`
struct Equality<Variable, Integer> {
    x: Variable,
    y: Variable,
    n: Integer,
}

struct CSRNode<Vertex, Weight> {
    target: Vertex,
    weight: Weight,
}

struct CSR<'a, Vertex, Weight> {
    index: &'a mut [Vertex],
    node: &'a mut [CSRNode<Vertex, Weight>],
}

impl<'a, Vertex, Weight> CSR<'a, Vertex, Weight> {
    fn new(index: ZeroedSlice<'a, Vertex>, node: &'a mut [CSRNode<Vertex, Weight>]) -> Self {
        Self {
            index: index.into_mut(),
            node,
        }
    }

    fn adjacency(&self, v: Vertex) -> &[CSRNode<Vertex, Weight>]
    where
        Vertex: Into<usize> + Copy,
    {
        let v = v.into();
        let end = self.index[v].into();
        let start = if v == 0 { 0 } else { self.index[v - 1].into() };
        assert!(start <= end);
        &self.node[start..end]
    }
}

trait ForwardIndex: Monoid + Into<usize> {
    const MAX: usize;
    fn increment(&mut self);
}

enum EqualityResult<'a, Vertex, Weight> {
    Loop {
        representative: ZeroedSlice<'a, Vertex>,
        edge_id: usize,
    },
    NonzeroCycle {
        representative: &'a mut [Vertex],
        bfs_queue_id: usize,
        csr_node: &'a CSRNode<Vertex, Weight>,
    },
    Ok {
        representative: &'a mut [Vertex],
        component_count: usize,
    },
}

fn solve_equalities<'a, Vertex: ForwardIndex + Copy, Weight: Group + Copy>(
    equalities: &[Equality<Vertex, Weight>],
    x_csr: &'a mut CSR<Vertex, Weight>,
    y_csr: &'a mut CSR<Vertex, Weight>,
    representative: ZeroedSlice<'a, Vertex>,
    offset: &mut [Weight],
    bfs_queue: &mut [Vertex],
) -> EqualityResult<'a, Vertex, Weight> {
    let size = equalities.len();
    assert!(Vertex::MAX >= size);
    assert_eq!(size, x_csr.node.len());
    assert_eq!(size, y_csr.node.len());

    let order = x_csr.index.len();
    assert!(Vertex::MAX >= order);
    assert_eq!(order, y_csr.index.len());

    let mut loop_count: usize = 0;
    for (edge_id, e) in equalities.iter().enumerate() {
        let x = e.x.into();
        assert!(x < order);
        let y = e.y.into();
        assert!(y < order);
        if x != y {
            x_csr.index[x].increment();
            y_csr.index[y].increment();
        } else if e.n == Weight::ZERO {
            loop_count += 1;
        } else {
            return EqualityResult::Loop {
                representative,
                edge_id,
            };
        }
    }
    {
        let sum = x_csr
            .index
            .iter_mut()
            .fold(Vertex::ZERO, |sum, i| sum + std::mem::replace(i, sum));
        assert_eq!(size, loop_count + sum.into());
    }
    {
        let sum = y_csr
            .index
            .iter_mut()
            .fold(Vertex::ZERO, |sum, i| sum + std::mem::replace(i, sum));
        assert_eq!(size, loop_count + sum.into());
    }
    for e in equalities {
        let x = e.x.into();
        assert!(x < x_csr.index.len());
        let i = x_csr.index[x].into();
        assert!(i < x_csr.node.len());
        x_csr.node[i] = CSRNode {
            target: e.y,
            weight: -e.n,
        };
        x_csr.index[x].increment();

        let y = e.y.into();
        assert!(y < y_csr.index.len());
        let j = y_csr.index[y].into();
        assert!(j < y_csr.node.len());
        y_csr.node[j] = CSRNode {
            target: e.x,
            weight: e.n,
        };
        y_csr.index[y].increment();
    }

    let representative = representative.into_mut(); // shadows `representative`
    assert_eq!(order, representative.len());
    assert_eq!(order, offset.len());
    assert_eq!(order, bfs_queue.len());
    let mut component = Vertex::ZERO;
    let mut v = Vertex::ZERO;
    while v.into() < order {
        if representative[v.into()] == Vertex::ZERO {
            // unvisited
            let v = v; // shadows `v`
            component.increment();
            let component = component; // shadows `component`
            representative[v.into()] = component;
            offset[v.into()] = Weight::ZERO;
            bfs_queue[0] = v;
            let mut i = 0;
            let mut j = 1;
            while i < j {
                let v = bfs_queue[i]; // shadows `v`
                let base = offset[v.into()];
                for e in x_csr.adjacency(v).iter().chain(y_csr.adjacency(v)) {
                    let v = e.target; // shadows `v`
                    let expected_offset = base + e.weight;
                    if representative[v.into()] == Vertex::ZERO {
                        // unvisited
                        representative[v.into()] = component;
                        offset[v.into()] = expected_offset;
                        bfs_queue[j] = v;
                        j += 1;
                    } else if offset[v.into()] != expected_offset {
                        return EqualityResult::NonzeroCycle {
                            representative,
                            bfs_queue_id: i,
                            csr_node: e,
                        };
                    }
                }
                i += 1;
            }
            loop_count += i;
        }
        v.increment();
    }
    assert_eq!(order, loop_count);

    return EqualityResult::Ok {
        representative,
        component_count: component.into(),
    };
}
