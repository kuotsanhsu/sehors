use crate::{
    algebra::{Group, Monoid},
    zeroed_slice::ZeroedSlice,
};

trait Graph {
    type Vertex;
    type EdgeLabel;
    fn order(&self) -> usize;
    fn size(&self) -> usize;
    fn out_edges(&self, v: Self::Vertex) -> impl Iterator<Item = (Self::Vertex, Self::EdgeLabel)>;
}

trait Edge {
    type Vertex;
    type Weight;
    fn src(&self) -> Self::Vertex;
    fn dst(&self) -> Self::Vertex;
    fn weight(&self) -> Self::Weight;
}

struct CSR<'a, EdgeId, E> {
    /// EdgeId -> Edge
    edge: &'a [E],
    /// Vertex -> NodeId (= EdgeId)
    index: &'a [EdgeId],
    /// NodeId (= EdgeId) -> EdgeId
    node: &'a [EdgeId],
}

trait Bounded {
    const MAX: usize;
}

trait ForwardIndex: Monoid + Into<usize> {
    fn increment(&mut self);
}

impl<'a, VertexId, EdgeId, E> CSR<'a, EdgeId, E>
where
    E: Edge<Vertex = VertexId>,
{
    fn new(edge: &'a [E], index: ZeroedSlice<'a, EdgeId>, node: &'a mut [EdgeId]) -> Self
    where
        VertexId: Into<usize> + Bounded,
        EdgeId: ForwardIndex + Copy,
    {
        let size = edge.len();
        assert_eq!(size, node.len());
        assert!(VertexId::MAX >= size);

        let index = index.into_mut();
        let order = index.len();
        assert!(VertexId::MAX >= order);

        for e in edge {
            let v = e.src().into();
            assert!(v < order);
            index[v].increment();
        }
        index
            .iter_mut()
            .fold(EdgeId::ZERO, |sum, d| sum + std::mem::replace(d, sum));

        let mut edge_id = EdgeId::ZERO;
        for e in edge {
            let v = e.src().into();
            node[index[v].into()] = edge_id;
            index[v].increment();
            edge_id.increment();
        }

        Self { edge, index, node }
    }
}

impl<'a, VertexId, EdgeId, Weight, E> Graph for CSR<'a, EdgeId, E>
where
    VertexId: Into<usize>,
    EdgeId: Into<usize> + Copy,
    E: Edge<Vertex = VertexId, Weight = Weight>,
{
    type Vertex = VertexId;
    type EdgeLabel = (EdgeId, Weight);
    fn order(&self) -> usize {
        self.index.len()
    }
    fn size(&self) -> usize {
        self.edge.len()
    }
    fn out_edges(&self, v: Self::Vertex) -> impl Iterator<Item = (Self::Vertex, Self::EdgeLabel)> {
        let v = v.into();
        let end = self.index[v].into();
        let start = if v == 0 { 0 } else { self.index[v - 1].into() };
        self.node[start..end].iter().map(|&i| {
            let e = &self.edge[i.into()];
            (e.dst(), (i, e.weight()))
        })
    }
}

/// `x - y = n` iff `y + n = x`
struct Equality<Variable, Integer> {
    x: Variable,
    y: Variable,
    n: Integer,
}

impl<Variable, Integer> Edge for Equality<Variable, Integer>
where
    Variable: Copy,
    Integer: Copy,
{
    type Vertex = Variable;
    type Weight = Integer;
    fn src(&self) -> Self::Vertex {
        self.y
    }
    fn dst(&self) -> Self::Vertex {
        self.x
    }
    fn weight(&self) -> Self::Weight {
        self.n
    }
}

struct Bigraph<'a, EdgeId, E> {
    forward: CSR<'a, EdgeId, E>,
    backward: CSR<'a, EdgeId, E>,
}

impl<'a, VertexId, EdgeId, E> Bigraph<'a, EdgeId, E>
where
    E: Edge<Vertex = VertexId>,
{
    fn new(
        edge: &'a [E],
        forward_index: ZeroedSlice<'a, EdgeId>,
        forward_node: &'a mut [EdgeId],
        backward_index: ZeroedSlice<'a, EdgeId>,
        backward_node: &'a mut [EdgeId],
    ) -> Self
    where
        VertexId: Into<usize> + Bounded,
        EdgeId: ForwardIndex + Copy,
    {
        Self {
            forward: CSR::new(edge, forward_index, forward_node),
            // FIXME: `backward` should swap `src` with `dst` and negate `weight`.
            backward: CSR::new(edge, backward_index, backward_node),
        }
    }
}

impl<'a, VertexId, EdgeId, Weight, E> Graph for Bigraph<'a, EdgeId, E>
where
    VertexId: Into<usize> + Copy,
    EdgeId: Into<usize> + Copy,
    E: Edge<Vertex = VertexId, Weight = Weight>,
{
    type Vertex = VertexId;
    type EdgeLabel = (EdgeId, Weight);
    fn order(&self) -> usize {
        self.forward.order()
    }
    fn size(&self) -> usize {
        self.forward.size() + self.backward.size()
    }
    fn out_edges(&self, v: Self::Vertex) -> impl Iterator<Item = (Self::Vertex, Self::EdgeLabel)> {
        // FIXME: the `edge_id` should differentiate `forward` and `backward`.
        self.forward.out_edges(v).chain(self.backward.out_edges(v))
    }
}

enum EqualityResult<'a, VertexId, EdgeId> {
    NonzeroCycle {
        representative: &'a mut [VertexId],
        bfs_queue_id: usize,
        edge_id: EdgeId,
    },
    Ok {
        representative: &'a mut [VertexId],
        component_count: usize,
    },
}

/// Requires no self-loop.
fn solve_equalities<'a, EdgeId, Variable, Integer>(
    bigraph: &'a Bigraph<EdgeId, Equality<Variable, Integer>>,
    representative: ZeroedSlice<'a, Variable>,
    offset: &mut [Integer],
    bfs_queue: &mut [Variable],
) -> EqualityResult<'a, Variable, EdgeId>
where
    EdgeId: Into<usize> + Copy,
    Variable: ForwardIndex + Copy,
    Integer: Group + Copy,
{
    let order = bigraph.order();
    let representative = representative.into_mut(); // shadows `representative`
    assert_eq!(order, representative.len());
    assert_eq!(order, offset.len());
    assert_eq!(order, bfs_queue.len());
    let mut component = Variable::ZERO;
    let mut v = Variable::ZERO;
    while v.into() < order {
        if representative[v.into()] == Variable::ZERO {
            // unvisited
            let v = v; // shadows `v`
            component.increment();
            let component = component; // shadows `component`
            representative[v.into()] = component;
            offset[v.into()] = Integer::ZERO;
            bfs_queue[0] = v;
            let mut i = 0;
            let mut j = 1;
            while i < j {
                let v = bfs_queue[i]; // shadows `v`
                let base = offset[v.into()];
                for (v, (edge_id, weight)) in bigraph.out_edges(v) {
                    let expected_offset = base + weight;
                    if representative[v.into()] == Variable::ZERO {
                        // unvisited
                        representative[v.into()] = component;
                        offset[v.into()] = expected_offset;
                        bfs_queue[j] = v;
                        j += 1;
                    } else if offset[v.into()] != expected_offset {
                        return EqualityResult::NonzeroCycle {
                            representative,
                            bfs_queue_id: i,
                            edge_id,
                        };
                    }
                }
                i += 1;
            }
        }
        v.increment();
    }

    return EqualityResult::Ok {
        representative,
        component_count: component.into(),
    };
}
