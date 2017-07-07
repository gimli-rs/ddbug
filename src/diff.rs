use std::cmp;
use std::collections::BinaryHeap;
use std::usize;

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    None,
    Diagonal,
    Horizontal,
    Vertical,
}

#[derive(Debug, Clone, Copy)]
struct Node {
    cost: usize,
    from: Direction,
    done: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct State {
    cost: usize,
    index1: usize,
    index2: usize,
}

impl Ord for State {
    fn cmp(&self, other: &State) -> cmp::Ordering {
        // min-heap
        other.cost.cmp(&self.cost)
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &State) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// Use Dijkstra's algorithm to find the shortest edit path between two arrays.
//
// step_cost is used for add/delete operations.
//
// diff_cost is used to calculate the cost for modify operations. It should
// return:
//     0 for items that are completely equal
//     (2 * step_cost) for items that are completely different
//     values in between for items that are partially equal
pub fn shortest_path<Item, F>(
    item1: &[Item],
    item2: &[Item],
    step_cost: usize,
    diff_cost: F,
) -> Vec<Direction>
    where F: Fn(&Item, &Item) -> usize
{
    // len + 1 because we need to allow for the 0 items state too.
    let len1 = item1.len() + 1;
    let len2 = item2.len() + 1;
    let len = len1 * len2;

    let mut node: Vec<Node> = vec![Node {
            cost: usize::MAX,
            from: Direction::None,
            done: false,
        }; len];
    let mut heap = BinaryHeap::new();

    fn push(
        node: &mut Node,
        heap: &mut BinaryHeap<State>,
        index1: usize,
        index2: usize,
        cost: usize,
        from: Direction,
    ) {
        if cost < node.cost {
            node.cost = cost;
            node.from = from;
            heap.push(State {
                cost: cost,
                index1: index1,
                index2: index2,
            });
        }
    }

    // Start at the end.  This makes indexing and boundary conditions
    // simpler, and also means we can backtrack in order.
    push(&mut node[len - 1], &mut heap, len1 - 1, len2 - 1, 0, Direction::None);

    while let Some(State { index1, index2, .. }) = heap.pop() {
        if (index1, index2) == (0, 0) {
            let mut result = Vec::new();
            let mut index1 = 0;
            let mut index2 = 0;
            loop {
                let index = index1 + index2 * len1;
                let from = node[index].from;
                match from {
                    Direction::None => {
                        return result;
                    }
                    Direction::Diagonal => {
                        index1 += 1;
                        index2 += 1;
                    }
                    Direction::Horizontal => {
                        index1 += 1;
                    }
                    Direction::Vertical => {
                        index2 += 1;
                    }
                }
                result.push(from);
            }
        }

        let index = index1 + index2 * len1;
        if node[index].done {
            continue;
        }
        node[index].done = true;

        if index1 > 0 {
            let next1 = index1 - 1;
            let next = index - 1;
            if !node[next].done {
                let cost = node[index].cost + step_cost;
                push(&mut node[next], &mut heap, next1, index2, cost, Direction::Horizontal);
            }
        }
        if index2 > 0 {
            let next2 = index2 - 1;
            let next = index - len1;
            if !node[next].done {
                let cost = node[index].cost + step_cost;
                push(&mut node[next], &mut heap, index1, next2, cost, Direction::Vertical);
            }
        }
        if index1 > 0 && index2 > 0 {
            let next1 = index1 - 1;
            let next2 = index2 - 1;
            let next = index - len1 - 1;
            if !node[next].done {
                let cost = node[index].cost + diff_cost(&item1[next1], &item2[next2]);
                push(&mut node[next], &mut heap, next1, next2, cost, Direction::Diagonal);
            }
        }
    }

    panic!("failed to find shortest path");
}
