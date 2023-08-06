// Online Go compiler to run Golang program online
// Print "Hello World!" message

package main

import (
	"fmt"
	"math"
	"math/bits"
	"sort"
	"strings"
)

type Node struct {
	value    string
	children []*Node
	depth    int
	parent   *Node
}

type Rmq interface {
	query(int, int) int
}

type LookupTable struct {
	table [][]int
}

type SparseTable struct {
	table [][]int
	data  []int
}

func makeLookupTable(data []int) LookupTable {
	table := make([][]int, len(data))
	for i := 0; i < len(data); i++ {
		table[i] = make([]int, len(data))
	}

	for start := 0; start < len(data); start++ {
		smallestIndex := start
		table[start][start] = start
		for end := start + 1; end < len(data); end++ {
			if data[end] < data[smallestIndex] {
				smallestIndex = end
			}
			table[start][end] = smallestIndex
			table[end][start] = smallestIndex
		}
	}
	return LookupTable{table}
}
func makeLookupTableRmq(data []int) Rmq {
	lookupTable := makeLookupTable(data)
	return Rmq(&lookupTable)
}

func (self *LookupTable) query(start int, end int) int {
	return self.table[start][end]
}

func makeSparseTable(data []int) SparseTable {
	length := uint(len(data))
	nRows := bits.Len(length)

	table := make([][]int, nRows)
	table[0] = make([]int, length)

	for i := 0; i < len(data); i++ {
		table[0][i] = i
	}

	size := 2
	for i := 1; i < nRows; i++ {
		rowLength := len(data) - size + 1
		table[i] = make([]int, rowLength)

		for j := 0; j < rowLength; j++ {
			index1 := table[i-1][j]
			index2 := table[i-1][j+size/2]
			var minIndex int
			if data[index1] <= data[index2] {
				minIndex = index1
			} else {
				minIndex = index2
			}
			table[i][j] = minIndex
		}

		size *= 2
	}

	return SparseTable{data: data, table: table}
}
func makeSparseTableRmq(data []int) Rmq {
	sparseTable := makeSparseTable(data)
	return Rmq(&sparseTable)
}

func (self *SparseTable) query(a int, b int) int {
	var start, end int
	if a <= b {
		start = a
		end = b
	} else {
		start = b
		end = a
	}
	size := uint(end - start + 1)
	row := bits.Len(size) - 1
	rangeSize := 1 << row

	index1 := self.table[row][start]
	index2 := self.table[row][end-rangeSize+1]
	if self.data[index1] <= self.data[index2] {
		return index1
	} else {
		return index2
	}
}

func computeDepths(node *Node, depth int) {
	node.depth = depth
	for _, child := range node.children {
		computeDepths(child, depth+1)
	}
}

func _treeToRqmSliceDfs(node *Node, nodes *[]*Node, nodeToIndex map[*Node]int) {
	nodeToIndex[node] = len(*nodes)
	*nodes = append(*nodes, node)
	for _, child := range node.children {
		_treeToRqmSliceDfs(child, nodes, nodeToIndex)
		*nodes = append(*nodes, node)
	}
}
func treeToRmqSlice(root *Node, nNodes int) ([]*Node, map[*Node]int) {
	nodes := make([]*Node, 0, nNodes*2-1)
	nodeToIndex := map[*Node]int{}
	_treeToRqmSliceDfs(root, &nodes, nodeToIndex)
	return nodes, nodeToIndex
}

func lca(a *Node, b *Node) *Node {
	if a == nil || b == nil {
		return nil
	}
	minDepth := a.depth
	if b.depth < minDepth {
		minDepth = b.depth
	}
	for a.depth > minDepth {
		a = a.parent
	}
	for b.depth > minDepth {
		b = b.parent
	}
	for a != nil {
		if a == b {
			return a
		}
		a = a.parent
		b = b.parent
	}
	panic("node depths incorrect")
}

type Lca struct {
	nodes       []*Node
	depths      []int
	nodeToIndex map[*Node]int
	rmq         Rmq
}

func makeLca(root *Node, makeRmq func([]int) Rmq) Lca {
	nodes, nodeToIndex := treeToRmqSlice(root, 1)

	depths := make([]int, 0, len(nodes))
	for _, n := range nodes {
		depths = append(depths, n.depth)
	}

	rmq := makeRmq(depths)

	return Lca{
		nodes,
		depths,
		nodeToIndex,
		rmq,
	}
}

func (lca Lca) query(a *Node, b *Node) *Node {
	indexA := lca.nodeToIndex[a]
	indexB := lca.nodeToIndex[b]
	lcaIndex := lca.rmq.query(indexA, indexB)
	return lca.nodes[lcaIndex]
}

func chunkToChunkId(chunk []int) uint {
	id := uint(0)
	for i := 0; i < len(chunk)-1; i++ {
		var bit uint
		if chunk[i+1] == chunk[i]+1 {
			bit = 1
		} else if chunk[i+1] == chunk[i]-1 {
			bit = 0
		} else {
			panic("invalid LCA chunk")
		}
		id |= bit << i
	}
	return id
}

func chuckIdToChuck(id uint, length int) []int {
	chunk := make([]int, 0, length)
	chunk = append(chunk, 0)
	for i := 0; i < length-1; i++ {
		lsb := id & 1
		lastValue := chunk[i]
		if lsb == 1 {
			chunk = append(chunk, lastValue+1)
		} else {
			chunk = append(chunk, lastValue-1)
		}
		id = id >> 1
	}
	return chunk
}

type IndirectionLca struct {
	data               []int
	chunkSize          int
	sparseTable        SparseTable
	chunkMinimaIndexes []int
	chunks             []*LookupTable
}

func makeIndirectionLca(data []int) IndirectionLca {
	chunkSize := int(math.Round(math.Log2(float64(len(data))) / 2))

	nChunks := len(data) / chunkSize
	if nChunks*chunkSize != len(data) {
		nChunks += 1
	}
	chunkMinima := make([]int, 0, nChunks)
	chunkMinimaIndexes := make([]int, 0, nChunks)
	chunkMinimaOffsets := make([]int, 0, nChunks)
	chunks := make([]*LookupTable, 0, nChunks)
	chunkIdToLookupTable := map[uint]*LookupTable{}

	for start := 0; start < len(data); start += chunkSize {
		end := start + chunkSize
		if end > len(data) {
			end = len(data)
		}
		minimumIndex := start
		for i := start + 1; i < end; i++ {
			if data[i] < data[minimumIndex] {
				minimumIndex = i
			}
		}

		chunkMinima = append(chunkMinima, data[minimumIndex])
		chunkMinimaIndexes = append(chunkMinimaIndexes, minimumIndex)
		chunkMinimaOffsets = append(chunkMinimaOffsets, minimumIndex-start)

		var chunk []int
		if end == start+chunkSize {
			chunk = data[start:end]
		} else {
			chunk = make([]int, 0, chunkSize)
			copy(chunk, data[start:end])
			for len(chunk) < chunkSize {
				chunk = append(chunk, chunk[len(chunk)-1]+1)
			}
		}

		chunkId := chunkToChunkId(chunk)
		lookupTable := chunkIdToLookupTable[chunkId]
		if lookupTable == nil {
			tempLookupTable := makeLookupTable(chunk)
			lookupTable = &tempLookupTable
			chunkIdToLookupTable[chunkId] = lookupTable
		}
		chunks = append(chunks, lookupTable)
	}

	sparseTable := makeSparseTable(chunkMinima)

	return IndirectionLca{data, chunkSize, sparseTable, chunkMinimaIndexes, chunks}
}

func makeIndirectionLcaRmq(data []int) Rmq {
	lca := makeIndirectionLca(data)
	return Rmq(&lca)
}

func swap[T interface{}](a *T, b *T) {
	temp := *a
	*a = *b
	*b = temp
}

func (lca IndirectionLca) query(a int, b int) int {
	if a > b {
		swap(&a, &b)
	}
	chunkA := a / lca.chunkSize
	chunkB := b / lca.chunkSize

	// Case 1: same chunk
	if chunkA == chunkB {
		chunkIndex := lca.chunks[chunkA].query(a%lca.chunkSize, b%lca.chunkSize)
		return lca.chunkSize*chunkA + chunkIndex
	}

	// Case 2: different chunks
	minimumStart := lca.chunkSize*chunkA + lca.chunks[chunkA].query(a%lca.chunkSize, lca.chunkSize-1)
	minimumEnd := lca.chunkSize*chunkB + lca.chunks[chunkB].query(0, b%lca.chunkSize)

	var minimumBorder int
	if lca.data[minimumStart] <= lca.data[minimumEnd] {
		minimumBorder = minimumStart
	} else {
		minimumBorder = minimumEnd
	}
	if chunkA+1 == chunkB {
		return minimumBorder
	}

	minimumMiddle := lca.chunkMinimaIndexes[lca.sparseTable.query(chunkA+1, chunkB-1)]
	if lca.data[minimumBorder] <= lca.data[minimumMiddle] {
		return minimumBorder
	} else {
		return minimumMiddle
	}
}

func main() {
	treeDescr := "ab,be,ek,el,bf,fm,mq,mr,ms,ac,cg,gn,go,ot,ad,dh,di,dj,jp"
	edges := strings.Split(treeDescr, ",")

	nodes := map[byte]*Node{}

	for _, edge := range edges {
		a := edge[0]
		b := edge[1]
		nodeA := nodes[a]
		nodeB := nodes[b]
		if nodeA == nil {
			nodeA = &Node{string(a), []*Node{}, 0, nil}
			nodes[a] = nodeA
		}
		if nodeB == nil {
			nodeB = &Node{string(b), []*Node{}, 0, nil}
			nodes[b] = nodeB
		}
		nodeA.children = append(nodes[a].children, nodes[b])
		nodeB.parent = nodeA
	}

	root := nodes[treeDescr[0]]
	computeDepths(root, 0)

	lookupTable := makeLca(root, makeLookupTableRmq)
	sparseTable := makeLca(root, makeSparseTableRmq)
	indirectionTable := makeLca(root, makeIndirectionLcaRmq)

	nodeList := NodeSlice{}
	for _, node := range nodes {
		nodeList = append(nodeList, node)
	}
	sort.Sort(nodeList)

	for _, nodeA := range nodeList {
		for _, nodeB := range nodeList {
			lcaNaive := lca(nodeA, nodeB)
			lcaLookup := lookupTable.query(nodeA, nodeB)
			lcaSparse := sparseTable.query(nodeA, nodeB)
			lcaIndirection := indirectionTable.query(nodeA, nodeB)
			if !(lcaNaive == lcaLookup && lcaLookup == lcaSparse && lcaSparse == lcaIndirection) {
				fmt.Println("error", nodeA.value, nodeB.value, lcaNaive.value, lcaLookup.value, lcaSparse.value, lcaIndirection.value)
				return
			}
		}
	}
}

type NodeSlice []*Node

func (a NodeSlice) Len() int           { return len(a) }
func (a NodeSlice) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a NodeSlice) Less(i, j int) bool { return a[i].value < a[j].value }
