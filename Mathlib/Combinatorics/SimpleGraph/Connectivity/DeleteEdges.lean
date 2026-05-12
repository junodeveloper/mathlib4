/-
Copyright (c) 2026 Juno Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juno Hwang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Connected components after deleting an edge

This file contains lemmas for applying component handshaking arguments after deleting a single
edge.
-/

@[expose] public section

open Sym2

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v x : V}

/-- A list of edge sets coming from cycles of `G`, pairwise edge-disjoint and covering all edges. -/
def IsCycleDecomposition [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (cycles : List (Finset (Sym2 V))) : Prop :=
  (∀ c ∈ cycles, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ c = p.edges.toFinset) ∧
    cycles.Pairwise Disjoint ∧ cycles.foldr (· ∪ ·) ∅ = G.edgeFinset

/-- If all vertices of `G` have even degree, then after deleting `s(u, v)`, any odd-degree
vertex different from `u` must be `v`. -/
theorem eq_right_of_ne_left_of_odd_degree_deleteEdges_singleton_of_forall_even_degree
    [∀ y : V, Fintype (G.neighborSet y)] (hx_ne_u : x ≠ u)
    (hx_odd : Odd ((G.deleteEdges {s(u, v)}).degree x)) (heven : ∀ y, Even (G.degree y)) :
    x = v := by
  by_contra hx_ne_v
  have hx_even : Even ((G.deleteEdges {s(u, v)}).degree x) :=
    G.even_degree_deleteEdges_singleton_of_ne hx_ne_u hx_ne_v (heven x)
  rw [← Nat.not_even_iff_odd] at hx_odd
  exact hx_odd hx_even

/-- If all vertices of `G` have even degree, then after deleting `s(u, v)`, any odd-degree
vertex different from `v` must be `u`. -/
theorem eq_left_of_ne_right_of_odd_degree_deleteEdges_singleton_of_forall_even_degree
    [∀ y : V, Fintype (G.neighborSet y)] (hx_ne_v : x ≠ v)
    (hx_odd : Odd ((G.deleteEdges {s(u, v)}).degree x)) (heven : ∀ y, Even (G.degree y)) :
    x = u := by
  by_contra hx_ne_u
  have hx_even : Even ((G.deleteEdges {s(u, v)}).degree x) :=
    G.even_degree_deleteEdges_singleton_of_ne hx_ne_u hx_ne_v (heven x)
  rw [← Nat.not_even_iff_odd] at hx_odd
  exact hx_odd hx_even

namespace ConnectedComponent

variable {G : SimpleGraph V} {u v : V}

/-- In a connected component of `G.deleteEdges {s(u, v)}` that contains `u` but not `v`, every
vertex other than `u` has even degree after deletion, provided all vertices different from both
endpoints had even degree before deletion. -/
theorem even_degree_deleteEdges_singleton_of_mem_left_of_notMem_right
    (C : (G.deleteEdges {s(u, v)}).ConnectedComponent) [∀ x : V, Fintype (G.neighborSet x)]
    (huC : u ∈ C) (hvC : v ∉ C)
    (heven : ∀ x, x ≠ u → x ≠ v → Even (G.degree x)) :
    ∀ x : C, x ≠ ⟨u, huC⟩ → Even ((G.deleteEdges {s(u, v)}).degree (x : V)) := by
  intro x hxu
  have hx_ne_u : (x : V) ≠ u := by
    intro hx
    exact hxu (Subtype.ext hx)
  have hx_ne_v : (x : V) ≠ v := by
    intro hx
    exact hvC (by simpa [hx] using x.prop)
  exact G.even_degree_deleteEdges_singleton_of_ne hx_ne_u hx_ne_v (heven x hx_ne_u hx_ne_v)

/-- If a component of `G.deleteEdges {s(u, v)}` contains `u`, and `u` had even degree before
deleting the edge `uv`, then there is another odd-degree vertex in that component after deletion. -/
theorem exists_ne_odd_degree_deleteEdges_singleton_of_mem_left_of_adj
    (C : (G.deleteEdges {s(u, v)}).ConnectedComponent) [Finite C]
    [∀ x : V, Fintype (G.neighborSet x)] (huC : u ∈ C) (hGuv : G.Adj u v)
    (hu_even : Even (G.degree u)) :
    ∃ x : C, x ≠ ⟨u, huC⟩ ∧ Odd ((G.deleteEdges {s(u, v)}).degree (x : V)) := by
  exact C.exists_ne_odd_degree_of_exists_odd_degree ⟨u, huC⟩
    (G.odd_degree_deleteEdges_singleton_of_adj hGuv hu_even)

/-- If every vertex of `G` has even degree, then deleting an edge `uv` leaves `u` and `v` in the
same connected component. -/
theorem right_mem_of_left_mem_deleteEdges_singleton_of_adj_of_forall_even_degree
    (C : (G.deleteEdges {s(u, v)}).ConnectedComponent) [Finite C]
    [∀ x : V, Fintype (G.neighborSet x)] (huC : u ∈ C) (hGuv : G.Adj u v)
    (heven : ∀ x, Even (G.degree x)) : v ∈ C := by
  by_contra hvC
  have h_others : ∀ x : C, x ≠ ⟨u, huC⟩ →
      Even ((G.deleteEdges {s(u, v)}).degree (x : V)) :=
    C.even_degree_deleteEdges_singleton_of_mem_left_of_notMem_right huC hvC
      (fun x _ _ ↦ heven x)
  have h_even_u : Even ((G.deleteEdges {s(u, v)}).degree u) :=
    C.even_degree_of_forall_ne_even_degree ⟨u, huC⟩ h_others
  have h_odd_u : Odd ((G.deleteEdges {s(u, v)}).degree u) :=
    G.odd_degree_deleteEdges_singleton_of_adj hGuv (heven u)
  rw [← Nat.not_even_iff_odd] at h_odd_u
  exact h_odd_u h_even_u

end ConnectedComponent

/-- If every vertex of `G` has even degree, then deleting an edge `uv` does not disconnect its
endpoints. -/
theorem reachable_deleteEdges_singleton_of_adj_of_forall_even_degree [Finite V]
    [∀ x : V, Fintype (G.neighborSet x)] (hGuv : G.Adj u v) (heven : ∀ x, Even (G.degree x)) :
    (G.deleteEdges {s(u, v)}).Reachable u v := by
  let C : (G.deleteEdges {s(u, v)}).ConnectedComponent :=
    (G.deleteEdges {s(u, v)}).connectedComponentMk u
  have huC : u ∈ C := ConnectedComponent.connectedComponentMk_mem
  have hvC : v ∈ C :=
    C.right_mem_of_left_mem_deleteEdges_singleton_of_adj_of_forall_even_degree huC hGuv heven
  exact C.reachable_of_mem_supp huC hvC

/-- In a finite graph in which every vertex has even degree, every edge lies on a cycle. -/
theorem exists_cycle_of_adj_of_forall_even_degree [Finite V] [∀ x : V, Fintype (G.neighborSet x)]
    (hGuv : G.Adj u v) (heven : ∀ x, Even (G.degree x)) :
    ∃ (w : V) (p : G.Walk w w), p.IsCycle ∧ s(u, v) ∈ p.edges :=
  G.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hGuv, G.reachable_deleteEdges_singleton_of_adj_of_forall_even_degree hGuv heven⟩

/-- In a finite graph in which every vertex has even degree, every edge lies on a cycle. -/
theorem exists_cycle_of_mem_edgeSet_of_forall_even_degree [Finite V]
    [∀ x : V, Fintype (G.neighborSet x)] {e : Sym2 V} (he : e ∈ G.edgeSet)
    (heven : ∀ x, Even (G.degree x)) :
    ∃ (w : V) (p : G.Walk w w), p.IsCycle ∧ e ∈ p.edges := by
  induction e using Sym2.ind with
  | h u v =>
      exact G.exists_cycle_of_adj_of_forall_even_degree (by simpa using he) heven

/-- Deleting the edges of a walk removes from a vertex's neighbor set exactly the neighbors of
that vertex in the walk's subgraph. -/
theorem neighborSet_deleteEdges_walk_edges [DecidableEq V] {u : V} (p : G.Walk u u) (x : V) :
    (G.deleteEdges p.edges.toFinset).neighborSet x =
      G.neighborSet x \ p.toSubgraph.neighborSet x := by
  ext y
  simp [Subgraph.mem_neighborSet, Walk.adj_toSubgraph_iff_mem_edges]

/-- The degree after deleting the edges of a walk is the original degree minus the degree in the
walk's subgraph. -/
theorem degree_deleteEdges_walk_edges [DecidableEq V] {u x : V} {p : G.Walk u u}
    [Fintype (G.neighborSet x)] [Fintype (p.toSubgraph.neighborSet x)] :
    (G.deleteEdges p.edges.toFinset).degree x = G.degree x - p.toSubgraph.degree x := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  rw [← Set.toFinset_card ((G.deleteEdges p.edges.toFinset).neighborSet x),
    ← Set.toFinset_card (G.neighborSet x)]
  rw [show ((G.deleteEdges p.edges.toFinset).neighborSet x).toFinset =
      (G.neighborSet x \ p.toSubgraph.neighborSet x).toFinset from Set.toFinset_inj.mpr <|
        G.neighborSet_deleteEdges_walk_edges p x]
  rw [Set.toFinset_diff]
  rw [← Subgraph.finset_card_neighborSet_eq_degree]
  exact Finset.card_sdiff_of_subset (by
    intro y hy
    exact Set.mem_toFinset.mpr (p.toSubgraph.neighborSet_subset x (Set.mem_toFinset.mp hy)))

/-- A vertex on a cycle has degree two in the cycle's subgraph. -/
theorem Walk.IsCycle.degree_toSubgraph_of_mem {u x : V} {p : G.Walk u u}
    [Fintype (p.toSubgraph.neighborSet x)] (hp : p.IsCycle) (hx : x ∈ p.support) :
    p.toSubgraph.degree x = 2 := by
  rw [Subgraph.degree]
  rw [← Nat.card_eq_fintype_card]
  exact hp.ncard_neighborSet_toSubgraph_eq_two hx

/-- A vertex outside a walk's support has degree zero in the walk's subgraph. -/
theorem Walk.degree_toSubgraph_of_notMem_support {u x : V} {p : G.Walk u u}
    [Fintype (p.toSubgraph.neighborSet x)] (hx : x ∉ p.support) :
    p.toSubgraph.degree x = 0 :=
  Subgraph.degree_of_notMem_verts (by simpa [Walk.mem_verts_toSubgraph] using hx)

/-- Deleting the edges of a cycle preserves even degree at every vertex. -/
theorem even_degree_deleteEdges_cycle_edges [DecidableEq V] {u x : V} {p : G.Walk u u}
    [Fintype (G.neighborSet x)] [Finite (p.toSubgraph.neighborSet x)] (hp : p.IsCycle)
    (hx_even : Even (G.degree x)) : Even ((G.deleteEdges p.edges.toFinset).degree x) := by
  letI : Fintype (p.toSubgraph.neighborSet x) := Fintype.ofFinite _
  rw [G.degree_deleteEdges_walk_edges (p := p) (x := x)]
  by_cases hx : x ∈ p.support
  · have hdeg : p.toSubgraph.degree x = 2 := hp.degree_toSubgraph_of_mem hx
    rw [hdeg]
    rw [Nat.even_sub]
    · simpa using hx_even
    · rw [← hdeg]
      exact p.toSubgraph.degree_le x
  · have hdeg : p.toSubgraph.degree x = 0 := p.degree_toSubgraph_of_notMem_support hx
    simp [hdeg, hx_even]

/-- Deleting the edges of a cycle preserves the property that every vertex has even degree. -/
theorem forall_even_degree_deleteEdges_cycle_edges [DecidableEq V]
    [∀ x : V, Fintype (G.neighborSet x)] {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    (heven : ∀ x, Even (G.degree x)) : ∀ x, Even ((G.deleteEdges p.edges.toFinset).degree x) := by
  intro x
  letI : Fintype (p.toSubgraph.neighborSet x) := (Walk.finite_neighborSet_toSubgraph p).fintype
  exact G.even_degree_deleteEdges_cycle_edges hp (heven x)

/-- Deleting the edges of a cycle decreases the number of edges. -/
theorem card_edgeFinset_deleteEdges_cycle_lt [DecidableEq V] [Fintype G.edgeSet]
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    (G.deleteEdges p.edges.toFinset).edgeFinset.card < G.edgeFinset.card := by
  apply G.card_edgeFinset_deleteEdges_lt p.edges.toFinset
  rcases hp.edges_toFinset_nonempty with ⟨e, he⟩
  exact ⟨e, by
    rw [Finset.mem_inter]
    exact ⟨p.edges_toFinset_subset_edgeFinset he, he⟩⟩

/-- A finite graph with all degrees even and at least one edge has a cycle whose edge deletion
strictly decreases the number of edges. -/
theorem exists_cycle_and_card_edgeFinset_deleteEdges_lt [DecidableEq V] [Finite V]
    [∀ x : V, Fintype (G.neighborSet x)] [Fintype G.edgeSet]
    (hG : G.edgeFinset.Nonempty) (heven : ∀ x, Even (G.degree x)) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧
      (G.deleteEdges p.edges.toFinset).edgeFinset.card < G.edgeFinset.card := by
  rcases hG with ⟨e, he⟩
  rw [mem_edgeFinset] at he
  rcases G.exists_cycle_of_mem_edgeSet_of_forall_even_degree he heven with ⟨u, p, hp, _⟩
  exact ⟨u, p, hp, G.card_edgeFinset_deleteEdges_cycle_lt hp⟩

/-- A finite graph with all degrees even and at least one edge has a cycle whose edge deletion
strictly decreases the number of edges and preserves even degree. -/
theorem exists_cycle_and_card_edgeFinset_deleteEdges_lt_and_forall_even_degree [DecidableEq V]
    [Finite V] [∀ x : V, Fintype (G.neighborSet x)] [Fintype G.edgeSet]
    (hG : G.edgeFinset.Nonempty) (heven : ∀ x, Even (G.degree x)) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧
      (G.deleteEdges p.edges.toFinset).edgeFinset.card < G.edgeFinset.card ∧
        ∀ x, Even ((G.deleteEdges p.edges.toFinset).degree x) := by
  rcases G.exists_cycle_and_card_edgeFinset_deleteEdges_lt hG heven with ⟨u, p, hp, hlt⟩
  exact ⟨u, p, hp, hlt, G.forall_even_degree_deleteEdges_cycle_edges hp heven⟩

/-- A finite graph in which every vertex has even degree has an edge-disjoint cycle
decomposition. -/
theorem exists_isCycleDecomposition_of_forall_even_degree [DecidableEq V] [Finite V]
    [∀ x : V, Fintype (G.neighborSet x)] [Fintype G.edgeSet]
    (heven : ∀ x, Even (G.degree x)) :
    ∃ cycles : List (Finset (Sym2 V)), G.IsCycleDecomposition cycles := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (G : SimpleGraph V) (hfin : ∀ x : V, Fintype (G.neighborSet x))
      (hfed : Fintype G.edgeSet),
      letI : ∀ x : V, Fintype (G.neighborSet x) := hfin
      letI : Fintype G.edgeSet := hfed
      G.edgeFinset.card = n → (∀ x, Even (G.degree x)) →
        ∃ cycles : List (Finset (Sym2 V)), G.IsCycleDecomposition cycles
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih G hfin hfed hcard heven
    letI : ∀ x : V, Fintype (G.neighborSet x) := hfin
    letI : Fintype G.edgeSet := hfed
    by_cases hG : G.edgeFinset.Nonempty
    · rcases G.exists_cycle_and_card_edgeFinset_deleteEdges_lt_and_forall_even_degree hG heven with
        ⟨u, p, hp, hlt, heven'⟩
      let H := G.deleteEdges p.edges.toFinset
      have hfedH : Fintype H.edgeSet := inferInstance
      have hcardH : H.edgeFinset.card = H.edgeFinset.card := rfl
      rcases ih H.edgeFinset.card (by rw [← hcard]; simpa [H] using hlt) H
          (fun x => finiteAtDeleteEdges (G := G) (v := x) (p.edges.toFinset : Set (Sym2 V)))
          hfedH hcardH (by simpa [H] using heven') with
        ⟨cycles, hcycles, hpair, hcover⟩
      refine ⟨p.edges.toFinset :: cycles, ?_, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨u, p, hp, rfl⟩
        · rcases hcycles c hc with ⟨w, q, hq, rfl⟩
          refine ⟨w, q.mapLe (G.deleteEdges_le p.edges.toFinset), hq.mapLe _, ?_⟩
          simp [q.edges_mapLe_eq_edges]
      · simp only [List.pairwise_cons]
        constructor
        · intro c hc
          rcases hcycles c hc with ⟨w, q, _hq, rfl⟩
          rw [Finset.disjoint_left]
          intro e hep heq
          have heH : e ∈ H.edgeFinset := q.edges_toFinset_subset_edgeFinset heq
          rw [edgeFinset_deleteEdges] at heH
          exact (Finset.mem_sdiff.mp heH).2 hep
        · exact hpair
      · simp only [List.foldr_cons]
        rw [hcover]
        change p.edges.toFinset ∪ H.edgeFinset = G.edgeFinset
        simp only [H, edgeFinset_deleteEdges]
        exact Finset.union_sdiff_of_subset p.edges_toFinset_subset_edgeFinset
    · refine ⟨[], ?_, ?_, ?_⟩
      · intro c hc
        simp at hc
      · simp
      · rw [Finset.not_nonempty_iff_eq_empty.mp hG]
        rfl
  have hmain : P G.edgeFinset.card := Nat.strongRecOn G.edgeFinset.card hP
  exact hmain G (fun x => inferInstance) inferInstance rfl heven

/-- In a finite graph in which every vertex has even degree, no edge is a bridge. -/
theorem not_isBridge_of_adj_of_forall_even_degree [Finite V] [∀ x : V, Fintype (G.neighborSet x)]
    (hGuv : G.Adj u v) (heven : ∀ x, Even (G.degree x)) : ¬ G.IsBridge s(u, v) := by
  intro hbr
  exact hbr.right (G.reachable_deleteEdges_singleton_of_adj_of_forall_even_degree hGuv heven)

end SimpleGraph
