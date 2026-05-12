/-
Copyright (c) 2026 Juno Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juno Hwang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.DegreeSum
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

/-- In a finite graph in which every vertex has even degree, no edge is a bridge. -/
theorem not_isBridge_of_adj_of_forall_even_degree [Finite V] [∀ x : V, Fintype (G.neighborSet x)]
    (hGuv : G.Adj u v) (heven : ∀ x, Even (G.degree x)) : ¬ G.IsBridge s(u, v) := by
  intro hbr
  exact hbr.right (G.reachable_deleteEdges_singleton_of_adj_of_forall_even_degree hGuv heven)

end SimpleGraph
