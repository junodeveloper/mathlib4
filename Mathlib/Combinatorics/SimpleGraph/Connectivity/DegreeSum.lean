/-
Copyright (c) 2026 Juno Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juno Hwang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Degree-sum formula for connected components

This file contains wrappers for applying the degree-sum formula to connected components.
-/

@[expose] public section

open Finset

namespace SimpleGraph
namespace ConnectedComponent

variable {V : Type*} {G : SimpleGraph V}

/-- The number of vertices of odd degree in a connected component is even, where degrees are
computed in the original graph. -/
theorem even_card_odd_degree_vertices (C : G.ConnectedComponent) [Fintype C]
    [∀ v : C, Fintype (G.neighborSet v)] :
    Even #{v : C | Odd (G.degree (v : V))} := by
  classical
  convert C.toSimpleGraph.even_card_odd_degree_vertices using 2
  ext v
  simp only [mem_filter, mem_univ, true_and]
  letI : Fintype (C.toSimpleGraph.neighborSet v) := Subtype.fintype _
  have hd : C.toSimpleGraph.degree v = G.degree (v : V) := by
    rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
    exact Fintype.card_congr
      { toFun := fun w ↦ ⟨(w : C), w.prop⟩
        invFun := fun w ↦ ⟨⟨w, C.neighborSet_subset_supp v.prop w.prop⟩, w.prop⟩
        left_inv := by
          intro w
          ext
          rfl
        right_inv := by
          intro w
          ext
          rfl }
  exact ⟨fun h ↦ hd.symm ▸ h, fun h ↦ hd ▸ h⟩

/-- The number of vertices of odd degree in a connected component is not equal to one, where
degrees are computed in the original graph. -/
theorem card_odd_degree_vertices_ne_one (C : G.ConnectedComponent) [Fintype C]
    [∀ v : C, Fintype (G.neighborSet v)] :
    #{v : C | Odd (G.degree (v : V))} ≠ 1 := by
  intro h
  exact Nat.not_even_one (h ▸ C.even_card_odd_degree_vertices)

/-- If a vertex in a connected component has odd degree, then another vertex in the component
has odd degree, where degrees are computed in the original graph. -/
theorem exists_ne_odd_degree_of_exists_odd_degree (C : G.ConnectedComponent) [Finite C]
    [∀ v : C, Fintype (G.neighborSet v)] (v : C) (hv : Odd (G.degree (v : V))) :
    ∃ w : C, w ≠ v ∧ Odd (G.degree (w : V)) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  by_contra h
  have hfinset : ({w : C | Odd (G.degree (w : V))} : Finset C) = {v} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    refine ⟨?_, fun h_eq ↦ h_eq ▸ hv⟩
    intro hw
    by_contra hwv
    exact h ⟨w, hwv, hw⟩
  have hcard : #{w : C | Odd (G.degree (w : V))} = 1 := by
    change #({w : C | Odd (G.degree (w : V))} : Finset C) = 1
    rw [hfinset, card_singleton]
  exact C.card_odd_degree_vertices_ne_one hcard

/-- If every vertex in a connected component except `v` has even degree, then `v` also has even
degree, where degrees are computed in the original graph. -/
theorem even_degree_of_forall_ne_even_degree (C : G.ConnectedComponent) [Finite C]
    [∀ v : C, Fintype (G.neighborSet v)] (v : C)
    (h : ∀ w : C, w ≠ v → Even (G.degree (w : V))) : Even (G.degree (v : V)) := by
  by_contra hv
  rw [Nat.not_even_iff_odd] at hv
  rcases C.exists_ne_odd_degree_of_exists_odd_degree v hv with ⟨w, hwne, hwodd⟩
  rw [← Nat.not_even_iff_odd] at hwodd
  exact hwodd (h w hwne)

end ConnectedComponent
end SimpleGraph
