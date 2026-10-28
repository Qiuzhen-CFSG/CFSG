module

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic

/-!
# An order-two image moves at most one interval of a filtration

If [D : D ∩ V] ≤ 2, a subgroup of D containing D ∩ V and an element outside V
is all of D. Thus a monotone subgroup filtration above V has at most one step
containing an element of D absent from the preceding term. This uses ordinary
subgroup indices and does not assume the filtration's whole quotient is abelian.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
last paragraph of 13.8.28, printed p.966. BinarySections supplies the movement
witnesses from the actual simple two-core quotient.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem small_relative_index_separates (V D X : Subgroup G)
    (hVX : V ⊓ D ≤ X) (hXD : X ≤ D) (hindex : V.relIndex D ≤ 2)
    (hw : ∃ x ∈ X, x ∉ V) : D ≤ X := by
  have hmul := relIndex_mul_relIndex (V ⊓ D) X D hVX hXD
  rw [inf_relIndex_right] at hmul
  have hfirst : (V ⊓ D).relIndex X ≠ 1 := by
    intro he
    obtain ⟨x, hx, hn⟩ := hw
    exact hn ((relIndex_eq_one.mp he hx).1)
  have hn₁ : (V ⊓ D).relIndex X ≠ 0 := ((V ⊓ D).subgroupOf X).index_ne_zero_of_finite
  have hn₂ : X.relIndex D ≠ 0 := (X.subgroupOf D).index_ne_zero_of_finite
  have hfirst' : 2 ≤ (V ⊓ D).relIndex X := by omega
  have hsecond : 1 ≤ X.relIndex D := by omega
  have he : X.relIndex D = 1 := by nlinarith
  exact relIndex_eq_one.mp he
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem small_relative_index_moving_steps {n : ℕ}
    (s : Fin (n + 1) → Subgroup G) (hmono : Monotone s) (V D : Subgroup G)
    (hV : V ≤ s 0) (hindex : V.relIndex D ≤ 2) (P : Fin n → Prop)
    (hm : ∀ i, P i → ∃ x ∈ D, x ∈ s i.succ ∧ x ∉ s i.castSucc) :
    Nat.card {i // P i} ≤ 1 := by
  apply Finite.card_le_one_iff_subsingleton.mpr
  refine ⟨fun i j => Subtype.ext ?_⟩
  suffices hh : ∀ i j : Fin n, P i → P j → ¬ i < j by
    have hij := hh i j i.property j.property
    have hji := hh j i j.property i.property
    exact le_antisymm (not_lt.mp hji) (not_lt.mp hij)
  intro i j hi hj hij
  obtain ⟨x, hxD, hxS, hnx⟩ := hm i hi
  have hiV : V ≤ s i.castSucc := hV.trans (hmono (Fin.zero_le _))
  have hijS : s i.succ ≤ s j.castSucc := hmono (by simpa using hij)
  have hD : D ≤ D ⊓ s j.castSucc := small_relative_index_separates V D
    (D ⊓ s j.castSucc) (fun z hz => ⟨hz.2, hV.trans (hmono (Fin.zero_le _)) hz.1⟩)
    inf_le_left hindex ⟨x, ⟨hxD, hijS hxS⟩, fun hx => hnx (hiV hx)⟩
  obtain ⟨y, hyD, _, hny⟩ := hm j hj
  exact hny (hD hyD).2
end Subgroup
