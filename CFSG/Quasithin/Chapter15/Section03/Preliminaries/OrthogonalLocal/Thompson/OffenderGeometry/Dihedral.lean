module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson.Transfer
public import Theory.GroupTheory.WreathTwoSylowModel
public import Mathlib.Data.Finset.Powerset

/-!
# Elementary offenders in the standard orthogonal Sylow action

The standard embedded dihedral group acts on the literal four-dimensional
binary module. Its elementary subgroups are checked inside the eight-element
group: exponent two first restricts the search to the five involutions. Of
these subgroups, only the identity, either individual base transvection, and
the base four-group satisfy the offender order bound. A transvection and its
conjugate generate the base, whose fixed space has pointwise fixer equal to
the base inside this Sylow group.

The finite certificates enumerate at most 32 subsets of the involutions and
16 vectors; they do not enumerate subgroups of the full orthogonal actor.
All certificates are reduced by Lean's kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.5,
printed p.1122; the natural action is the preceding definite-plane decomposition.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OrthogonalOffenderGeometry
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
abbrev D := DihedralGroup 4
open DihedralGroup

private def baseSet : Finset D := {r 0, r 2, sr 1, sr 3}
private def involutions : Finset D := {r 2, sr 0, sr 1, sr 2, sr 3}
private def candidates : Finset (Finset D) :=
  {{r 0}, {r 0, r 2}, {r 0, sr 0}, {r 0, sr 1}, {r 0, sr 2},
    {r 0, sr 3}, {r 0, r 2, sr 0, sr 2}, baseSet}

private theorem involutions_complete : ∀ x : D, x ^ 2 = 1 → x ≠ 1 → x ∈ involutions := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem elementary_sets : ∀ s ∈ involutions.powerset,
    (∀ x ∈ insert 1 s, ∀ y ∈ insert 1 s, x * y ∈ insert 1 s) →
    insert 1 s ∈ candidates := by
  decide +kernel

private def fixedSet (s : Finset D) : Finset OrthogonalVector :=
  Finset.univ.filter (fun v => ∀ x ∈ s, wreathTwoDihedralHom x • v = v)

set_option maxRecDepth 10000 in
private theorem offender_sets : ∀ s ∈ candidates, 16 ≤ (fixedSet s).card * s.card →
    s = {r 0} ∨ s = {r 0, sr 1} ∨ s = {r 0, sr 3} ∨ s = baseSet := by
  decide +kernel

/-- The base four-group in the actual dihedral embedding. -/
def dihedralBase : Subgroup D where
  carrier x := x ∈ ({r 0, r 2, sr 1, sr 3} : Finset D)
  one_mem' := by change (1 : D) ∈ baseSet; decide +kernel
  mul_mem' := by
    have h : ∀ x ∈ baseSet, ∀ y ∈ baseSet, x * y ∈ baseSet := by decide +kernel
    intro x y hx hy
    exact h x hx y hy
  inv_mem' := by
    have h : ∀ x ∈ baseSet, x⁻¹ ∈ baseSet := by decide +kernel
    intro x hx
    exact h x hx

/-- The fixed vectors of the embedded dihedral subgroup. -/
def dihedralFixed (H : Subgroup D) : Subgroup OrthogonalVector :=
  orthogonalFixedVectors (H.map wreathTwoDihedralHom)

theorem dihedral_mem_fixed_iff (H : Subgroup D) (v : OrthogonalVector) :
    v ∈ dihedralFixed H ↔ ∀ x ∈ H, wreathTwoDihedralHom x • v = v := by
  constructor
  · intro hv x hx; exact hv _ (mem_map_of_mem _ hx)
  · rintro hv a ⟨x,hx,rfl⟩; exact hv x hx

private theorem fixed_card (H : Subgroup D) :
    Nat.card (dihedralFixed H) = (fixedSet (H : Set D).toFinite.toFinset).card := by
  classical
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_of_finset'
  intro v
  simp only [fixedSet, Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
  exact (dihedral_mem_fixed_iff H v).symm

/-- An elementary offender is trivial, a single base transvection, or the base. -/
theorem dihedral_offender (H : Subgroup D) (hexp : ∀ x ∈ H, x ^ 2 = 1)
    (hbound : 16 ≤ Nat.card (dihedralFixed H) * Nat.card H) :
    H ≤ dihedralBase ∧ (H = ⊥ ∨ sr 1 ∈ H ∨ sr 3 ∈ H) := by
  classical
  let s := (H : Set D).toFinite.toFinset
  have hmem (x : D) : x ∈ s ↔ x ∈ H := Set.Finite.mem_toFinset _
  have hOne : (1 : D) ∈ s := (hmem _).mpr H.one_mem
  have hsub : s.erase 1 ⊆ involutions := by
    intro x hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    exact involutions_complete x (hexp x ((hmem x).mp hx)) hne
  have hc := elementary_sets (s.erase 1) (Finset.mem_powerset.mpr hsub)
  rw [Finset.insert_erase hOne] at hc
  have hcan := hc (fun x hx y hy => (hmem _).mpr (H.mul_mem ((hmem _).mp hx) ((hmem _).mp hy)))
  have hcard : Nat.card H = s.card := by
    rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
    rfl
  rw [fixed_card, hcard] at hbound
  have hcases := offender_sets s hcan hbound
  have hbase (x : D) : x ∈ dihedralBase ↔ x ∈ baseSet := Iff.rfl
  rcases hcases with hs | hs | hs | hs
  · have hbot : H = ⊥ := by
      ext x
      rw [← hmem, hs]
      simp only [Finset.mem_singleton, mem_bot]
      rfl
    exact ⟨hbot ▸ bot_le, Or.inl hbot⟩
  · constructor
    · intro x hx
      rw [← hmem, hs] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact dihedralBase.one_mem
      · have hx := Finset.mem_singleton.mp hx
        subst x
        change sr 1 ∈ baseSet
        decide +kernel
    · exact Or.inr (Or.inl ((hmem _).mp (hs ▸ (by decide +kernel))))
  · constructor
    · intro x hx
      rw [← hmem, hs] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact dihedralBase.one_mem
      · have hx := Finset.mem_singleton.mp hx
        subst x
        change sr 3 ∈ baseSet
        decide +kernel
    · exact Or.inr (Or.inr ((hmem _).mp (hs ▸ (by decide +kernel))))
  · exact ⟨fun x hx => (hbase x).mpr (hs ▸ (hmem x).mpr hx),
      Or.inr (Or.inl ((hmem _).mp (hs ▸ (by decide +kernel))))⟩

/-- Either individual base transvection normally generates the base. -/
theorem dihedral_base_le (N : Subgroup D)
    (hconj : ∀ x y : D, y ∈ N → x * y * x⁻¹ ∈ N)
    (hseed : sr 1 ∈ N ∨ sr 3 ∈ N) : dihedralBase ≤ N := by
  have hswap1 : (sr 0 : D) * sr 1 * (sr 0)⁻¹ = sr 3 := by decide +kernel
  have hswap3 : (sr 0 : D) * sr 3 * (sr 0)⁻¹ = sr 1 := by decide +kernel
  have ha : sr 1 ∈ N := hseed.elim id (fun h => hswap3 ▸ hconj (sr 0) (sr 3) h)
  have hb : sr 3 ∈ N := hseed.elim (fun h => hswap1 ▸ hconj (sr 0) (sr 1) h) id
  have hab : (sr 1 : D) * sr 3 = r 2 := by decide +kernel
  intro x hx
  change x ∈ baseSet at hx
  simp only [baseSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact N.one_mem
  · exact hab ▸ N.mul_mem ha hb
  · exact ha
  · exact hb

/-- The base has order four. -/
theorem dihedral_base_card : Nat.card dihedralBase = 4 := by
  change Nat.card {x : D // x ∈ baseSet} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fixer_certificate : ∀ x : D,
    (∀ v ∈ fixedSet baseSet, wreathTwoDihedralHom x • v = v) → x ∈ baseSet := by
  decide +kernel

/-- Within the dihedral Sylow, the pointwise fixer of the base fixed space is the base. -/
theorem dihedral_fixer (x : D)
    (hx : ∀ v ∈ dihedralFixed dihedralBase, wreathTwoDihedralHom x • v = v) :
    x ∈ dihedralBase := by
  apply fixer_certificate x
  intro v hv
  apply hx v
  rw [dihedral_mem_fixed_iff]
  exact (Finset.mem_filter.mp hv).2

end CFSG.Quasithin.Chapter15.Section03.OrthogonalOffenderGeometry

end
