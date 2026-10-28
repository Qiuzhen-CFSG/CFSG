module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.Calculation
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Normal generation in the even three-block group

A normal subgroup of the tetrahedral three-block group that interchanges
two blocks is the whole group. Its commutator with the normal four-group
first gives that four-group; the image in the three-block symmetric group
then contains every transposition.

This supplies the local action generation step in Goldschmidt (1980),
(6.12.6), without identifying an arbitrary extension of the action kernel.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricSix.SynthemeCalculation

private theorem involution_swap_or_core : ∀ σ : Equiv.Perm (Fin 4),
    σ ^ 2 = 1 → σ.IsSwap ∨ σ ∈ DuadCalculation.core := by
  unfold Equiv.Perm.IsSwap
  decide +kernel

/-- Under any identification with S₄, a block-moving involution is a
transposition. The two-cores make this independent of the chosen marking. -/
theorem symmetricFour_isSwap_of_involution_block_swap
    (e : evenModel ≃* Equiv.Perm (Fin 4)) (x : evenModel)
    (hx : x ^ 2 = 1) (hs : x.val.right.IsSwap) : (e x).IsSwap := by
  rcases involution_swap_or_core (e x) (by rw [← map_pow, hx, map_one]) with he | he
  · exact he
  exfalso
  have hm : x ∈ evenCore := by
    rw [evenCore_eq, ← pCore_map_iso 2 e.symm]
    have hh : e x ∈ pCore 2 (Equiv.Perm (Fin 4)) := DuadCalculation.core_eq ▸ he
    exact mem_map.mpr ⟨e x, hh, e.symm_apply_apply x⟩
  have hh := hs.sign_eq
  rw [show x.val.right = 1 from hm, map_one] at hh
  exact (by decide : (1 : ℤˣ) ≠ -1) hh

private theorem normal_eq_top_of_swap {α : Type*} [Finite α] [DecidableEq α]
    (N : Subgroup (Equiv.Perm α)) [N.Normal] {x : Equiv.Perm α}
    (hx : x ∈ N) (hs : x.IsSwap) : N = ⊤ := by
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap]
  apply (closure_le _).mpr
  rintro y hy
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hcd)
  exact hg ▸ Subgroup.Normal.conj_mem inferInstance _ hx g

/-- A block transposition normally generates the entire even block group. -/
theorem evenModel_normal_eq_top_of_block_swap
    (N : Subgroup evenModel) [N.Normal] {x : evenModel}
    (hx : x ∈ N) (hs : x.val.right.IsSwap) : N = ⊤ := by
  have hxcore : x ∉ evenCore := by
    intro hm
    have he : x.val.right = 1 := hm
    have hh := hs.sign_eq
    rw [he, map_one] at hh
    exact (by decide : (1 : ℤˣ) ≠ -1) hh
  have hcore : evenCore ≤ N := by
    rcases normal_subgroup_evenCore (N ⊓ evenCore) inf_le_right with he | he
    · exfalso
      apply hxcore
      rw [← centralizer_evenCore]
      apply mem_centralizer_iff.mpr
      intro y hy
      have hm : ⁅x,y⁆ ∈ N ⊓ evenCore :=
        commutator_le_inf N evenCore (commutator_mem_commutator hx hy)
      rw [he] at hm
      exact (commutatorElement_eq_one_iff_commute.mp (show ⁅x,y⁆ = 1 from hm)).symm.eq
    · rw [← he]
      exact inf_le_left
  let M := N.map evenQuotientHom
  let : M.Normal := Subgroup.Normal.map inferInstance _ evenQuotientHom_surjective
  have hM : M = ⊤ := normal_eq_top_of_swap M (mem_map_of_mem _ hx) hs
  apply top_unique
  intro g _
  have hg : evenQuotientHom g ∈ M := hM ▸ mem_top _
  obtain ⟨n, hn, he⟩ := hg
  have hk : g * n⁻¹ ∈ evenCore := by
    change evenQuotientHom (g * n⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hh := N.mul_mem (hcore hk) hn
  simpa only [inv_mul_cancel_right] using hh

end Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
