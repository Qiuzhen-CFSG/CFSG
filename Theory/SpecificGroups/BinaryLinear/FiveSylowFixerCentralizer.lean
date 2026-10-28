module
public import Theory.SpecificGroups.BinaryLinear.EndpointParabolic
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.GroupAction.InnerCentralizerCardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The centralizer of a Sylow-fixing automorphism of GL5(2)

The nonidentity pointwise Sylow fixer is inner, induced by the unique
nonidentity element of the Sylow center. The original full-flag marking
identifies its centralizer with the flag stabilizer of block sizes 1+3+1.
The actual diagonal quotient by its intrinsic two-core therefore has
order 168. The full outer group is a two-group, so the full automorphism
centralizer has order indivisible by nine as well.

This retains the supplied Sylow and involution and uses the actual flag
quotient, rather than an arbitrary parabolic containing the centralizer.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832. The binary
linear automorphism and flag calculations are cited in the imported modules.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.OuterCyclic
open SmallParabolicLevi SmallParabolicLevi.TwoNodes FiveFlagGeometry

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem endpoint_block_card (k : Fin 5) :
    Nat.card (Block (cutLabel {i : Fin 4 | i.val = 0 ∨ i.val = 3}) k) =
      (![1,3,1,0,0] : Fin 5 → ℕ) k := by
  classical
  have label : cutLabel {i : Fin 4 | i.val = 0 ∨ i.val = 3} =
      (![0,1,1,1,2] : Fin 5 → Fin 5) := by
    funext i
    apply Fin.ext
    fin_cases i <;> simp [cutLabel,
      show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
      Finset.filter_insert,Finset.filter_singleton]
  rw [label,Nat.card_eq_fintype_card]
  fin_cases k <;> simp [Block,Fintype.card_subtype,
    show (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

private theorem block_group_card (c : Fin 5 → Fin 5) (k : Fin 5) :
    Nat.card (BinaryLinear.GL (BlockSpace c k)) =
      ∏ i ∈ Finset.range (Nat.card (Block c k)), (2 ^ Nat.card (Block c k) - 2 ^ i) := by
  classical
  let e : BlockSpace c k ≃ₗ[ZMod 2] Space (Nat.card (Block c k)) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      ((Fintype.equivFin (Block c k)).trans (finCongr Nat.card_eq_fintype_card.symm)).symm
  rw [Nat.card_congr (linearGroupCongr e).toEquiv,
    ←Nat.card_congr (matrixEquivLinear _).toEquiv,Matrix.card_GL_field]
  simpa only [ZMod.card, Fintype.card_fin] using
    (Fin.prod_univ_eq_prod_range
      (fun i : ℕ => 2 ^ Nat.card (Block c k) - 2 ^ i) (Nat.card (Block c k)))

private theorem endpoint_flag_quotient_card (b : FiveBasis) :
    Nat.card (flagStabilizer b {i : Fin 4 | i.val = 0 ∨ i.val = 3} ⧸
      pCore 2 (flagStabilizer b {i : Fin 4 | i.val = 0 ∨ i.val = 3})) = 168 := by
  rw [Nat.card_congr (flagDiagonalQuotientEquiv b _).toEquiv,Nat.card_pi]
  simp_rw [block_group_card,endpoint_block_card]
  norm_num [Fin.prod_univ_succ,Finset.prod_range_succ]

private theorem not_nine_dvd_endpoint_flag (b : FiveBasis) :
    ¬ 9 ∣ Nat.card (flagStabilizer b {i : Fin 4 | i.val = 0 ∨ i.val = 3}) := by
  let C := flagStabilizer b {i : Fin 4 | i.val = 0 ∨ i.val = 3}
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  have hc := (pCore 2 C).card_mul_index
  rw [Subgroup.index_eq_card,endpoint_flag_quotient_card,hk] at hc
  intro h9
  rw [←hc] at h9
  exact (by decide : ¬ 9 ∣ 168)
    (((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_left h9)

/-- A nonidentity central Sylow element in GL5(2) has centralizer order indivisible by nine. -/
theorem not_nine_dvd_central_sylow_centralizer
    (P : Sylow 2 (LinearGroup 5)) (g : LinearGroup 5) (hg : g ∈ P)
    (hgo : orderOf g = 2) (hgc : ∀ x ∈ P, x*g = g*x) :
    ¬ 9 ∣ Nat.card (centralizer ({g} : Set (LinearGroup 5))) := by
  let Z := (center (P : Subgroup (LinearGroup 5))).map (P : Subgroup (LinearGroup 5)).subtype
  have hgZ : g ∈ Z := ⟨⟨g,hg⟩,mem_center_iff.mpr
    (fun x => Subtype.ext (hgc x x.property)),rfl⟩
  have hZ : zpowers g = Z := eq_of_le_of_card_ge (zpowers_le.mpr hgZ) (by
    rw [Nat.card_zpowers,hgo]
    rw [show Nat.card Z = Nat.card (center (P : Subgroup (LinearGroup 5))) from
      card_map_of_injective (P : Subgroup (LinearGroup 5)).subtype_injective]
    exact linear_sylow_center_card_le_two (by decide) P)
  obtain ⟨b,hb⟩ := InvariantNodeActions.sylow_eq_cutStabilizer (m := 4) P
  have he : centralizer ({g} : Set (LinearGroup 5)) =
      flagStabilizer b {i : Fin 4 | i.val = 0 ∨ i.val = 3} := by
    rw [←centralizer_closure,←zpowers_eq_closure,hZ]
    exact InvariantNodeActions.sylow_center_centralizer_eq_endCuts (by decide) P b hb
  rw [he]
  exact not_nine_dvd_endpoint_flag b

/-- The full automorphism centralizer retains at most one factor three. -/
theorem not_nine_dvd_sylow_fixer_centralizer_five
    (P : Sylow 2 (LinearGroup 5)) (a : MulAut (LinearGroup 5)) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut (LinearGroup 5)))) := by
  obtain ⟨g,hg,rfl⟩ := sylow_fixing_inner (Or.inr rfl) P a hP
  have hz : center (LinearGroup 5) = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    have hh : (slEquivLinear 5).symm g ∈ center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
      apply mem_center_iff.mpr
      intro x
      apply (slEquivLinear 5).injective
      simpa only [map_mul,MulEquiv.apply_symm_apply] using
        mem_center_iff.mp hg (slEquivLinear 5 x)
    rw [binary_center_eq_bot (by decide),mem_bot] at hh
    exact mem_bot.mpr ((slEquivLinear 5).symm.injective (hh.trans (map_one _).symm))
  have hgo : orderOf g = 2 := by
    rwa [MulAut.conj_orderOf_of_center_eq_bot hz] at ha
  have hgc : ∀ x ∈ P, x*g = g*x := by
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hP x hx)).symm
  have hnot := not_nine_dvd_central_sylow_centralizer P g hg hgo hgc
  have hd := MulAut.centralizer_conj_card_dvd hz g
  obtain ⟨k,hk⟩ := (linear_outer_isTwoGroup (Or.inr rfl : 5 = 4 ∨ 5 = 5)).exists_card_eq
  rw [hk] at hd
  intro h9
  exact hnot (((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_right (h9.trans hd))
end BinaryLinear.OuterCyclic
