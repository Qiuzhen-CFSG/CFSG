module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ModulePreparation
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Faithfulness of the original center action in the linear and Suzuki cases

Zero O²-fixed space on a nonzero module prevents O² from lying in the
kernel. Simplicity then kills the kernel for the large linear, Suzuki and
projective unitary models. For SL₂(2) and Sz(2), order 2ⁿr with r prime
forces a kernel either to contain O² or to be a two-group; the intrinsic
two-core quotient has no nontrivial normal two-subgroup. Thus the small
models require no false simplicity assertion or extra faithfulness input.

The actual source center is nonzero at every vertex, so these results
apply to its unchanged conjugation action. `FaithfulApplication` connects
this calculation to the moving neighbor and corrected 5.12. Special
unitary scalar kernels and the remaining Chapter 8 geometry are separate.

Source: DGS, *Groups and Graphs* (1985), 5.1(b), pp.104--105,
6.2(c), p.119, and the module applications in 8.2--8.7, pp.134--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem residual_not_le_kernel [Nontrivial W]
    (ρ : Representation (ZMod 2) D W)
    (hres : fixedSpace ρ (pResidual 2 D) = ⊥) : ¬ pResidual 2 D ≤ ρ.ker := by
  intro h
  have he : fixedSpace ρ (pResidual 2 D) = ⊤ := by
    apply top_unique
    intro v _ g
    change ρ g v = v
    rw [show ρ g = 1 from h g.property]
    rfl
  exact top_ne_bot (he.symm.trans hres)

private theorem simple_action_faithful [IsSimpleGroup D] [Nontrivial W]
    (ρ : Representation (ZMod 2) D W)
    (hres : fixedSpace ρ (pResidual 2 D) = ⊥) : Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exact (residual_not_le_kernel ρ hres (hk ▸ le_top)).elim

private theorem prime_times_two_power_action_faithful [Finite D] [Nontrivial W]
    {r n : ℕ} (hr : r.Prime) (hcard : Nat.card D = 2^n*r)
    (hcore : pCore 2 D = ⊥) (ρ : Representation (ZMod 2) D W)
    (hres : fixedSpace ρ (pResidual 2 D) = ⊥) : Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  by_cases hd : r ∣ Nat.card ρ.ker
  · have hi : ρ.ker.index ∣ 2^n := by
      apply Nat.dvd_of_mul_dvd_mul_right hr.pos
      have hm := Nat.mul_dvd_mul_right hd ρ.ker.index
      rw [ρ.ker.card_mul_index, hcard, mul_comm r ρ.ker.index] at hm
      exact hm
    have hp : IsPGroup 2 (D ⧸ ρ.ker) :=
      IsPGroup.of_card_dvd_pow (ρ.ker.index_eq_card ▸ hi)
    exact (residual_not_le_kernel ρ hres
      ((pResidual_le_iff_isPGroup_quotient 2 ρ.ker).mpr hp)).elim
  · have hc : Nat.card ρ.ker ∣ 2^n :=
      ((hr.coprime_iff_not_dvd.mpr hd).symm).dvd_of_dvd_mul_right
        (hcard ▸ ρ.ker.card_subgroup_dvd_card)
    have hk : ρ.ker ≤ pCore 2 D := le_sSup ⟨inferInstance, IsPGroup.of_card_dvd_pow hc⟩
    exact bot_unique (hk.trans hcore.le)

private theorem core_free_of_core_quotient {L : Type*} [Group L] [Finite L]
    (e : (L ⧸ pCore 2 L) ≃* D) : pCore 2 D = ⊥ := by
  rw [← pCore_map_iso 2 e, Subgroup.pCore_quotient_pCore_eq_bot, Subgroup.map_bot]

/-- Residual fixed-space vanishing proves faithfulness for every actual binary
SL₂ quotient, including the solvable field-two group. -/
theorem linear_quotient_action_faithful {F L : Type*} [Field F] [Finite F] [CharP F 2]
    [Group L] [Finite L] [Nontrivial W]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) W)
    (hres : fixedSpace ρ (pResidual 2 SL(2,F)) = ⊥) : Function.Injective ρ := by
  by_cases hn1 : n = 1
  · have hc : Nat.card SL(2,F) = 2^1*3 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, hF, hn1]
      norm_num
    exact prime_times_two_power_action_faithful (by decide) hc
      (core_free_of_core_quotient e) ρ hres
  · have hc : 4 ≤ Nat.card F := by
      rw [hF]
      exact (show 4 = 2^2 from rfl).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
    let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
    exact simple_action_faithful ρ hres

/-- Residual fixed-space vanishing proves faithfulness for every actual Suzuki
quotient, including Sz(2); its order-twenty case is not treated as simple. -/
theorem suzuki_quotient_action_faithful {L : Type*} [Group L] [Finite L] [Nontrivial W]
    (m : ℕ) (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) W)
    (hres : fixedSpace ρ (pResidual 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) = ⊥) :
    Function.Injective ρ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact prime_times_two_power_action_faithful (by decide : Nat.Prime 5)
      (show Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) = 2^2*5 from
        BenderSuzuki.MatrixGroups.suzukiZero_card)
      (core_free_of_core_quotient e) ρ hres
  · let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    exact simple_action_faithful ρ hres

/-- On a projective unitary quotient of field order at least four, the
same residual condition makes the original action faithful. -/
theorem projective_unitary_action_faithful {F : Type*} [Field F] [Finite F]
    [Nontrivial W] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) W)
    (hres : fixedSpace ρ
      (pResidual 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) = ⊥) :
    Function.Injective ρ := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hc hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let := BenderSuzuki.External.huppert_II_10_13 J (2^n) hq hc hfixed
  exact simple_action_faithful ρ hres

open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The original Sylow-center span is nontrivial at every vertex. -/
theorem source_center_nontrivial {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Nontrivial (Z (family P) v) := by
  let := finite_endpoints h
  apply (Subgroup.nontrivial_iff_ne_bot _).mpr
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [← hg, Z_translate]
  exact fun he => base_Z_ne_bot h _
    ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
