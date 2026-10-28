module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Concrete parabolic comparisons for 14.7.68

The full point and plane stabilizers in SL₃(F) surject onto Fˣ. The normal
perfect subgroup supplied by the local construction dies in this quotient,
so Fˣ would be a two-group. For |F|=2ⁿ this forces |F|=2, contradicting
the factor five in the stabilizer order. This stronger contradiction uses
the full special linear group in the literal C.2.7(g) interface.

For a proper binary five-space flag, a factor five forces one of the two
end parabolics. Its actual two-core quotient is PSL₄(2), of order 20160,
contradicting the absence of a factor seven in the local stabilizer.
For binary four-space, every proper subspace stabilizer has two-core quotient
GLᵣ(2) × GL₄₋ᵣ(2), whose order has no factor five. The actual projective flag
stabilizer embeds in its first subspace stabilizer, excluding that source case.
The isomorphisms used below identify actual stabilizer groups. Their
construction from the existential source geometry is a separate step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7(g,h),
printed pp.145–147, and 14.7.68(2), printed pp.1071–1072. Scalar maps follow
Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.LinearParabolics

open Matrix.PSL3.LinearThree
open scoped MatrixGroups Pointwise

private def pointScalar (F : Type*) [Field F] [Finite F] : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def lineScalar (F : Type*) [Field F] [Finite F] : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

private theorem pointScalar_surjective (F : Type*) [Field F] [Finite F] :
    Function.Surjective (pointScalar F).toHomUnits := by
  intro a
  refine ⟨⟨pointTorus F a, (pointTorus_mem_borel F a).1⟩, ?_⟩
  apply Units.ext
  change (pointTorus F a).val 0 0 = a.val
  simp [pointTorus]

private theorem lineScalar_surjective (F : Type*) [Field F] [Finite F] :
    Function.Surjective (lineScalar F).toHomUnits := by
  intro a
  refine ⟨⟨lineTorus F a, (lineTorus_mem_borel F a).2⟩, ?_⟩
  apply Units.ext
  change (lineTorus F a).val 2 2 = a.val
  simp [lineTorus]

private theorem card_two_of_units_two (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hu : IsPGroup 2 Fˣ) : Nat.card F = 2 := by
  obtain ⟨a, ha⟩ := hu.exists_card_eq
  have he := Nat.card_eq_card_units_add_one F
  rw [ha, hF] at he
  cases n with
  | zero => omega
  | succ n =>
    cases a with
    | zero => simpa using (hF.trans he)
    | succ a => simp only [pow_succ] at he; omega

private theorem no_five_subgroup_card_two (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) (P : Subgroup SL(3,F)) : ¬ 5 ∣ Nat.card P := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hd : Nat.card P ∣ Nat.card (GL (Fin 3) F) :=
    P.card_subgroup_dvd_card.trans
      (Subgroup.card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective)
  rw [Matrix.card_GL_field] at hd
  have hc : Fintype.card F = 2 := by simpa using hF
  norm_num [hc, Fin.prod_univ_succ] at hd
  intro h5
  have := h5.trans (show Nat.card P ∣ 168 by simpa using hd)
  norm_num at this

/-- The full SL₃ parabolic has an abelian scalar quotient incompatible with the residual. -/
theorem linearThree_false_of_coordinates {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (he : Nonempty (M ≃* pointParabolicSL F) ∨ Nonempty (M ≃* lineParabolicSL F)) :
    False := by
  have h5 := hasA5TwoResidual_dvd_card h
  rcases he with he | he
  · obtain ⟨e⟩ := he
    have hu := hasA5TwoResidual_solvable_image h ((pointScalar F).toHomUnits.comp e.toMonoidHom)
      ((pointScalar_surjective F).comp e.surjective)
    have htwo := card_two_of_units_two F hn hF hu
    apply no_five_subgroup_card_two F htwo (pointParabolicSL F)
    rwa [← Nat.card_congr e.toEquiv]
  · obtain ⟨e⟩ := he
    have hu := hasA5TwoResidual_solvable_image h ((lineScalar F).toHomUnits.comp e.toMonoidHom)
      ((lineScalar_surjective F).comp e.surjective)
    have htwo := card_two_of_units_two F hn hF hu
    apply no_five_subgroup_card_two F htwo (lineParabolicSL F)
    rwa [← Nat.card_congr e.toEquiv]

open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry

private theorem linearFour_card : Nat.card (LinearGroup 4) = 20160 := by
  rw [← Nat.card_congr (matrixEquivLinear 4).toEquiv, Matrix.card_GL_field]
  decide

/-- A proper binary five-space flag with a factor five has a quotient of order 20160. -/
theorem binaryFive_false_of_coordinates {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) (b : FiveBasis) (cuts : Set (Fin 4))
    (hproper : flagStabilizer b cuts ≠ ⊤)
    (e : M ≃* flagStabilizer b cuts) : False := by
  have h5 : 5 ∣ Nat.card (flagStabilizer b cuts) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hasA5TwoResidual_dvd_card h
  have h7 : ¬ 7 ∣ Nat.card (flagStabilizer b cuts) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hasA5TwoResidual_not_seven_dvd h
  rcases cuts_eq_singleton_end_of_five_dvd b cuts hproper h5 with rfl | rfl
  · let q := (MaximalOvergroups.lineQuotientEquiv b).trans
      (projectiveEquivLinear (by decide : 0 < 4))
    have hc : Nat.card (flagStabilizer b {0} ⧸ pCore 2 (flagStabilizer b {0})) = 20160 :=
      (Nat.card_congr q.toEquiv).trans linearFour_card
    apply h7
    exact (by decide : 7 ∣ 20160).trans (hc ▸ card_quotient_dvd_card _)
  · let q := (MaximalOvergroups.hyperplaneQuotientEquiv b).trans
      (projectiveEquivLinear (by decide : 0 < 4))
    have hc : Nat.card (flagStabilizer b {3} ⧸ pCore 2 (flagStabilizer b {3})) = 20160 :=
      (Nat.card_congr q.toEquiv).trans linearFour_card
    apply h7
    exact (by decide : 7 ∣ 20160).trans (hc ▸ card_quotient_dvd_card _)


private theorem linear_card (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

/-- A proper binary four-space subspace stabilizer has no factor five in its order. -/
theorem binaryFour_false_of_injective_coordinates {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) (W : Submodule (ZMod 2) (Space 4))
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) (e : M →* parabolic W) (he : Function.Injective e) : False := by
  let : Finite (LinearGroup 4) := Finite.of_equiv
    (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) (matrixEquivLinear 4).toEquiv
  have hdpos : 0 < Module.finrank (ZMod 2) W :=
    Nat.pos_of_ne_zero (fun hz => hW (Submodule.finrank_eq_zero.mp hz))
  have hdlt := Submodule.finrank_lt hWt
  have hqd := W.finrank_quotient_add_finrank
  simp only [Space, Module.finrank_fin_fun] at hdlt hqd
  let a : W ≃ₗ[ZMod 2] Space (Module.finrank (ZMod 2) W) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Space])
  let b : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space (4 - Module.finrank (ZMod 2) W) :=
    LinearEquiv.ofFinrankEq _ _ (by simp only [Space, Module.finrank_fin_fun]; omega)
  let q := SmallParabolicLevi.quotientTwoCoreEquivOfCoordinates W a b
  have hqc := Nat.card_congr q.toEquiv
  rw [Nat.card_prod, linear_card, linear_card] at hqc
  have hnot : ¬ 5 ∣ Nat.card (parabolic W ⧸ pCore 2 (parabolic W)) := by
    rw [hqc]
    clear hqc q a b hqd
    interval_cases hr : Module.finrank (ZMod 2) W <;> norm_num [Fin.prod_univ_succ]
  obtain ⟨s, hs⟩ := (pCore_isPGroup (p := 2) (G := parabolic W)).exists_card_eq
  have hcard := (pCore 2 (parabolic W)).card_mul_index
  rw [index_eq_card, hs] at hcard
  have h5 : 5 ∣ Nat.card (parabolic W) :=
    (hasA5TwoResidual_dvd_card h).trans (Subgroup.card_dvd_of_injective e he)
  rw [← hcard] at h5
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5 with h5 | h5
  · have := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
    norm_num at this
  · exact hnot h5

open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private noncomputable def binaryFlagHom {n k : ℕ} (hn : 0 < n)
    (f : LinearFlag (ZMod 2) n k) (i : Fin k) :
    (f.stabilizer.map (QuotientGroup.mk' (center SL(n, ZMod 2)))) →*
      BinaryLinear.parabolic (f.space i) :=
  (((projectiveEquivLinear hn).toMonoidHom).comp
    (f.stabilizer.map (QuotientGroup.mk' (center SL(n, ZMod 2)))).subtype).codRestrict _ (by
      rintro ⟨g, hg⟩
      obtain ⟨x, hx, rfl⟩ := hg
      change projectiveEquivLinear hn (QuotientGroup.mk x) ∈ _
      rw [projectiveEquivLinear_mk]
      have hm := (mem_iInf.mp hx) i
      change Matrix.SpecialLinearGroup.toLin' x ∈
        MulAction.stabilizer (LinearGroup n) (f.space i) at hm
      rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set] at hm
      exact hm)

private theorem binaryFlagHom_injective {n k : ℕ} (hn : 0 < n)
    (f : LinearFlag (ZMod 2) n k) (i : Fin k) :
    Function.Injective (binaryFlagHom hn f i) := by
  intro x y he
  apply Subtype.ext
  apply (projectiveEquivLinear hn).injective
  exact congrArg Subtype.val he

/-- Exclude the literal four-dimensional projective flag alternative, with no transport premise. -/
theorem binaryFour_false {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    (hp : IsBinaryPositiveRankParabolic P 4) : False := by
  obtain ⟨e, k, hk, _, f, he⟩ := hp
  let t := eM.trans ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he))
  let i : Fin k := ⟨0, by omega⟩
  exact binaryFour_false_of_injective_coordinates h (f.space i) (f.nonzero i) (f.proper i)
    ((binaryFlagHom (by decide : 0 < 4) f i).comp t.toMonoidHom)
    ((binaryFlagHom_injective (by decide : 0 < 4) f i).comp t.injective)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.LinearParabolics

end
