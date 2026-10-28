module
public import Theory.SpecificGroups.PSL3.ScalarLiftTwoCore
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Rank-one parabolic residuals in linear-three central covers

A quasisimple cover of PSL₃ with trivial two-core is a scalar quotient of
SL₃ over the prescribed projective marking, including at field order four.
The solvable residuals of the two marked parabolic preimages are therefore
the images of the vector and covector stabilizers. The scalar projection is
injective on these locals, although it need not be injective on the cover.
Their two-core quotients are PSL₂ over the same field. A further pullback
through a two-core retains these literal quotient identifications.

The common Borel normalizes both factors, and neither lies in that Borel.
The source Cartan selection uses these results without removing a cubic
covering center or equating independently marked field degrees.
Source: Aschbacher–Smith I.1.3,5.1.10,5.2.1–2, pp.407,634,646–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.CoveredLocals
variable {F : Type*} [Field F] [Finite F]
variable {X : Type*} [Group X] [Finite X]

abbrev parabolic (F : Type*) [Field F] [Finite F] (i : Bool) : Subgroup PSL(3,F) :=
  if i then pointParabolic F else lineParabolic F
abbrev localSL (F : Type*) [Field F] (i : Bool) : Subgroup SL(3,F) :=
  if i then pointLocalSL F else lineLocalSL F
abbrev localProjective (F : Type*) [Field F] (i : Bool) : Subgroup PSL(3,F) :=
  if i then pointLocal F else lineLocal F
abbrev factor (r : X →* PSL(3,F)) (i : Bool) : Subgroup X :=
  let P := (parabolic F i).comap r
  (solvableResidual P).map P.subtype

omit [Finite F] in
private theorem scalar_local_injective (i : Bool) :
    Function.Injective ((projection F).comp (localSL F i).subtype) := by
  cases i
  · exact lineLocal_projection_injective F
  · exact pointLocal_projection_injective F

/-- Both parabolic residuals lift through the same projective marking. -/
theorem factor_scalar_image [IsQuasisimple X] (hF : 4 ≤ Nat.card F)
    (r : X →* PSL(3,F)) (hr : Function.Surjective r) (hc : pCore 2 X = ⊥) :
    ∃ k : SL(3,F) →* X, Function.Surjective k ∧ r.comp k = projection F ∧
      ∀ i, factor r i = (localSL F i).map k := by
  obtain ⟨k,hk,hkr⟩ := exists_scalar_lift_of_twoCore_eq_bot (by omega) r hr hc
  refine ⟨k,hk,hkr,?_⟩
  intro i
  cases i
  · have hh := map_solvableResidual_comap k hk ((lineParabolic F).comap r)
    rw [comap_comap,hkr,lineParabolic_comap,lineParabolicSL_residual F hF] at hh
    exact hh.symm
  · have hh := map_solvableResidual_comap k hk ((pointParabolic F).comap r)
    rw [comap_comap,hkr,pointParabolic_comap,pointParabolicSL_residual F hF] at hh
    exact hh.symm

/-- The covering center is disjoint from each lifted local factor. -/
theorem factor_projection_injective [IsQuasisimple X] (hF : 4 ≤ Nat.card F)
    (r : X →* PSL(3,F)) (hr : Function.Surjective r) (hc : pCore 2 X = ⊥) (i : Bool) :
    Function.Injective (r.comp (factor r i).subtype) := by
  obtain ⟨k,hk,hkr,hi⟩ := factor_scalar_image hF r hr hc
  intro x y hxy
  have hx := (hi i).le x.property
  have hy := (hi i).le y.property
  obtain ⟨a,ha,hax⟩ := hx
  obtain ⟨b,hb,hby⟩ := hy
  have hp : projection F a = projection F b := by
    have hh : r (k a) = r (k b) := by
      rw [hax,hby]
      exact hxy
    change (r.comp k) a = (r.comp k) b at hh
    rwa [hkr] at hh
  have hab : (⟨a,ha⟩ : localSL F i) = ⟨b,hb⟩ := scalar_local_injective i hp
  exact Subtype.ext (hax.symm.trans ((congrArg k (congrArg Subtype.val hab)).trans hby))

/-- The image is the actual standard local, not merely an abstract family tag. -/
theorem factor_image (hF : 4 ≤ Nat.card F) (r : X →* PSL(3,F))
    (hr : Function.Surjective r) (i : Bool) :
    (factor r i).map r = localProjective F i := by
  have hh := map_solvableResidual_comap r hr (parabolic F i)
  cases i
  · exact hh.trans (ParabolicResiduals.lineParabolic_residual F hF)
  · exact hh.trans (ParabolicResiduals.pointParabolic_residual F hF)

/-- The local covering projection is an isomorphism on each parabolic residual. -/
def factorEquiv [IsQuasisimple X] (hF : 4 ≤ Nat.card F)
    (r : X →* PSL(3,F)) (hr : Function.Surjective r) (hc : pCore 2 X = ⊥) (i : Bool) :
    factor r i ≃* localProjective F i :=
  (MulEquiv.ofBijective (r.subgroupMap (factor r i))
    ⟨fun _ _ h => factor_projection_injective hF r hr hc i (congrArg Subtype.val h),
      r.subgroupMap_surjective _⟩).trans (MulEquiv.subgroupCongr (factor_image hF r hr i))

omit [Finite X] in
/-- Each full parabolic, and hence the common Borel, normalizes its residual. -/
theorem borel_normalizes_factor (r : X →* PSL(3,F)) (i : Bool) :
    (borel F).comap r ≤ normalizer (factor r i : Set X) := by
  let P := (parabolic F i).comap r
  have hb : borel F ≤ parabolic F i := by
    cases i
    · exact map_mono (f := projection F) inf_le_right
    · exact map_mono (f := projection F) inf_le_left
  exact ((comap_mono hb).trans P.le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image P (solvableResidual P))

/-- Neither local factor is contained in the common flag stabilizer. -/
theorem local_not_le_borel (i : Bool) : ¬ localProjective F i ≤ borel F := by
  intro h
  cases i
  · let g := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F)
    have hg : g ∈ lineLocalSL F := by
      rw [mem_lineLocalSL_iff]
      simp [g,SpecialLinearGroup.transvection_coe]
    have hb := h (mem_map_of_mem (projection F) hg)
    have hb' : g ∈ (borel F).comap (projection F) := hb
    rw [borel_comap] at hb'
    have hz := (mem_borelSL_iff F g).mp hb'
    simpa [g,SpecialLinearGroup.transvection_coe] using hz.1
  · let g := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F)
    have hg : g ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      simp [g,SpecialLinearGroup.transvection_coe]
    have hb := h (mem_map_of_mem (projection F) hg)
    have hb' : g ∈ (borel F).comap (projection F) := hb
    rw [borel_comap] at hb'
    have hz := (mem_borelSL_iff F g).mp hb'
    simpa [g,SpecialLinearGroup.transvection_coe] using hz.2.2

/-- Both lifted factors escape the same original Borel preimage. -/
theorem factor_not_le_borel (hF : 4 ≤ Nat.card F) (r : X →* PSL(3,F))
    (hr : Function.Surjective r) (i : Bool) : ¬ factor r i ≤ (borel F).comap r := by
  intro h
  apply local_not_le_borel (F := F) i
  rw [←factor_image hF r hr i]
  exact map_le_iff_le_comap.mpr h

variable [CharP F 2]
/-- The literal parabolic residual has the original-field rank-one core quotient. -/
def factorCoreEquiv [IsQuasisimple X] (hF : 4 ≤ Nat.card F)
    (r : X →* PSL(3,F)) (hr : Function.Surjective r) (hc : pCore 2 X = ⊥) (i : Bool) :
    (factor r i ⧸ pCore 2 (factor r i)) ≃* PSL(2,F) := by
  let e := factorEquiv hF r hr hc i
  let eqr := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have eSL : (localProjective F i ⧸ pCore 2 (localProjective F i)) ≃* SL(2,F) := by
    cases i
    · exact lineLocalCoreQuotientEquiv F
    · exact pointLocalCoreQuotientEquiv F
  exact eqr.trans (eSL.trans (Theory.PSL2.sl2QuotientEquiv F))

/-- Pulling back through the two-core retains the same local quotient. -/
def twoCoreFactorEquiv [IsQuasisimple (X ⧸ pCore 2 X)] (hF : 4 ≤ Nat.card F)
    (r : (X ⧸ pCore 2 X) →* PSL(3,F)) (hr : Function.Surjective r) (i : Bool) :
    let q := r.comp (QuotientGroup.mk' (pCore 2 X))
    (factor q i ⧸ pCore 2 (factor q i)) ≃* PSL(2,F) := by
  let q0 := QuotientGroup.mk' (pCore 2 X)
  let R := factor (r.comp q0) i
  have him : R.map q0 = factor r i := by
    have hh := map_solvableResidual_comap q0 (QuotientGroup.mk'_surjective _) ((parabolic F i).comap r)
    exact hh
  let a := q0.subgroupMap R
  have hk : IsPGroup 2 a.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := MulEquiv.subgroupCongr him
  exact (a.quotientPCoreEquivOfSurjective (q0.subgroupMap_surjective R) hk).trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (factorCoreEquiv hF r hr (pCore_quotient_pCore_eq_bot 2) i))
end Matrix.PSL3.LinearThree.CoveredLocals
