module
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Stellmacher.ElementaryAbelianMaxOrder
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Sylow

/-!
# The elementary Thompson subgroup of a unitary-four inner Sylow

Every nontrivial elementary inner actor on the Hermitian four-space has
fixed-space ratio at least 3/2. Thus it cannot be an offender. The maximum
elementary subgroup argument places every largest elementary subgroup of a
Sylow of the plane residual in its actual two-core; maximality gives equality.
The quotient and core coordinates are those of the projective flag model.

Source: Aschbacher–Smith F.4.29(6) and the unitary step of F.4.35,
printed pp.289,292 (`refs/quasithin.pdf`). This generalizes the inner
calculation in `UnitaryTwo/PlaneThompson`; it does not identify the inner
Sylow with an ambient Sylow containing outer automorphisms.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourThompson
open Representation.OrthogonalFourMinus.FiniteModel
local instance (m : ℕ) [NeZero m] : Algebra (ZMod 2) (fixedField m) := ZMod.algebra _ 2
local instance (m : ℕ) [NeZero m] : Module (ZMod 2) (Space m) :=
  Module.compHom (Space m) (algebraMap (ZMod 2) (fixedField m))
local notation "ρ" => Representation.SL2.BinarySmall.hermitian

private theorem hermitian_not_offender (m : ℕ) [NeZero m]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field m))) :
    ¬ IsOffender (ρ m) A := by
  intro hA
  have hlow := Representation.OrthogonalFourMinus.RankOne.inner_ratio_bound m A hA.1
  have hhigh := (actionRatio_le_one_iff (ρ m) hA.1).mpr hA.2
  have hh : (3 / 2 : ℝ≥0∞) ≤ 1 := hlow.trans hhigh
  rw [ENNReal.div_le_iff (by norm_num) (by simp)] at hh
  norm_num at hh

section Generic
variable {H D : Type*} [Group H] [Group D] [Finite H] [Finite D]

private theorem unique_maximum_of_no_offenders
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set H)) (hc : centralizer (V : Set H) ≤ V)
    (hno : ∀ A, ¬ IsOffender (Representation.NormalElementaryQuotient.representation V q hq hker) A)
    (T : Subgroup H) (hVT : V ≤ T) (A : Subgroup H)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups T) : A = V := by
  have hbot : A.map q = ⊥ := by
    by_contra hn
    exact hno _ ((CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      V q hq hker T A hVT hA hn).isOffender _)
  have hAV : A ≤ V := ((Subgroup.map_eq_bot_iff A).mp hbot).trans (hker ▸ hc)
  exact Subgroup.eq_of_le_of_card_ge hAV (hA.2.2 V hVT inferInstance)
end Generic

open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1 ≤ m)
local notation "L" => L2 m hm
local notation "Q" => pCore 2 L
local instance coreElementary : IsElementaryAbelian 2 Q :=
  L2TwoCore_elementaryAbelian m hm
local instance coreCommutative : IsMulCommutative Q :=
  IsElementaryAbelian.toIsMulCommutative (p := 2)
local instance coreCommGroup : CommGroup Q :=
  { (pCore 2 L).toGroup with mul_comm := mul_comm' }
local instance coreAddComm : AddCommGroup (Additive Q) :=
  @Additive.addCommGroup Q (coreCommGroup m hm)

private def planeQuotient : L →* Matrix.SpecialLinearGroup (Fin 2) (Field m) :=
  (L2QuotientEquivSL2 m hm).toMonoidHom.comp (QuotientGroup.mk' Q)

private theorem planeQuotient_surjective : Function.Surjective (planeQuotient m hm) :=
  (L2QuotientEquivSL2 m hm).surjective.comp (QuotientGroup.mk'_surjective Q)

private theorem planeQuotient_ker : (planeQuotient m hm).ker = Q := by
  rw [planeQuotient, MonoidHom.ker_comp_of_injective _ _
    (L2QuotientEquivSL2 m hm).injective, QuotientGroup.ker_mk']

private theorem planeCore_centralizer : centralizer (Q : Set L) = Q := by
  apply le_antisymm
  · intro g hg
    have he : MulAut.conjNormal g = (1 : MulAut Q) := by
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change g * (u : L) * g⁻¹ = u
      rw [← hg u u.property, mul_inv_cancel_right]
    have hm : g ∈ (MulAut.conjNormal : L →* MulAut Q).ker := he
    rwa [L2TwoCore_conjugation_ker] at hm
  · exact (pCore 2 L).le_centralizer

private theorem planeQuotient_ker_centralizer : (planeQuotient m hm).ker = centralizer (Q : Set L) :=
  (planeQuotient_ker m hm).trans (planeCore_centralizer m hm).symm

variable [NeZero m]

private def planeCoordinates : Additive Q ≃ₗ[ZMod 2] Space m where
  toFun x := ((L2TwoCoreEquiv m hm).symm x.toMul).toAdd
  invFun x := Additive.ofMul (L2TwoCoreEquiv m hm (Multiplicative.ofAdd x))
  left_inv x := by change (L2TwoCoreEquiv m hm) ((L2TwoCoreEquiv m hm).symm x.toMul) = x.toMul; simp
  right_inv x := by change ((L2TwoCoreEquiv m hm).symm ((L2TwoCoreEquiv m hm) _)).toAdd = x; simp
  map_add' x y := by change ((L2TwoCoreEquiv m hm).symm (x.toMul * y.toMul)).toAdd = _; rw [map_mul]; rfl
  map_smul' a x := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;> simp

local notation "α" => Representation.NormalElementaryQuotient.representation Q (planeQuotient m hm)
  (planeQuotient_surjective m hm) (planeQuotient_ker_centralizer m hm)

private theorem planeCoordinates_equivariant (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (v : Additive Q) :
    (planeCoordinates m hm) (α g v) = (ρ m) g ((planeCoordinates m hm) v) := by
  obtain ⟨g, rfl⟩ := (planeQuotient_surjective m hm) g
  have he : (α ((planeQuotient m hm) g) v).toMul = MulAut.conjNormal g v.toMul := by
    apply Subtype.ext
    exact Representation.NormalElementaryQuotient.representation_apply Q (planeQuotient m hm)
      (planeQuotient_surjective m hm) (planeQuotient_ker_centralizer m hm) g v
  change ((L2TwoCoreEquiv m hm).symm (α ((planeQuotient m hm) g) v).toMul).toAdd = _
  rw [he, L2TwoCoreEquiv_symm_conj]
  rfl

private theorem planeAction_not_offender (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field m))) : ¬ IsOffender α A := by
  intro hA
  have hm := hA.map_equivariant α (ρ m) (MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) (Field m))) Function.injective_id
    (planeCoordinates m hm) (planeCoordinates_equivariant m hm)
  exact hermitian_not_offender m A (by simpa using hm)

theorem plane_unique_maximum (T : Sylow 2 L) (A : Subgroup L)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup L)) : A = Q := by
  exact unique_maximum_of_no_offenders Q (planeQuotient m hm) (planeQuotient_surjective m hm)
    (planeQuotient_ker_centralizer m hm) (planeCore_centralizer m hm).le (planeAction_not_offender m hm)
    T (pCore_isPGroup.le_sylow_of_normal T) A hA

/-- The entire elementary Thompson subgroup is the literal plane two-core. -/
theorem plane_thompson (T : Sylow 2 L) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup L) = Q := by
  apply le_antisymm
  · exact sSup_le fun A hA => (plane_unique_maximum m hm T A hA).le
  · obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (T : Subgroup L)
    rw [← plane_unique_maximum m hm T A hA]
    exact le_sSup hA

end CFSG.Quasithin.ChapterF.UnitarySource.FourThompson
