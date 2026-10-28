module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongClass
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointLocal
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortNormalizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Intrinsic long-root class in the nonbinary unitary short centralizer

The singular-cone calculation characterizes this class as the nonidentity
orthogonal vectors fixed by a Sylow of the entire plane residual. This
condition is invariant under automorphisms. The orthogonal module is the
commutator of the two-core with the short centralizer, so every residual
automorphism fixing the short root preserves the same long-root class.
The Chapter6 consumer applies this to actual full-normalizer conjugation.

Source: Aschbacher–Smith F.4.42, printed pp.295–296.
-/

open Matrix Subgroup Theory.GroupTheory
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourLongClass
open GreenBook.LieModels.UnitaryFour
open SourceNormalizer.FourShortRoot SourceNormalizer.FourSingularity
variable (m : ℕ) (hm : 1 ≤ m) [NeZero m]
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "B" => localFactor F (form F σ hσ)
local notation "C" => shortCentralizer F σ hσ

private theorem singular_iff_local_sylow (X : hermitianMatrices F σ) :
    X.val.det = 0 ↔ ∃ P : Sylow 2 B,
      (P : Subgroup B) ≤ centralizer ({radicalHom F σ hσ (Multiplicative.ofAdd X)} : Set B) := by
  let q := (planeSL2Equiv m).toMonoidHom.comp (factorRestriction F (form F σ hσ))
  have hq : Function.Surjective q :=
    (planeSL2Equiv m).surjective.comp (factorRestriction_surjective F σ hσ)
  have hdet : X.val.det = 0 ↔ FiniteModel.form m (planeHermitianEquiv m X) = 0 := by
    constructor
    · intro he
      apply Subtype.ext
      change (X.val.map (planeFieldEquiv m)).det = 0
      simpa only [Matrix.det_fin_two,Matrix.map_apply,map_sub,map_mul,map_zero] using
        congrArg (planeFieldEquiv m) he
    · intro he
      have hh := congrArg Subtype.val he
      change (X.val.map (planeFieldEquiv m)).det = 0 at hh
      apply (planeFieldEquiv m).injective
      simpa only [Matrix.det_fin_two,Matrix.map_apply,map_sub,map_mul,map_zero] using hh
  have hfix (a : B) :
      FiniteModel.action m (q a) (planeHermitianEquiv m X) = planeHermitianEquiv m X ↔
        a ∈ centralizer ({radicalHom F σ hσ (Multiplicative.ofAdd X)} : Set B) := by
    have ha : FiniteModel.action m (q a) (planeHermitianEquiv m X) =
        planeHermitianEquiv m (hermitianCongruence F σ hσ
          (factorRestriction F (form F σ hσ) a) X) := by
      apply Subtype.ext
      exact planeHermitianEquiv_action_val m _ X
    rw [ha,(planeHermitianEquiv m).injective.eq_iff]
    rw [mem_centralizer_singleton_iff,←mul_inv_eq_iff_eq_mul]
    have hc : a * radicalHom F σ hσ (Multiplicative.ofAdd X) * a⁻¹ =
        radicalHom F σ hσ (Multiplicative.ofAdd (hermitianCongruence F σ hσ
          (factorRestriction F (form F σ hσ) a) X)) :=
      congrArg Subtype.val (radicalEquiv_conj F σ hσ a (Multiplicative.ofAdd X))
    rw [hc]
    exact ((radicalHom_injective F σ hσ).eq_iff.trans Multiplicative.ofAdd.injective.eq_iff).symm
  rw [hdet,singular_iff_fixed_sylow]
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hq 2 P
    refine ⟨R,fun a ha => (hfix a).mp (hP (q a) ?_)⟩
    rw [←hR]
    exact ⟨a,ha,rfl⟩
  · rintro ⟨P,hP⟩
    refine ⟨P.mapSurjective hq,?_⟩
    rintro _ ⟨a,ha,rfl⟩
    exact (hfix a).mpr (hP ha)

/-- The residual long-root class is intrinsic in the original plane group:
its elements lie in the orthogonal module and centralize an inner Sylow. -/
theorem longClass_iff (x : C) :
    IsConj (longMark F σ hσ) x ↔
      x ≠ 1 ∧ x.val ∈ orthogonalRadical F σ hσ ∧
        ∃ P : Sylow 2 B, (P : Subgroup B) ≤ centralizer ({x.val} : Set B) := by
  constructor
  · intro hx
    have hxV : x.val ∈ orthogonalRadical F σ hσ :=
      (long_normalClosure F σ hσ).le (by
        obtain ⟨a,rfl⟩ := isConj_iff.mp hx
        exact Subgroup.Normal.conj_mem (inferInstance : (normalClosure ({longMark F σ hσ} : Set C)).Normal) _
          (subset_normalClosure (Set.mem_singleton _)) a)
    obtain ⟨X,hX,he⟩ := hxV
    have hxV' : x.val ∈ orthogonalRadical F σ hσ := ⟨X,hX,he⟩
    have hxe : x = radicalIntoCentralizer F σ hσ X := Subtype.ext he.symm
    have hh := (longClass_iff_singular F σ hσ X.toAdd hX).mp (hxe ▸ hx)
    refine ⟨?_,hxV',?_⟩
    · intro hone
      have hz : longMark F σ hσ = 1 := (isConj_one_right.mp (hone ▸ hx.symm))
      have ho := longMark_order F σ hσ
      rw [hz,orderOf_one] at ho
      contradiction
    · rw [hxe]
      exact (singular_iff_local_sylow m hm X.toAdd).mp hh.2
  · rintro ⟨hx1,hxV,hP⟩
    obtain ⟨X,hX,he⟩ := hxV
    have hxe : x = radicalIntoCentralizer F σ hσ X := Subtype.ext he.symm
    rw [hxe]
    apply (longClass_iff_singular F σ hσ X.toAdd hX).mpr
    refine ⟨?_,?_⟩
    · intro hz
      apply hx1
      rw [hxe,show X = 1 from hz]
      exact map_one _
    · apply (singular_iff_local_sylow m hm X.toAdd).mpr
      rw [hxe] at hP
      exact hP

/-- Every automorphism of the original plane residual fixing the short root
preserves its entire long-root orbit in the residual centralizer. -/
theorem automorphism_preserves_longClass (hm' : 1 < m)
    (a : MulAut B) (ha : a (shortLocal F σ hσ) = shortLocal F σ hσ)
    (x : C) (hx : IsConj (longMark F σ hσ) x) :
    IsConj (longMark F σ hσ)
      (⟨a x.val, by
        apply mem_centralizer_singleton_iff.mpr
        simpa only [map_mul,ha] using
          congrArg a (mem_centralizer_singleton_iff.mp x.property)⟩ : C) := by
  have hq : 2 < Nat.card (FixedBy.subfield F σ) := by
    rw [PointLocal.fixedField_card m hm]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
  have hrad : (radical F σ hσ).map a.toMonoidHom = radical F σ hσ := by
    rw [radical_eq_twoCore,pCore_map_iso]
  have hc : (shortCentralizer F σ hσ).map a.toMonoidHom = C := by
    change (centralizer ({shortLocal F σ hσ} : Set B)).map a.toMonoidHom = _
    rw [CentralizerSmallKernelTransport.map_centralizer,ha]
    rfl
  have hV : (orthogonalRadical F σ hσ).map a.toMonoidHom =
      orthogonalRadical F σ hσ := by
    rw [orthogonal_eq_commutator F σ hσ hq,map_commutator,hrad,hc]
  obtain ⟨hx1,hxV,P,hP⟩ := (longClass_iff m hm x).mp hx
  apply (longClass_iff m hm _).mpr
  refine ⟨?_,hV ▸ mem_map_of_mem a.toMonoidHom hxV,
    P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  · intro he
    apply hx1
    apply Subtype.ext
    exact a.injective ((congrArg Subtype.val he).trans (map_one a).symm)
  · rintro _ ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a b * a x.val = a x.val * a b
    simpa only [map_mul] using congrArg a
      (mem_centralizer_singleton_iff.mp (hP hb))

end CFSG.Quasithin.ChapterF.UnitarySource.FourLongClass
