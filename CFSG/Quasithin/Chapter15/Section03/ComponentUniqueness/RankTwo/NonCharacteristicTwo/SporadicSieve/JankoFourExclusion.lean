module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.RankTwoRadicalBounds
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CharacteristicTwo
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction

/-!
# The J₄ branch of the rank-two sporadic sieve

The full source configuration forces nine to divide the local solvable
radical. A maximal Sylow-overgroup cover identifies a maximal proper overgroup
with the literal max1, max2 or max4 carrier.
Each candidate has characteristic two, so the source maximality makes
the containment an equality. Their radical bounds then give a contradiction.
No uniqueness of the ambient embeddings or conjugacy classification is needed.

The local radical bounds for max1 and the first centralizer are proved.
The remaining model inputs are explicit: full automorphism innerness,
exhaustive maximal Sylow-overgroup coverage, and the characteristic-two and
quotient calculations for the actual max4 subgroup. The conditional theorem
below is not yet the unconditional J₄ exclusion. Its assembly owner must
supply those four existing model results; an outer two-group bound alone
cannot discharge innerness.

Source: Aschbacher--Smith, 15.3.41--42, printed p.1138, using 1.1.5(3f),
printed pp.501--503; GLS3 Table 5.3i. The second involution centralizer
is not identified with the whole Mathieu maximal subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
open Janko4.LocalStructure.RankTwoRadicalBounds
open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

attribute [local irreducible] Janko4.Cardinality.max1Subgroup

variable {X : Type*} [Group X] [Finite X]

private theorem exclude_overgroup {M Y S : Subgroup X}
    (d : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (D : Subgroup X) (hMD : M ≤ D) {A : Type*} [Group A] [Finite A]
    (e : D ≃* A) (hc : HasCharacteristicTwo A)
    (h9 : ¬ 9 ∣ Nat.card (solvableRadical A)) : False := by
  have hcD : HasCharacteristicTwo D :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hc
  have hDM : D = M := d.maximal D hMD
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcD)
  exact no_localConfiguration_of_radical_bound d
    ((MulEquiv.subgroupCongr hDM.symm).trans e) h9

/-- The source configuration is impossible in the actual J₄ carrier once
the existing exhaustive cover and the two max4 facts are supplied. -/
theorem no_localConfiguration_of_model_inputs
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    {M Y S : Subgroup X} (d : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* Janko4.Model)
    (hcover : MaximalSylowCover)
    (hc4 : HasCharacteristicTwo max4Subgroup)
    (eq4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  have hm : IsTwoLocal (M.map e.toMonoidHom) := Theory.Quasithin.isTwoLocal_map e d.twoLocal
  have hna : ¬ IsMulCommutative Janko4.Model := by
    intro h
    exact Group.IsPerfect.not_isSolvable Janko4.Model
      (IsSimpleGroup.comm_iff_isSolvable.mp (isMulCommutative_iff.mp h))
  have hproper := twoLocal_ne_top_of_nonabelian_simple hna hm
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hPM : ((P.mapSurjective he : Sylow 2 Janko4.Model) : Subgroup _) ≤
      M.map e.toMonoidHom := by
    change (P : Subgroup X).map e.toMonoidHom ≤ M.map e.toMonoidHom
    exact map_mono (hP.symm ▸ d.sylow_le)
  obtain ⟨D, hD, hMD⟩ := (eq_top_or_exists_le_coatom (M.map e.toMonoidHom)).resolve_left hproper
  let B := D.map e.symm.toMonoidHom
  have hMB : M ≤ B := by
    intro x hx
    exact ⟨e x, hMD ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  let a : B ≃* D := (e.symm.subgroupMap D).symm
  rcases hcover (P.mapSurjective he) D hD (hPM.trans hMD) with h | h | h
  · obtain ⟨f⟩ := h
    unfold CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.certifiedMathieuSubgroup at f
    exact @exclude_overgroup X _ _ M Y S d B hMB
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four).toGroup
      inferInstance (a.trans f)
      Janko4.LocalStructure.max1_twoCore_centralizer_le max1_radical_not_nine
  · obtain ⟨f⟩ := h
    exact @exclude_overgroup X _ _ M Y S d B hMB sourceSubgroup
      sourceSubgroup.toGroup inferInstance (a.trans f)
      Janko4.LocalStructure.max2_twoCore_centralizer_le max2_radical_not_nine
  · obtain ⟨f⟩ := h
    exact @exclude_overgroup X _ _ M Y S d B hMB max4Subgroup
      max4Subgroup.toGroup inferInstance (a.trans f) hc4 (max4_radical_not_nine_of_quotient eq4)

variable {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- Conditional final assembly, retaining the entire `ComponentSetup` and
inheriting simplicity and perfectness through its actual marked component.
All four additional model premises still have to be discharged. -/
theorem exclusion_of_model_inputs (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Janko4.Model)
    (hi : ∀ [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model],
      Function.Surjective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model))
    (hcover : MaximalSylowCover)
    (hc4 : HasCharacteristicTwo max4Subgroup)
    (eq4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) : False := by
  let : IsSimpleGroup (componentImage I L L) := d.simple_image
  let : IsSimpleGroup Janko4.Model := (componentModel d e).symm.isSimpleGroup
  let : IsQuasisimple L := d.component_quasisimple
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have dc : LocalConfiguration (⊤ : Subgroup (ComponentQuotient I L))
      (componentImage I L M) (componentImage I L Y) (componentImage I L S) := by
    simpa only [componentImage_eq_top_of_inner d e hi] using d.quotient_local
  exact no_localConfiguration_of_model_inputs dc (ambientModelOfInner d e hi) hcover hc4 eq4

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
