module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Escape
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Generation
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Residual

/-!
# The genuine dimension-four MS input

Failure of the marked ambient Sylow assertion makes N_G(T₁) escape M.
The equality ⟨L_w,T⟩=LT then turns local normalizer uniqueness into MS3
for the literal pair (L_w,T₁). The residual quotient and local join
calculations supply every remaining MS clause and its actual SL₃(2)
quotient. Only the exact universal binary specialization of C.1.34 remains
explicit in the final application; no local Sylow or core callback is used.

The producer of that classification is `qt-rank-two-ms93`. The original
source Sylow contradiction and final assembly remain with
`qt-d-double-natural-pure-fusion`, under the parent
`qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith 12.1.4, printed p.790; C.1.31 and C.1.34,
printed pp.135--137.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem doubleNatural_four_pure_ms3_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      MSNoCharacteristicNormal (B.pointResidual w) (B.pointSylow w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf C hC hnormal
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hf' : ¬ Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)) (B.pointCentralizer w) :=
    he ▸ hf
  have hTN := (D.doubleNatural_pure_sylow_escape_of_many h hmany B S w hw hp hfix hf').1
  rw [← he] at hTN
  have hrestrict := D.doubleNatural_pure_characteristic_normal_restriction_of_many
    h hmany B S w hw hp hfix hf'
  rw [← he] at hrestrict
  apply hrestrict C hC
  have hCR : C.map (B.pointSylow w).subtype ≤ B.pointSylow w := map_subtype_le C
  have hCJ : C.map (B.pointSylow w).subtype ≤ B.pointResidual w ⊔ B.pointSylow w :=
    hCR.trans le_sup_right
  have hn := (normal_subgroupOf_iff_le_normalizer hCJ).mp hnormal
  have hCL : C.map (B.pointSylow w).subtype ≤ L ⊔ (T : Subgroup G) :=
    hCR.trans (inf_le_left.trans le_sup_right)
  apply (normal_subgroupOf_iff_le_normalizer hCL).mpr
  rw [← S.four_pure_residual_sup_sylow D.sylow_normalizes_component w hw hp]
  let := hC
  exact sup_le (le_sup_left.trans hn)
    (hTN.trans (normalizer_le_normalizer_characteristic_image (B.pointSylow w) C))

private theorem smallRankTwo_of_binary_quotient (X : Type*) [Group X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    SmallRankTwoQuotient X := by
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  let a := (centralPreimageQuotientEquiv (pCore 2 X)).trans
    ((QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro x hx
        exact ⟨e.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,e.apply_symm_apply x⟩)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3))).trans
        QuotientGroup.quotientBot))
  exact Or.inl ⟨a.trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

theorem doubleNatural_four_pure_smallMSPair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w) ∧
        Nonempty ((B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointResidual w ⊔ B.pointSylow w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hsq,hfit,hcomp,_,hs,hr,hprod⟩ :=
    D.doubleNatural_pure_residual_join_clauses_of_many h hmany B S w hw hp hfix
  obtain ⟨a⟩ := S.pureResidual_quotient_projective w hw hp
  let e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    a.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3))
  exact ⟨⟨inferInstance,hsq,hfit,hprod,hcomp,smallRankTwo_of_binary_quotient _ e,hr,
    D.doubleNatural_four_pure_ms3_of_many h hmany B S w hw hp hfix hf⟩,⟨e⟩,hs⟩

/-- The complete binary C.1.34 implication, with every section and Sylow clause. -/
@[expose] def BinaryLinearThreeMSClassification (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (X R : Subgroup J),
    SmallMSPair κ X R →
    Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ P : Subgroup J, Chapter1.IsSylowIn 2 P (X ⊔ R) → R ≤ P →
      ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives X R P 1 (ZMod 2) e

theorem doubleNatural_four_pure_ms_alternatives_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∃ e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives (B.pointResidual w) (B.pointSylow w) (B.pointSylow w)
          1 (ZMod 2) e := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hms,he,hs⟩ := D.doubleNatural_four_pure_smallMSPair_of_many h hmany B S w hw hp hfix hf
  exact classification G _ _ hms he _ hs le_rfl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
