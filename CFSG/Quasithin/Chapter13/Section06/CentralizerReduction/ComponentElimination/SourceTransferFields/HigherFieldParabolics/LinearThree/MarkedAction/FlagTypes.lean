module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ModuleAction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers


/-!
# Preservation of both marked SL₃ flag types

The literal Tᵥ action preserves the marked upper unipotent subgroup and
therefore its normalizer, the standard Borel. The two maximal proper
Borel overgroups are exactly the point and line parabolics. An automorphism
is injective on subgroups, so it either fixes both or interchanges them.

The source Thompson commutator puts the actual component into the B.5
offender actor. The complete adequate classifier then gives repeated natural
coordinates on its canonical moved quotient, retaining the action of the
whole plus group. That action supplies a binary intertwiner. Fixed vectors
of the derived parabolics distinguish the two flags and exclude interchange,
even when the classifier's group marking has the dual orientation.

The final theorem discharges the repeated-natural premise of ModuleAction
from the source hypotheses, inheriting elementary abelianness of W_K from
Uᵥ. Only the universal adequate B.5 classification implication remains an
explicit earlier-source input; no flag-normalization or module premise is
assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the B.5.6
application before 13.6.14 and the parabolic argument in 13.6.19,
printed pp.929–931.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection Matrix.PSL3.LinearThree

private theorem coatom_image_eq_or {F : Type*} [Field F] [Finite F]
    (a : MulAut SL(3, F)) (hB : (borelSL F).map a.toMonoidHom = borelSL F)
    (P : Subgroup SL(3, F)) (hP : IsCoatom P) (hBP : borelSL F ≤ P) :
    P.map a.toMonoidHom = pointParabolicSL F ∨
      P.map a.toMonoidHom = lineParabolicSL F := by
  have hm := (OrderIso.isCoatom_iff a.mapSubgroup P).mpr hP
  have hBP' : borelSL F ≤ P.map a.toMonoidHom := hB ▸ map_mono hBP
  rcases BorelOvergroups.overgroup_borelSL F _ hBP' hm.ne_top with hp | hl
  · exact Or.inl ((hm.le_iff_eq (pointParabolicSL_isCoatom F).ne_top).mp hp).symm
  · exact Or.inr ((hm.le_iff_eq (lineParabolicSL_isCoatom F).ne_top).mp hl).symm

private theorem flag_dichotomy_of_unipotent {F : Type*} [Field F] [Finite F]
    (a : MulAut SL(3, F)) (hU : (unipotentSL F).map a.toMonoidHom = unipotentSL F) :
    ((pointParabolicSL F).map a.toMonoidHom = pointParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = lineParabolicSL F) ∨
    ((pointParabolicSL F).map a.toMonoidHom = lineParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = pointParabolicSL F) := by
  have hB : (borelSL F).map a.toMonoidHom = borelSL F := by
    rw [← normalizer_unipotentSL F, map_equiv_normalizer_eq, hU]
  have hp := coatom_image_eq_or a hB _ (pointParabolicSL_isCoatom F) inf_le_left
  have hl := coatom_image_eq_or a hB _ (lineParabolicSL_isCoatom F) inf_le_right
  have hne : pointParabolicSL F ≠ lineParabolicSL F := by
    intro he
    have ht := parabolicsSL_sup_eq_top F
    rw [he, sup_idem] at ht
    exact (lineParabolicSL_isCoatom F).ne_top ht
  rcases hp with hp | hp <;> rcases hl with hl | hl
  · exact (hne (map_injective a.injective (hp.trans hl.symm))).elim
  · exact Or.inl ⟨hp, hl⟩
  · exact Or.inr ⟨hp, hl⟩
  · exact (hne (map_injective a.injective (hp.trans hl.symm))).elim

universe u
variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- Sylow marking alone gives the preserve-or-interchange dichotomy. The source
module hypotheses exclude the second alternative in `modelAction_flags`. -/
theorem modelAction_flag_dichotomy {F : Type*} [Field F] [Finite F]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) = unipotentSL F)
    (t : Tv T v) :
    ((pointParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        pointParabolicSL F ∧
      (lineParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        lineParabolicSL F) ∨
    ((pointParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        lineParabolicSL F ∧
      (lineParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        pointParabolicSL F) :=
  flag_dichotomy_of_unipotent _ (modelAction_unipotentSL K L T z v hL hz hn e hmark t)

/-- The complete adequate B.5 classifier forces the literal source action to
preserve both marked parabolics. This supplies the two action hypotheses of
`flagPreimages_normalized_of_modelAction` in the SL₃ branch of 13.6.19, without
assuming local-family membership or normalization of either preimage. -/
theorem modelAction_flags [Finite G] [IsElementaryAbelian 2 (Uv z v)]
    {𝒦 : GroupClass.{u}}
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) = unipotentSL F)
    (t : Tv T v) :
    (pointParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        pointParabolicSL F ∧
      (lineParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
        lineParabolicSL F := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  exact modelAction_flags_of_repeated_natural K L T z v hL hz hK hn e hmark
    (plus_component_repeated_natural K L T z v hL hz source hSQ hK hn hU hSyl
      hcore hF hm e) t

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
