module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.Shortness
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.Normalization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection

/-!
# Marked symplectic parabolic obstruction

The full adequate B.5 classifier supplies natural coordinates on the canonical
moved quotient. Its extending action excludes exceptional diagram automorphisms,
even when the coordinates use an arbitrary group marking. Consequently Tᵥ
normalizes both fixed literal point and plane preimages in source 13.6.19.
A.3.6 gives central kernels for their intrinsic core comparisons, and the actual
W_K action makes every moving residual non-short and hence non-block.

The final theorem packages these three claims for either published preimage.
No natural-section, diagram-preservation or central-kernel premise remains.
Movement and the C.1.26 application belong to the parent higher-field assembly;
the universal adequate B.5 and A.3.6 inputs and earlier ambient hypotheses retain
their source owners in qt-13-06-centralizer-reduction. K is never identified
with its plus quotient, and the whole W_K need not be a single natural module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.929–931.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]
variable (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
    KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
variable {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F)

include source hG hF hm hv hK hn hU hSyl hW

/-- The literal quotient conjugation preserves parabolic types by B.5.
The natural coordinates may use either exceptional graph orientation. -/
theorem source_modelAction_preservesDiagram (t : Tv T v) :
    DiagramAutomorphisms.PreservesDiagram
      (LinearThree.MarkedAction.modelAction K L T z v hL hz hn e t) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = (2 : ℕ) ^ 1 by decide).trans_lt
      (Nat.pow_lt_pow_right (by decide) hm)
  exact modelAction_preservesDiagram_of_natural K L T z v hL hz hlarge hK hn e
    (NaturalSection.source_natural_section K L T z v hL hz source hG
      hF hm hv hK hn hU hSyl hW e) t

/-- Both fixed literal preimages are normalized from the permitted source
hypotheses and containment marking, with no extra representation premise. -/
theorem source_flagPreimages_normalized
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent) :
    Tv T v ≤ normalizer (pointPreimage K L T z v hL hz e : Set G) ∧
      Tv T v ≤ normalizer (planePreimage K L T z v hL hz e : Set G) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact NaturalSection.source_flagPreimages_normalized K L T z v hL hz source hG
    hF hm hv hK hn hU hSyl hW e hmark

/-- The three marked-action inputs for either literal Sp₄ parabolic.
The independent geometry may choose either preimage and supply movement;
this theorem then supplies its normalization, central comparison kernel,
non-shortness and non-blockness for the parent's C.1.26 application. -/
theorem source_flag_obstruction
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent)
    (P : Subgroup G)
    (hP : P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G))) :
    ∃ hPK : P ≤ K,
      Tv T v ≤ normalizer (P : Set G) ∧
      Tv T v ≤ normalizer (residualIn P : Set G) ∧
      (LinearThree.LocalStructure.coreComparison K L T (residualIn P) z v hL hz
        ((map_subtype_le _).trans hPK)).ker ≤
          center (residualIn P ⧸ pCore 2 (residualIn P)) ∧
      (¬ residualIn P ≤ centralizer ({z} : Set G) →
        ¬ ChapterC.IsShort (residualIn P) ∧ ¬ ChapterC.IsBlock (residualIn P)) := by
  have hnorm := source_flagPreimages_normalized K L T z v hL hz source hG
    hF hm hv hK hn hU hSyl hW e hmark
  have hPK : P ≤ K := by
    rcases hP with h | h
    · exact h ▸ pointPreimage_le K L T z v hL hz e
    · exact (Set.mem_singleton_iff.mp h) ▸ planePreimage_le K L T z v hL hz e
  have hnP : Tv T v ≤ normalizer (P : Set G) := by
    rcases hP with h | h
    · exact h ▸ hnorm.1
    · exact (Set.mem_singleton_iff.mp h) ▸ hnorm.2
  refine ⟨hPK, hnP, LinearThree.residualIn_normalized (Tv T v) P hnP,
    source_coreComparison_ker_le_center K L T z v hL hz hG hA36 hv hK hW e
      (residualIn P) ((map_subtype_le _).trans hPK), ?_⟩
  intro hmove
  have hs := source_flag_residual_not_short hG hA36 hF hm K L T z v hv hL hz
    hK hn hU hSyl hW e P hP hmove
  exact ⟨hs, fun hb => hs hb.short⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
