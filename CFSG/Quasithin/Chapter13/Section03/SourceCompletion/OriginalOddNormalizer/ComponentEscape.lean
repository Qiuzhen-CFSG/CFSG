module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RemainingModels
public import CFSG.Quasithin.Chapter4.Section02.Unitary.ComponentEscape

/-!
# The actual escaping component of the original odd-actor pair

Failure of uniqueness constructs the original proper C.2.8 pair. The
normalized unitary residual rules out the contained generalized-Fitting
branch, so this pair contains an escaping ordinary component with actual
central quotient J₄ or Rudvalis. The literal residual quotient, relative
Sylow and conjugated original module are retained in the same witness.

The remaining J₄ exclusion, Rudvalis flag geometry and final odd-normalizer
assembly belong to qt-d-13316-source. Only the earlier Structural1222
premise retains its final discharge at qt-theorem-d.

Source: Aschbacher–Smith C.2.13, p.148, and 4.2.12–13,4.4.6,
pp.610–612,620, in the original 13.3.16 application, pp.893–896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open ChapterA.Section02 ClassificationModels
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original odd actor selects an escaping ordinary component, retaining
the actual unitary quotient map and the common full-module marking. -/
theorem unitary_original_oddActorResidual_escaping_component (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      (Y.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
      (∃ e : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived,
        ∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
          s.quotient (QuotientGroup.mk' (pCore 2 L)
            ⟨y.val,((map_subtype_le _).trans inf_le_left) y.property⟩)) ∧
      (∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        ∃ n : SporadicName, (n = .j4 ∨ n = .ru) ∧
          Nonempty (K ⧸ center K ≃* n.Carrier)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,⟨e,he⟩,_,_,hmark⟩ :=
    unitary_original_oddActorResidual_pushingUp s A hAN hcomm hodd hAV hnot
  exact ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,⟨e,he⟩,
    hc.unitary_exists_ordinary_remaining_component hn e hlt,hmark⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
