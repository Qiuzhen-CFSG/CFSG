module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Actor
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Applicability

/-!
# Original-source applicability for nondegenerate planes

The genuine chosen-module hypotheses give E.6.1, the exact Sylow action
kernel and normalizer control for Q = O₂(LT). In every compatible full chart,
the specified cubic lifts from L itself and moves the full perpendicular
four-space, which lies in the center of this same Q.

No plane-centralizer bound or C.2 inspection conclusion is an input here.
Source: Aschbacher--Smith 13.3.12, printed pp.889--890.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source hypotheses and its selected natural module. -/
structure Context (T : Sylow 2 G) (L V : Subgroup G) [IsElementaryAbelian 2 V] where
  hypothesis : Hypothesis1331 T L
  maximal : L ∈ Chapter1.LStar G (T : Subgroup G)
  quotient : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived
  chosen : ChosenModule T L V
  structural : Structural1222.{u} KnownSimple.IsKnownSimple
  actor : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived
  coordinates : Additive V ≃ₗ[K] Atlas.G2.Natural.Space K
  equivariant : ∀ (l : inducedAutomizer V L) v,
    coordinates (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction K (actor l) (coordinates v)

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem Context.earlier_geometry (s : Context T L V) :
    Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V ∧
    (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2 ∧
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  obtain ⟨hTV,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  have hkernel := unitary_chosen_sylow_kernel s.chosen s.quotient.isSimpleGroup hTV
  have huniq := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have he := unitary_source_E61 s.hypothesis.qtke T L (normalizer (L : Set G))
    s.chosen.ne_bot (s.chosen.le_sylow.trans le_sup_right)
    (sup_le s.chosen.normalizes hTV)
    (sup_le L.le_normalizer s.chosen.sylow_normalizes_component) hkernel huniq.2
    (h12.source_chosen_TI s.structural s.chosen)
  refine ⟨he,hkernel,?_⟩
  simpa only [Section06.sylowCentralizer, hkernel] using he.normalizer_sylowCentralizer_le

theorem chosen_perpendicular_central (s : Context T L V) (E : Additive V ≃ₗ[K] W) :
    perpendicular E ≤ (center ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subtype := by
  intro x hx
  have hxV := perpendicular_le E hx
  refine ⟨⟨x,s.chosen.le_core hxV⟩,?_,rfl⟩
  exact Subgroup.mem_center_iff.mpr (fun y =>
    Subtype.ext ((s.chosen.core_centralizes y.property) x hxV).symm)

theorem Context.marked_cubic (s : Context T L V)
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (A : Subgroup G) (hAV : A ≤ V) (hA : pointCoordinateSubspace E A = plane) :
    ∃ n : normalizer (V : Set G),
      f (V.normalizerMonoidHom.rangeRestrict n) = cubic ∧
      n.val ∈ centralizer (A : Set G) ∧
      n.val ∈ L ∧
      n.val ∈ normalizer (perpendicular E : Set G) ∧
      ⁅zpowers n.val, perpendicular E⁆ = perpendicular E ∧
      perpendicular E ≤ (center ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).subtype := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect s.maximal.1
  obtain ⟨n,hnL,hn,hc,hp,hm⟩ := exists_component_cubic_lift s.chosen.normalizes
    s.actor f E he A hAV hA
  exact ⟨n,hn,hc,hnL,hp,hm,chosen_perpendicular_central s E⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
