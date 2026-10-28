module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalRank
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction

/-!
# The original maximal-escape action in the unitary rank argument

The proved E.6.7 block and E.6.8 component alternatives supply a moving
element of the literal local centralizer of every maximal obstruction of
corank greater than one. Thus the original unitary rank argument requires
only the preceding nondegenerate-plane centralizer theorem as a geometric
input. Its E.6.1 configuration is built on the original chosen module,
two-core, and unique maximal two-local, without a new model or rank premise.

Source: Aschbacher--Smith E.6.11(2), printed pp.249--250, and the use in
13.3.17(2), printed p.893, in `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]

/-- The moving-element part of E.6.11(2), on the actual source configuration. -/
theorem maximalEscapeAction_of_source {T : Sylow 2 G} {M V : Subgroup G}
    (h : Section06.HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    MaximalEscapeAction V M := by
  intro U hU hmax hn
  exact Section06.maximal_escape_action_knownSimple h hU hmax hn

/-- Original 13.3.17(2) with its maximal-escape premise discharged. Only
the preceding nondegenerate-plane centralizer argument remains explicit. -/
theorem unitary_rank_gt_three_of_plane_geometry
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (hres : pResidual 2 D.L = ⊤)
    (hTL : (D.T : Subgroup G) ≤ normalizer (D.L : Set G))
    (hVLT : D.V ≤ D.LT) (hred : IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl : (D.T : Subgroup G) ⊓ centralizer (D.V : Set G) = D.LT.pCoreIn 2)
    (hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G))
    (hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → D.LT ≤ N →
      N = normalizer (D.L : Set G))
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTI : ∀ g ∈ normalizer (D.L : Set G),
      D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom = D.V)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G))) :
    (3 : ℕ∞) < globalR D.V := by
  have hLTN : D.LT ≤ normalizer (D.V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hVn : D.V ≠ ⊥ := by
    intro hv
    have hz : D.V₁ = ⊥ := le_bot_iff.mp (hv ▸ hZV)
    rw [hz, Subgroup.card_bot] at hZ
    omega
  have hE := unitary_source_E61 hG D.T D.L (normalizer (D.L : Set G)) hVn
    hVLT hLTN (sup_le D.L.le_normalizer hTL) hsyl hu hTI
  exact unitary_rank_gt_three_of_earlier_geometry D e E0 he0 hUV hZV hTZ hTU
    hZ hU hres hTL hVLT hred hsyl hNL hfaith hu B hBV hTB hB hHfull hm hG hTI
    hplanes (maximalEscapeAction_of_source hE)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
