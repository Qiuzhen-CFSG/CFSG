module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.DerivedBranch

/-!
# The full action in the remaining unitary noncentrality case

If the original point core centralizes the plane, the component-action
branch is impossible. The genuine natural normalizer embedding then sends
LT onto all of G₂(2), since its component image is G₂(2)′ of index two.
The embedding retains the given natural coordinates and the specified
component isomorphism. Thus the remaining Baumann argument can use the
full action without assuming a new model or changing the original flag.

Source: Aschbacher--Smith13.3.10(2), pp.887--888, in13.3.14, pp.891--893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every remaining contrary source case has the full G₂(2) action,
with the original component chart and natural coordinates preserved. -/
theorem unitary_original_full_action_of_plane_centrality
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hc : ⁅D.QH,B⁆ = ⊥) :
    ∃ rho : Automizer D.V →* Atlas.G2.Model F,
      Function.Injective rho ∧
      (∀ l : inducedAutomizer D.V D.L, rho l = (e l : Atlas.G2.Model F)) ∧
      (∀ a v, E0 (automizerRepresentation D.V a v) =
        Atlas.G2.Natural.action F (rho a) (E0 v)) ∧
      (inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G))).map rho = ⊤ := by
  have hnot : ¬ inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G)) ≤
      inducedAutomizer D.V D.L := by
    intro hsmall
    exact unitary_original_noncentrality_of_component_action D h chosen hmax eL
      structural e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
      h1332 fixed five hsmall hc
  have hNL := (unitary_original_module_normalizers h hmax eL chosen structural).2
  let I := inducedAutomizer D.V D.L
  let J := inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G))
  let : (D.L.subgroupOf (normalizer (D.V : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer chosen.normalizes).mpr hNL
  let : I.Normal := Subgroup.Normal.map inferInstance D.V.normalizerMonoidHom.rangeRestrict
    D.V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨rho,hi,hl,he⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation D.V) I e E0 he0 (automizerRepresentation_injective D.V)
  have hIJ : I ≤ J := map_mono (fun _ hx => (le_sup_left : D.L ≤ D.L ⊔ (D.T : Subgroup G)) hx)
  have hd : Atlas.G2.Natural.BinaryNormalizer.Derived ≤ J.map rho := by
    intro g hg
    obtain ⟨l,hg'⟩ := e.surjective ⟨g,hg⟩
    exact ⟨l,hIJ l.property,(hl l).trans (congrArg Subtype.val hg')⟩
  have hn : ¬ J.map rho ≤ Atlas.G2.Natural.BinaryNormalizer.Derived := by
    intro hj
    apply hnot
    intro a ha
    obtain ⟨l,heq⟩ := e.surjective ⟨rho a,hj (mem_map_of_mem rho ha)⟩
    have hal : (l : Automizer D.V) = a := hi ((hl l).trans (congrArg Subtype.val heq))
    exact hal ▸ l.property
  obtain ⟨c,hcJ,hcD⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨rho,hi,hl,he,Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le hd hcJ hcD⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
