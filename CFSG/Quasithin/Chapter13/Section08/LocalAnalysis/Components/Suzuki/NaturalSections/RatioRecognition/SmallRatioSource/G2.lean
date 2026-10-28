module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Binary
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.ActionTransport
public import Theory.Representation.G2BinaryDerivedRatios
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# Both source G₂ branches in B.4.5

Cubic recognition identifies the original component action with its natural
six-space. Ordinary even G₂ has an actual offender, transported to the given
ambient group, so complete B.4.2 applies. At the binary endpoint the faithful
ambient action embeds in G₂(2). Its image either equals the derived group,
where both ratios are 3/2, or equals the full group and has the complete marked
B.4.2 action row. Every identification uses the original component intertwiner.

Source: Aschbacher–Smith B.4.5, B.4.6 and K.3.5, printed pp.87–90,457.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
open Atlas.G2.Natural.BinaryNormalizer
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem g2_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ⧸ center L ≃* Atlas.G2.Model F.Carrier) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨M⟩ := SourceClassification.g2_natural_action h F hF e
  have hi (g : Atlas.G2.Model F.Carrier) (v : Atlas.G2.Natural.Space F.Carrier) :
      M.linearEquiv.symm (binaryG2 F g v) =
        ρ (M.groupEquiv.symm g : G) (M.linearEquiv.symm v) := by
    apply M.linearEquiv.injective
    rw [M.linearEquiv.apply_symm_apply]
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, M.groupEquiv.apply_symm_apply,
      M.linearEquiv.apply_symm_apply] using
      (M.intertwines (M.groupEquiv.symm g) (M.linearEquiv.symm v)).symm
  have hff := (isFFModule_iff_quadraticRatio_le_one (binaryG2 F)).mpr
    (Atlas.G2.NaturalOffenders.natural_quadraticRatio F.card_eq F.degree_pos).le
  have hf : IsFFModule ρ := hff.map_equivariant (binaryG2 F) ρ
    (L.subtype.comp M.groupEquiv.symm.toMonoidHom)
    (L.subtype_injective.comp M.groupEquiv.symm.injective) M.linearEquiv.symm hi
  exact SourceClassification.g2_case h hf F hF e

theorem g2_model_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {r : ℕ} (hr : 2 ≤ r) (hm : ClassificationModels.IsG2At (L ⧸ center L) (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨F,_,_,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ r by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K : BinaryField := { Carrier := F, degree := r, degree_pos := by omega, card_eq := hcard }
  exact g2_case h K (by change 1 < r; omega) e

theorem g2_binary_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* Derived) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L := by
  classical
  obtain ⟨M⟩ := SourceClassification.g2_binary_natural_action h e
  let := h.layer_normal
  obtain ⟨f,hf,hmark,haction⟩ := ambient_embedding ρ L M.groupEquiv M.linearEquiv
    M.intertwines h.faithful
  have hD : Derived ≤ f.range := by
    intro x hx
    refine ⟨M.groupEquiv.symm ⟨x,hx⟩, ?_⟩
    rw [hmark,M.groupEquiv.apply_symm_apply]
  by_cases hwhole : f.range ≤ Derived
  · have hL : L = ⊤ := by
      apply top_unique
      intro g _
      have hm := hwhole ⟨g,rfl⟩
      have he : f (M.groupEquiv.symm ⟨f g,hm⟩) = f g := by
        rw [hmark,M.groupEquiv.apply_symm_apply]
      exact (hf he) ▸ (M.groupEquiv.symm ⟨f g,hm⟩).property
    let a := ChapterK.Alternating.wholeAction hL M
    have hr := derived_ratios
    have hq : quadraticRatio ρ = 3 / 2 :=
      (ChapterK.Alternating.quadraticRatio_eq a).trans hr.1
    have hc : cubicRatio ρ = 3 / 2 :=
      (ChapterK.Alternating.cubicRatio_eq a).trans hr.2
    let a' : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
        (ρ.comp L.subtype) (g2DerivedNatural (ZMod 2)) :=
      ⟨M.groupEquiv,M.linearEquiv,M.intertwines⟩
    exact Or.inr (.g2Derived a' (M.linearEquiv.finrank_eq.trans (Atlas.G2.Natural.finrank_space _)) hq hc)
  · obtain ⟨c,hc,hcd⟩ := Set.not_subset.mp hwhole
    have htop := eq_top_of_derived_le hD hc hcd
    let E := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩
    have hi (g : Full) (v : N) : M.linearEquiv.symm (Atlas.G2.Natural.action (ZMod 2) g v) =
        ρ (E.symm g) (M.linearEquiv.symm v) := by
      apply M.linearEquiv.injective
      rw [M.linearEquiv.apply_symm_apply,haction]
      change _ = Atlas.G2.Natural.action (ZMod 2) (E (E.symm g)) (M.linearEquiv (M.linearEquiv.symm v))
      rw [E.apply_symm_apply,M.linearEquiv.apply_symm_apply]
    have hff : IsFFModule (Atlas.G2.Natural.action (ZMod 2)) :=
      ⟨_,Atlas.G2.NaturalOffenders.natural_elementary_offender (n := 1) (by norm_num) (by decide)⟩
    have hffG := hff.map_equivariant _ ρ E.symm.toMonoidHom E.symm.injective M.linearEquiv.symm hi
    exact Or.inl (SourceClassification.g2_binary_case h hffG e)
end CFSG.Quasithin.ChapterB.SmallRatioClassification
