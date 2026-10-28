module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Frattini
public import CFSG.Quasithin.Chapter1.Section03.FrattiniShape
public import Theory.GroupAction.QuaternionPrimePlane

/-!
# Radical actions detected by the component Sylow image

The inverse image of the point stabilizer in the actual moved action is the
literal point centralizer. Consequently, if the image of T ∩ L ∩ C_G(u)
is Sylow in the component image, maximality makes it equal to the image of
T ∩ L. Thus T ∩ L itself centralizes u. Its established radical action
supplies both irreducibility and a faithful quaternion subgroup, on the
original odd Frattini quotient and with the original local actors.

We also expose the quaternion criterion for the other stabilizer branches:
the source radical quotient is an elementary plane, so a faithful Q₈ in
the actual centralizer action suffices. Constructing this Q₈ from a
projective four-group remains a separate step.

Source: Aschbacher--Smith, 13.1.12(1), printed pp.872--873, especially the
Sylow-image argument in the central-cover alternative of 13.1.10(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The component action retains the literal point centralizer. -/
theorem component_image_le_point_centralizer_iff
    {L A : Subgroup G} (hAL : A ≤ L) (u : normalizerMoved L) :
    (A.subgroupOf L).map (componentAction L) ≤
        ((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L) ↔
      A ≤ centralizer ({(u : G)} : Set G) := by
  constructor
  · intro hi a ha
    obtain ⟨b,hb,he⟩ := hi (mem_map.mpr
      ⟨⟨a,hAL ha⟩,ha,rfl⟩)
    have hv := congrArg (fun f : MulAut (normalizerMoved L) => (f u : G)) he
    change (b : G) * (u : G) * (b : G)⁻¹ = a * (u : G) * a⁻¹ at hv
    have hbfix : (b : G) * (u : G) * (b : G)⁻¹ = (u : G) := by
      have hbcomm : (u : G) * (b : G) = (b : G) * (u : G) :=
        mem_centralizer_iff.mp hb u (Set.mem_singleton _)
      rw [← hbcomm, mul_inv_cancel_right]
    apply mem_centralizer_iff.mpr
    intro v hvu
    obtain rfl := Set.mem_singleton_iff.mp hvu
    exact (mul_inv_eq_iff_eq_mul.mp (hv.symm.trans hbfix)).symm
  · intro h
    exact map_mono (fun a ha => h ha)

/-- The original radical has a genuine elementary Frattini plane. -/
theorem radical_frattini_plane
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    3 < p ∧ IsElementaryAbelian p (XiFrattiniQuotient (XiP p L)) ∧
      Nat.card (XiFrattiniQuotient (XiP p L)) = p ^ 2 := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  obtain ⟨hp,hs⟩ := XiP_oddQuotient_of_A36 h36 hL
    (uniqueness_local_quotient_sqtk hG hL.2.2) hn ho hd
  let : Fact (IsPGroup p (XiQuotient (XiP p L))) := ⟨hs.isPGroup⟩
  exact ⟨hp,isElementaryAbelian_quotient_frattini (p := p),hs.frattini_card⟩

/-- A quaternion subgroup in the literal centralizer image acts irreducibly
on the source plane. This criterion uses faithfulness, not nonabelianness. -/
theorem radicalCentralizerIrreducible_of_quaternion
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hQ : ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
      (XiP_invariant p inf_le_left)).range, Function.Injective f) :
    RadicalCentralizerIrreducible L p u := by
  obtain ⟨_,he,hc⟩ := radical_frattini_plane hG hL hn ho hd
  let := he
  let ρ := xiFrattiniAction
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
    (XiP_invariant p inf_le_left)
  obtain ⟨f,hf⟩ := hQ
  intro A hA
  apply QuaternionGroup.faithful_plane_irreducible ho hc
    (ρ.range.subtype.comp f) (ρ.range.subtype_injective.comp hf) A
  intro q a ha
  obtain ⟨s,hs⟩ := (f q).property
  change (f q : MulAut (XiFrattiniQuotient (XiP p L))) a ∈ A
  rw [← hs]
  exact hA s a ha

/-- If T ∩ L centralizes u, its unchanged Frattini action supplies both
the local quaternion lift and irreducibility of C_M(u). -/
theorem radical_actions_of_component_sylow_centralizes
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hcentral : (T : Subgroup G) ⊓ L ≤ centralizer ({u} : Set G)) :
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  obtain ⟨hi,hq⟩ := RadicalActions.XiP_intersection_actions_of_A36 h36 hL
    (uniqueness_local_quotient_sqtk hG hL.2.2) hn ho hd
  constructor
  · intro A hA
    apply hi A
    intro t a ha
    exact hA ⟨t,L.le_normalizer t.property.2,hcentral t.property⟩ a ha
  · let ρ := xiFrattiniAction ((T : Subgroup G) ⊓ L) (XiP p L)
      (inf_le_right.trans (XiP_invariant p L.le_normalizer))
    let τ := xiFrattiniAction (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G))
      (XiP p L) (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))
    obtain ⟨f,hf⟩ := hq
    let g := ρ.range.subtype.comp f
    have hg (x : QuaternionGroup 2) : g x ∈ τ.range := by
      obtain ⟨t,ht⟩ := (f x).property
      refine ⟨⟨t,t.property,hcentral t.property⟩,?_⟩
      change τ ⟨t,t.property,hcentral t.property⟩ = (f x).val
      rw [xiFrattiniAction_restrict inf_le_left
        (inf_le_right.trans (XiP_invariant p L.le_normalizer))]
      exact ht
    refine ⟨g.codRestrict τ.range hg,?_⟩
    intro x y hxy
    apply hf
    apply Subtype.ext
    exact congrArg (fun z : τ.range => (z : MulAut (XiFrattiniQuotient (XiP p L)))) hxy

/-- The source Sylow-image alternative gives the Q₈ lift on the literal
local intersection, and the required centralizer irreducibility. -/
theorem radical_actions_of_local_sylow_image
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (himage : IsSylowIn 2
      (((((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L)) (componentImage L)) :
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  have he := (isSylowIn_iff.mp himage).2.2
    ((((T : Subgroup G) ⊓ L).subgroupOf L).map (componentAction L))
    (((T.isPGroup'.to_le inf_le_left).comap_subtype).map (componentAction L))
    (map_mono (fun x hx => hx.1)) (map_le_range _ _)
  have hcentral : (T : Subgroup G) ⊓ L ≤ centralizer ({(u : G)} : Set G) := by
    apply (component_image_le_point_centralizer_iff inf_le_right u).mp
    rw [he]
    exact map_mono (fun x hx => hx.2)
  exact radical_actions_of_component_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd u hcentral

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
