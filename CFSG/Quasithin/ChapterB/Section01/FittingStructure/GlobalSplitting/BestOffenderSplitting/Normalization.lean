module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting.Basic
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting.Normalization.LocalAction
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting.Normalization.Recognition
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting.Normalization.TwoCore
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SolvableRecognition
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SourceAction.LocalGroup

/-!
# Arbitrary best offenders and the source plane normalizers

This proves the normalization step in B.1.9 using the literal action image
of E B on W=[V,F]. The solvability, faithfulness, and subgroup maps of that
action are constructed in LocalAction, and TwoCore proves its trivial two-core.

A defining minimal offender of each Gᵢ restricts to a genuine minimal best
offender on W. It normally generates Gᵢ, whose faithful image has order six.
B.1.8 therefore identifies that image with one of its actual factors. The
image of any best offender B lies in the local offender subgroup (including
the case where B fixes W), so it normalizes that factor. Normality of E and
faithfulness of E on W then lift normalization to the original Gᵢ.

The final three theorems discharge the image two-core premises and prove that
every best offender, and hence J(G,V), normalizes every source Gᵢ. Nontriviality
of F is not needed for this normalization conclusion. The remaining direct
product assembly of B.1.9(1) belongs to the parent BestOffenderSplitting module.
Source: Aschbacher–Smith, B.1.9(1), final proof paragraph,
printed p.71 (PDF p.82), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.BestOffenderNormalization
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem minimal_image (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    (B : Subgroup G) {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAE : A ≤ planeGenerated ρ) :
    IsMinimalBestOffender (imageRepresentation ρ B)
      ((A.subgroupOf (localGroup ρ B)).map (actionHom ρ B)) := by
  have hAH : A ≤ localGroup ρ B := hAE.trans le_sup_left
  have hm := MinimalPlanes.minimal_subgroupOf ρ hA hAH
  have hn : ¬ support ρ ≤ fixedSpace (localRepresentation ρ B)
      (A.subgroupOf (localGroup ρ B)) := by
    intro hfix
    apply hA.1.1.1
    apply bot_unique
    intro a ha
    exact planeGenerated_faithful_support ρ hρ hlocal (hAE ha)
      (fun w hw => hfix hw ⟨⟨a, hAH ha⟩, ha⟩)
  have hr := hm.restricted (localRepresentation ρ B) (support ρ)
    (le_top.trans (local_support_stable ρ B)) hn
  rwa [restricted_eq_map] at hr

theorem best_image_le {B : Subgroup G} (hB : IsBestOffender ρ B) :
    (B.subgroupOf (localGroup ρ B)).map (actionHom ρ B) ≤
      offenderSubgroup (imageRepresentation ρ B) := by
  have hBH : B ≤ localGroup ρ B := le_sup_right
  have hm := hB.subgroupOf ρ hBH
  by_cases hn : support ρ ≤ fixedSpace (localRepresentation ρ B)
      (B.subgroupOf (localGroup ρ B))
  · rintro x ⟨b, hb, rfl⟩
    have he : actionHom ρ B b = 1 := by
      apply imageRepresentation_injective ρ B
      ext w
      exact hn w.property ⟨b, hb⟩
    rw [he]
    exact one_mem _
  · have hr := hm.restricted (localRepresentation ρ B) (support ρ)
      (le_top.trans (local_support_stable ρ B)) hn
    rw [restricted_eq_map] at hr
    exact hr.le_offenderSubgroup _

/-- The remaining core premise is on the literal solvable local action image. -/
theorem best_normalizes_plane_of_image_core (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {B : Subgroup G} (hB : IsBestOffender ρ B)
    (himage : pCore 2 (actionImage ρ B) = ⊥)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    B ≤ normalizer (planeGroup ρ X : Set G) := by
  obtain ⟨A, hA, hn, hXA⟩ := hX
  have hX' : X ∈ minimalMovedFactors ρ := ⟨A, hA, hn, hXA⟩
  have hK : MinimalPlanes.localGroup A = planeGroup ρ X := by
    rw [planeGroup_eq_local ρ hρ hlocal ⟨hA, hn, hXA.symm⟩, hXA]
    rfl
  have hKE : MinimalPlanes.localGroup A ≤ planeGenerated ρ :=
    hK ▸ planeGroup_le_planeGenerated ρ hX'
  have hKH : MinimalPlanes.localGroup A ≤ localGroup ρ B := hKE.trans le_sup_left
  let f : MinimalPlanes.localGroup A →* actionImage ρ B :=
    (actionHom ρ B).comp (inclusion hKH)
  have hfi : Function.Injective f := by
    intro x y he
    have hh := actionHom_eq_of_mem_planeGenerated ρ hρ hlocal B
      (inclusion hKH x) (inclusion hKH y) (hKE x.property) (hKE y.property) he
    exact (inclusion_injective hKH) hh
  have hcard : Nat.card (MinimalPlanes.localGroup A) = 6 := by
    rw [hK]
    exact planeGroup_card ρ hρ hlocal hX'
  have hAE : A ≤ planeGenerated ρ :=
    (show A ≤ MinimalPlanes.localGroup A from le_sup_right).trans hKE
  have hmap : (MinimalPlanes.localActor A).map f =
      (A.subgroupOf (localGroup ρ B)).map (actionHom ρ B) := by
    rw [show f = (actionHom ρ B).comp (inclusion hKH) from rfl, ← map_map]
    congr 1
    ext a
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro ha
      exact ⟨⟨a, (show A ≤ MinimalPlanes.localGroup A from le_sup_right) ha⟩, ha, rfl⟩
  have hmin : IsMinimalBestOffender (imageRepresentation ρ B)
      ((MinimalPlanes.localActor A).map f) := by
    rw [hmap]
    exact minimal_image ρ hρ hlocal B hA hAE
  have hN := offenderSubgroup_normalizes_six_image (imageRepresentation ρ B)
    (actionImage_solvable ρ hρ hlocal hB.1) himage (imageRepresentation_injective ρ B)
    f hfi hcard (MinimalPlanes.localActor A)
    (MinimalPlanes.localActor_normally_generates hcore hA.1.1) hmin
  apply le_normalizer_iff.mpr
  intro b hb x hx
  let bH : localGroup ρ B := ⟨b, (show B ≤ localGroup ρ B from le_sup_right) hb⟩
  let xK : MinimalPlanes.localGroup A := ⟨x, hK.symm ▸ hx⟩
  have hbJ : actionHom ρ B bH ∈ offenderSubgroup (imageRepresentation ρ B) :=
    best_image_le ρ hB (mem_map_of_mem (actionHom ρ B) hb)
  have hm : actionHom ρ B bH * f xK * (actionHom ρ B bH)⁻¹ ∈ f.range :=
    (mem_normalizer_iff.mp (hN hbJ) (f xK)).mp ⟨xK, rfl⟩
  obtain ⟨k, hk⟩ := hm
  have hyE : b * x * b⁻¹ ∈ planeGenerated ρ :=
    (planeGenerated_normal ρ).conj_mem x (hKE xK.property) b
  let yH : localGroup ρ B := bH * inclusion hKH xK * bH⁻¹
  have he : actionHom ρ B (inclusion hKH k) = actionHom ρ B yH := by
    simpa only [yH, f, MonoidHom.comp_apply, map_mul, map_inv] using hk
  have he' := actionHom_eq_of_mem_planeGenerated ρ hρ hlocal B
    (inclusion hKH k) yH (hKE k.property) hyE he
  have hkg : (k : G) = b * x * b⁻¹ := congrArg Subtype.val he'
  rw [← hkg]
  exact hK ▸ k.property

/-- Once the local core calculation is supplied for each best offender, the
whole offender subgroup normalizes every source plane group. -/
theorem offenderSubgroup_normalizes_planes_of_image_cores (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    (himages : ∀ B, IsBestOffender ρ B → pCore 2 (actionImage ρ B) = ⊥)
    (i : Fin (cubicCount ρ)) :
    offenderSubgroup ρ ≤ normalizer (planeGroup ρ (cubicFactor ρ i) : Set G) := by
  exact iSup_le fun B => iSup_le fun hB =>
    best_normalizes_plane_of_image_core ρ hρ hcore hlocal hB.1 (himages B hB.1)
      (cubicFactor_mem ρ i)

/-- Every best offender normalizes the actual source group associated with
a minimal moved factor. The local image's two-core premise is discharged. -/
theorem best_normalizes_plane (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {B : Subgroup G} (hB : IsBestOffender ρ B)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    B ≤ normalizer (planeGroup ρ X : Set G) :=
  best_normalizes_plane_of_image_core ρ hρ hcore hlocal hB
    (actionImage_twoCore_eq_bot ρ hρ hcore hlocal B) hX

/-- The normalization conclusion for each literally indexed source Gᵢ. -/
theorem best_normalizes_cubic_plane (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {B : Subgroup G} (hB : IsBestOffender ρ B) (i : Fin (cubicCount ρ)) :
    B ≤ normalizer (planeGroup ρ (cubicFactor ρ i) : Set G) :=
  best_normalizes_plane ρ hρ hcore hlocal hB (cubicFactor_mem ρ i)

/-- J(G,V) normalizes every source Gᵢ, as required in the final paragraph
of the proof of B.1.9(1). No local image-core hypothesis remains. -/
theorem offenderSubgroup_normalizes_planes (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    (i : Fin (cubicCount ρ)) :
    offenderSubgroup ρ ≤ normalizer (planeGroup ρ (cubicFactor ρ i) : Set G) :=
  offenderSubgroup_normalizes_planes_of_image_cores ρ hρ hcore hlocal
    (fun B _ => actionImage_twoCore_eq_bot ρ hρ hcore hlocal B) i

end CFSG.Quasithin.ChapterB.FittingStructure.BestOffenderNormalization
