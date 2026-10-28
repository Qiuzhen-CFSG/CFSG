module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Bootstrap
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.NaturalModelBounds

/-!
# Same-actor best generation through the faithful image

Apply the full adequate B.5.6 classifier to the actual best-offender subgroup
of the faithful action image. The SL₃ and S₅ alternatives give a nontrivial
cubic fixing the supplied Sylow fixed space, contrary to the prime-to-three
marker centralizer. The remaining SL₂ section has no strong offenders.
Strong replacement and the odd action kernel return this bound to the original
actor. Its ordinary maximum images are therefore best and generate that same
actor.

The universal earlier-source classifier is explicit; no reduced family list,
model witness, or no-strong conclusion is assumed. Source: Aschbacher–Smith,
combined manuscript of 1 March 2004, B.1.4(4),(6), p.68; B.5.1 and B.5.6,
pp.99–105; proof of 15.3.67, pp.1153–1154.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open ChapterB.SourceInduction
universe u
variable {D W : Type u} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The full model dispatch and actual marker eliminate every strong offender
on the best-offender subgroup of the faithful image. -/
theorem image_offenderCore_not_strong_of_classification
    {K : GroupClass.{u}} (classify : AdequateClassificationInput.{u,u} K)
    (ρ : Representation (ZMod 2) D W)
    (hff : IsFFModule ρ) (hodd : Odd (Nat.card (actionHom ρ).ker))
    (hr : primeRank 3 D ≤ 1)
    (S : Sylow 2 (actionImage ρ)) (P : Submodule (ZMod 2) W)
    (hfix : P ≤ fixedSpace (imageRepresentation ρ) (S : Subgroup (actionImage ρ)))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : actionImage ρ) (v : W), v ∈ P ∧ imageRepresentation ρ g v = w} = ⊤)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤)))
    (cover : SQTKQuotient K (actionImage ρ)) :
    ¬ IsStrongFFModule ((imageRepresentation ρ).comp
      (offenderSubgroup (imageRepresentation ρ)).subtype) := by
  have hm := RankOneDispatch.image_offenderCore_model classify ρ hff hodd
    (action_kernel_coprime_three_of_marker ρ P hP) hr S P hfix hspan cover
  rcases offenderSubgroup_model_alternative (imageRepresentation ρ) hm S with hn | hc
  · exact hn
  · obtain ⟨c, hcS, hc3, hcfix⟩ := hc
    let a : subspaceKernel (imageRepresentation ρ) P ⊤ :=
      ⟨c, mem_top _, fun v hv => hcfix v (hfix hv)⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext hc3
    have ho : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes
      (image_markerCentralizer_coprime_three ρ P hP)
      (orderOf_dvd_of_pow_eq_one ha3) (orderOf_dvd_natCard a)
    have hc1 : c = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp ho)
    exact (hcS (hc1.symm ▸ S.one_mem)).elim

/-- Return the no-strong bound through the actual odd action kernel. A
hypothetical strong offender supplies nontriviality for classification. -/
theorem not_strong_of_classification_and_marker
    {K : GroupClass.{u}} (classify : AdequateClassificationInput.{u,u} K)
    (ρ : Representation (ZMod 2) D W)
    (hodd : Odd (Nat.card (actionHom ρ).ker)) (hr : primeRank 3 D ≤ 1)
    (S : Sylow 2 D) (P : Submodule (ZMod 2) W)
    (hfix : P ≤ fixedSpace ρ (S : Subgroup D))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : D) (v : W), v ∈ P ∧ ρ g v = w} = ⊤)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤)))
    (cover : SQTKQuotient K (actionImage ρ)) : ¬ IsStrongFFModule ρ := by
  intro hs
  obtain ⟨A, hA⟩ := hs
  have hff : IsFFModule ρ := ⟨A, hA.1, hA.2.le⟩
  let S' := S.mapSurjective (f := actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  have hfix' : P ≤ fixedSpace (imageRepresentation ρ) (S' : Subgroup _) := by
    change P ≤ fixedSpace (imageRepresentation ρ) (actionSubgroup ρ (S : Subgroup D))
    rw [fixedSpace_actionSubgroup]
    exact hfix
  have hspan' : Submodule.span (ZMod 2)
      {w | ∃ (g : actionImage ρ) (v : W), v ∈ P ∧ imageRepresentation ρ g v = w} = ⊤ := by
    rw [← orbit_span_comp_surjective (imageRepresentation ρ) (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective P]
    simpa only [imageRepresentation_actionHom] using hspan
  have hn := image_offenderCore_not_strong_of_classification classify ρ hff hodd hr
    S' P hfix' hspan' hP cover
  exact not_strong_of_odd_action_kernel ρ hodd
    (not_strong_of_offenderSubgroup (imageRepresentation ρ) hn) ⟨A, hA⟩

variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

/-- Best generation of the original Thompson image, retaining its kernel,
compatible Sylow and literal marker. -/
theorem thompson_image_generated_of_classification_and_marker
    {K : GroupClass.{u}} (classify : AdequateClassificationInput.{u,u} K)
    (hG : IsSQTK K G) (C : Subgroup G) (q : G →* H) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) H W)
    (hodd : Odd (Nat.card (actionHom
      (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype)).ker))
    (hr : primeRank 3 ((Stellmacher.elementaryAbelianMaxJ C).map q) ≤ 1)
    (S : Sylow 2 ((Stellmacher.elementaryAbelianMaxJ C).map q))
    (P : Submodule (ZMod 2) W)
    (hfix : P ≤ fixedSpace (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype) S)
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : (Stellmacher.elementaryAbelianMaxJ C).map q) (v : W),
        v ∈ P ∧ σ g v = w} = ⊤)
    (hP : Nat.Coprime 3 (Nat.card
      (subspaceKernel (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype) P ⊤)))
    (hordinary : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups C,
      A.map q ≠ ⊥ → IsOffender σ (A.map q)) :
    offenderSubgroup (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype) = ⊤ := by
  let I := (Stellmacher.elementaryAbelianMaxJ C).map q
  let ρ := σ.comp I.subtype
  have hn := not_strong_of_classification_and_marker classify ρ hodd hr S P hfix hspan hP
    (actionImage_sqtkCover hG q hq I σ)
  apply thompson_image_generated_of_maximum_images_best C q σ
  intro A hA hne
  have hAI : A.map q ≤ I := map_mono (le_sSup hA)
  have hb := ((hordinary A hA hne).subgroupOf σ hAI).isBest_of_not_strong ρ hn
  simpa only [map_subgroupOf_eq_of_le hAI] using hb.map_subtype σ

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
