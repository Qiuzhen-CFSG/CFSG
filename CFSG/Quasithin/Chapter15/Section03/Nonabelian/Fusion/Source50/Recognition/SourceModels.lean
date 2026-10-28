module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly
public import CFSG.Quasithin.ChapterG.Section06.Chapter13Bridge
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete

/-!
# The proved G.6.4 applied to the two literal constituents of U/Z

Only the Sylow-central clause of G.6.4 is needed. The original finite SQTK
centralizer is restricted to the preimage of K*〈v〉 and then mapped onto its
faithful constituent action. The proved source theorem supplies the model
list; the existing local prime restriction selects the natural three-space.
No universal classification callback is retained.
Source: Aschbacher–Smith 15.3.58, printed p.1149, using G.6.4(4).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open Component Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open SplitBranch G64Natural NormalReduction
universe u w f
variable {A E : Type u} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [Finite E]

theorem image_central_alternative
    (ρ : Representation (ZMod 2) A E) [ρ.IsIrreducible]
    (v : A) (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 1)
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q)
    (hcover : IsSQTK KnownSimple.IsKnownSimple Cover) :
    G64CentralAlternative (imageRepresentation ρ) := by
  let σ := imageRepresentation ρ
  let π := actionHom ρ
  have hπ : Function.Surjective π := ρ.asGroupHom.rangeRestrict_surjective
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff π hπ σ).mp
    (show ρ.IsIrreducible from inferInstance)
  have htr : IsTransvection σ (π v) := transvection_of_rank_one σ (π v) hr
  have hfaith := imageRepresentation_injective ρ
  have hsource : ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple
      σ (π v) (π.comp q) := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hcover
    quotient_surjective := hπ.comp hq
    twoCore := twoCore_eq_bot σ hfaith
    faithful := hfaith
    involution := transvection_square hfaith htr
    nonidentity := htr.ne_one
    displacement_rank := by rw [transvection_displacement_rank htr]; decide
    generated := by
      rw [← ChapterG.Section06.chapter13_displacementOrbit_eq]
      exact orbit_eq_top_of_irreducible σ (π v) htr }
  obtain ⟨_, hm⟩ := (ChapterG.Section06.lemma_G_6_4 hsource hr).2
    (T.mapSurjective hπ) (central_image π hπ T v ht)
  exact AbelianExclusion.central_alternative_of_source_model σ hm

theorem constituent_central_alternative
    (ρ : Representation (ZMod 2) A E) (K : Subgroup A) [K.Normal]
    (v : A) (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hJ : J.toRepresentation.IsIrreducible)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) = 1)
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q)
    (hcover : IsSQTK KnownSimple.IsKnownSimple Cover) :
    G64CentralAlternative (imageRepresentation (constituentAction J hv)) := by
  let := constituentAction_irreducible J hv hJ
  obtain ⟨P, hP⟩ := extension_sylow K v T ht
  exact image_central_alternative (constituentAction J hv) (extensionMark K v) P hP
    ((constituentAction_rank J hv).trans hr)
    (q.subgroupComap (extensionActor K v))
    (q.subgroupComap_surjective_of_surjective _ hq) (hcover.subgroup _)

theorem constituent_linear_three
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S) (K : Subgroup A) [K.Normal]
    (e : K ≃* (Fin n → S)) (ρ : Representation (ZMod 2) A E) (v : A)
    (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hJ : J.toRepresentation.IsIrreducible)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) = 1)
    (hdim : 3 ≤ Module.finrank (ZMod 2) J.toSubmodule)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id)))))
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q)
    (hcover : IsSQTK KnownSimple.IsKnownSimple Cover) :
    HasActionModel (imageRepresentation (constituentAction J hv)) (linearRepresentation 3) := by
  have halt := constituent_central_alternative ρ K v T ht J hv hJ hr q hq hcover
  have hr' : Module.finrank (ZMod 2) (LinearMap.range
      (imageRepresentation (constituentAction J hv)
        (actionHom (constituentAction J hv) (extensionMark K v)) - LinearMap.id)) = 1 :=
    (constituentAction_rank J hv).trans hr
  have hno := image_no_cubic hna e ρ v J hv hplane
  obtain ⟨m, hm₂, hm₅, hm⟩ := PermutationSieve.linear_of_central_alternative _
    (imageRepresentation_injective _) _ (transvection_of_rank_one _ _ hr') hno halt
  exact (LinearSieve.linear_model_eq_three _ _ hr' hdim hno hm₂ hm₅ hm).2

theorem natural_models
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S) (K : Subgroup A) [K.Normal]
    (e : K ≃* (Fin n → S)) (ρ : Representation (ZMod 2) A E)
    (hfaith : Function.Injective ρ) (v : A) (s : ℕ) (hs : 0 < s)
    (p : SplitPair ρ K v s)
    (Q : QuadraticForm (ZMod 2) E) (hQ : ∀ a x, Q (ρ a x) = Q x)
    (hnd : Q.polarBilin.Nondegenerate)
    (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id)))))
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q)
    (hcover : IsSQTK KnownSimple.IsKnownSimple Cover) : p.HasNaturalModels := by
  have h₁ := constituent_linear_three hna K e ρ v T ht
    p.first p.first_invariant p.first_irreducible p.first_displacement
    (by rw [p.first_dimension]; omega) hplane q hq hcover
  have h₂ := constituent_linear_three hna K e ρ v T ht
    p.second p.second_invariant p.second_irreducible p.second_displacement
    (by rw [p.second_dimension]; omega) hplane q hq hcover
  obtain ⟨m₁⟩ := constituent_natural_cover ρ K v p.first p.first_invariant h₁
  obtain ⟨m₂⟩ := constituent_natural_cover ρ K v p.second p.second_invariant h₂
  have hsing (J : Subrepresentation (ρ.comp K.subtype))
      (hJ : J.toRepresentation.IsIrreducible)
      (hd : 1 < Module.finrank (ZMod 2) J.toSubmodule)
      (m : BinaryLinearThree.NaturalCover J.toRepresentation) :
      ∀ x ∈ J.toSubmodule, Q x = 0 := by
    let := hJ
    have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
      J.toRepresentation hd (Q.comp J.toSubmodule.subtype)
      (fun a x => hQ a.val x.val) m.not_self_dual
    intro x hx
    exact congrArg (fun q : QuadraticForm (ZMod 2) J.toSubmodule => q ⟨x, hx⟩) hz
  have hs₁ := hsing p.first p.first_irreducible (by rw [p.first_dimension]; omega) m₁
  have hs₂ := hsing p.second p.second_irreducible (by rw [p.second_dimension]; omega) m₂
  have hf : Function.Injective (ρ.comp K.subtype) := hfaith.comp Subtype.val_injective
  have hf₁ := BinaryQuadraticConstituent.faithful_of_singular_complement
    (ρ.comp K.subtype) hf Q (fun a x => hQ a.val x) p.second p.first
    p.complement.symm hnd hs₂
  have hf₂ := BinaryQuadraticConstituent.faithful_of_singular_complement
    (ρ.comp K.subtype) hf Q (fun a x => hQ a.val x) p.first p.second
    p.complement hnd hs₁
  exact ⟨⟨m₁.toNaturalModel hf₁⟩, ⟨m₂.toNaturalModel hf₂⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
