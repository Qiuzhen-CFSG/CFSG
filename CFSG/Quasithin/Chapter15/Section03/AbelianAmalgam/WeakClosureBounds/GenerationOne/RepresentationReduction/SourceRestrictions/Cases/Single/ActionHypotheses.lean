module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Applying B.4 on the literal central-section action

For a normal quasisimple K and an invariant Irr⁺ section I, construct the
whole actor's representation on I/C_I(K). Its K-action is the original
irreducible central-quotient action. The image-structure theorem then
identifies the entire generalized Fitting subgroup of the faithful image.
When K is centerless and the quotient above K is a two-group, SQTK descends
to that image. A quadratic actor faithful on K retains its rank on the
section, while fixed codimension can only decrease; hence B.4.5 applies.

Every additional input is explicit: invariance of I, relative normality
and quasisimplicity of K, SQTK of the acting group, its two-group quotient
above K, the centerless cover calculation, and the common faithful
quadratic actor. These must be established in the local application;
none is inferred just from a family name or from a ratio bound on V.

The section construction follows the checked Suzuki SectionRecognition
argument, reusing the public SourceOrbit.ActionImage.Structure theorems.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(3--4),
printed pp.325--326; B.4.2/B.4.5, pp.86--87; 15.3.65, p.1152.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (I : Subrepresentation ρ)

noncomputable def sectionFixed : Subrepresentation I.toRepresentation where
  toSubmodule := (fixedSpace ρ K).comap I.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv

noncomputable def sectionRepresentation :
    Representation (ZMod 2) D (centralQuotient ρ K I.toSubmodule) :=
  (sectionFixed ρ K I).quotientRepresentation

theorem sectionRepresentation_component (hI : K ≤ subspaceStabilizer ρ I.toSubmodule)
    (k : K) (v : centralQuotient ρ K I.toSubmodule) :
    sectionRepresentation ρ K I k v = centralQuotientRepresentation ρ K I.toSubmodule hI k v := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

theorem section_component_survives (hi : IsIrrPlus ρ K I.toSubmodule) :
    ¬ K ≤ (actionHom (sectionRepresentation ρ K I)).ker := by
  intro hk
  apply hi.not_le_fixedSpace ρ
  rw [← hi.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hkK, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff (sectionRepresentation ρ K I) k).mp (hk hkK)
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.toSubmodule.subtype)).mp hfix

theorem section_component_irreducible (hi : IsIrrPlus ρ K I.toSubmodule) :
    IsIrreducible ((sectionRepresentation ρ K I).comp K.subtype) := by
  have he : (sectionRepresentation ρ K I).comp K.subtype =
      centralQuotientRepresentation ρ K I.toSubmodule hi.choose := by
    apply MonoidHom.ext
    intro k
    apply LinearMap.ext
    intro v
    exact sectionRepresentation_component ρ K I hi.choose k v
  rw [he]
  exact hi.choose_spec.2

variable [Finite D] [Finite V] [IsQuasisimple K]

instance sectionFinite : Finite (centralQuotient ρ K I.toSubmodule) :=
  Finite.of_surjective ((fixedSpace ρ K).comap I.toSubmodule.subtype).mkQ
    ((fixedSpace ρ K).comap I.toSubmodule.subtype).mkQ_surjective

/-- All nonnumerical B.4 assumptions on the exact faithful image of I/C_I(K).
The parent must prove the centerless and outer two-group premises on this actor. -/
theorem section_B4_hypotheses {𝒦 : GroupClass.{u}}
    (hi : IsIrrPlus ρ K I.toSubmodule) (hs : IsSQTK 𝒦 D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥) :
    B4Hypotheses 𝒦 (imageRepresentation (sectionRepresentation ρ K I)) := by
  let σ := sectionRepresentation ρ K I
  have hsurvive := section_component_survives ρ K I hi
  obtain ⟨hqs, hirr, hfit⟩ := image_structure σ K hsurvive hquot
    (section_component_irreducible ρ K I hi)
  let := hqs
  refine ⟨image_sqtk σ K hsurvive hs hquot hZ, imageRepresentation_injective σ, ?_, ?_⟩
  · exact IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hfit).symm
  · rw [hfit]
    exact hirr

/-- A common quadratic actor faithful on K remains faithful on the central section.
Its numerical bound passes through the submodule and quotient maps. -/
theorem section_quadratic_bound
    (hi : IsIrrPlus ρ K I.toSubmodule) (A : Subgroup D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) :
    quadraticRatio (imageRepresentation (sectionRepresentation ρ K I)) ≤ 2 := by
  let σ := sectionRepresentation ρ K I
  have hsurvive := section_component_survives ρ K I hi
  have hn : ¬ ∀ k ∈ K, ∀ v, σ k v = v := by
    intro h
    exact hsurvive (fun k hk => (actionHom_eq_one_iff σ k).mpr (h k hk))
  have hfaith := faithful_on_section_of_central_kernel σ K A hAC
    (central_kernel_of_quasisimple σ K hn)
  have hqσ : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection I.toRepresentation σ
      (sectionFixed ρ K I).toSubmodule.mkQ
      (sectionFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ I hq)
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨actionSubgroup σ A, hA.actionSubgroup σ hfaith, ?_, ?_⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact hqσ x hx y hy v
  · rw [fixedCodim_actionSubgroup, actionSubgroup_rank σ A hfaith]
    exact (fixedCodim_le_of_equivariant_surjection I.toRepresentation σ
      (sectionFixed ρ K I).toSubmodule.mkQ
      (sectionFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
        ((fixedCodim_subrepresentation_le ρ I A).trans hc)

/-- B.4.5 can now be applied to the literal section's faithful action image. -/
theorem section_B45_hypotheses {𝒦 : GroupClass.{u}}
    (hi : IsIrrPlus ρ K I.toSubmodule) (hs : IsSQTK 𝒦 D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥) :
    B45Hypotheses 𝒦 (imageRepresentation (sectionRepresentation ρ K I)) :=
  (section_B4_hypotheses ρ K I hi hs hquot hZ).with_quadratic_bound
    (section_quadratic_bound ρ K I hi A hA hq hc hAC)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
