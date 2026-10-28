module
public import Theory.Representation.BinaryOffender.MovedCentralProjection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.SectionTransport

/-!
# Component sections under a central projection

For a perfect actor, a surjection whose kernel is fixed identifies the
central quotients of the moved spaces. Thus a marked component section on
the quotient returns to the original module with the same actor marking.

Source: Aschbacher–Smith, 13.7.18, printed p.945.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
variable {A E F B W : Type*} [Group A] [Group B]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem centralSectionModel_of_central_surjection
    (ρ : Representation (ZMod 2) A E) (σ : Representation (ZMod 2) A F)
    (K : Subgroup A) [Group.IsPerfect K]
    (f : E →ₗ[ZMod 2] F) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ v, f (ρ k v) = σ k (f v))
    (hk : f.ker ≤ fixedSpace ρ K)
    (τ : Representation (ZMod 2) B W) (eK : K ≃* B)
    (hm : HasCentralSectionModel σ K τ eK) :
    HasCentralSectionModel ρ K τ eK := by
  obtain ⟨hp,e,hemk⟩ := exists_movedCentralQuotientEquiv_of_central_surjection
    ρ σ K f hf he hk
  obtain ⟨hs,em,hem⟩ := hm
  refine ⟨(fun k v => (subspaceCommutator_invariant ρ ⊤ K k.property v).2 v.property),
    e.trans em,?_⟩
  intro k v
  change em (e (Submodule.Quotient.mk _)) = τ (eK k) (em (e (Submodule.Quotient.mk v)))
  rw [hemk,hemk]
  have hrv : ρ k v ∈ subspaceCommutator ρ ⊤ K :=
    (subspaceCommutator_invariant ρ ⊤ K k.property v).2 v.property
  have hh : (⟨f (ρ k v),hp ⟨ρ k v,hrv⟩⟩ : subspaceCommutator σ ⊤ K) =
      ⟨σ k (f v),hs k ⟨f v,hp v⟩⟩ := Subtype.ext (he k v)
  rw [hh]
  exact hem k ⟨f v,hp v⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

