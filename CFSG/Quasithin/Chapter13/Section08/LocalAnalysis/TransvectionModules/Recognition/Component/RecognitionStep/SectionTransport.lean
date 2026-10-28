module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.ModelComponents
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Perfect

/-!
# Returning the natural component section to the source module

An injective equivariant map that identifies two commutator spaces identifies
also their fixed subspaces and their central quotients. Apply this to the
perfect component of the self-generated displacement actor, using the
perfect-commutator restriction identity. The subgroup equivalence is the
actual inclusion into the original actor, so the model coordinates survive.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the first
paragraph of 13.8.5, printed p.947, applying G.6.4 on pp.345–346.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
variable {A B D E F U : Type*} [Group A] [Group B] [Group D]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [AddCommGroup U] [Module (ZMod 2) U]

/-- Carry the literal central quotient through an equivariant embedding that
identifies the two commutator spaces. -/
theorem centralSectionModel_transport
    (ρ : Representation (ZMod 2) A E) (σ : Representation (ZMod 2) B F)
    (C : Subgroup A) (K : Subgroup B) (eC : C ≃* K)
    (f : E →ₗ[ZMod 2] F) (hf : Function.Injective f)
    (hI : (subspaceCommutator ρ ⊤ C).map f = subspaceCommutator σ ⊤ K)
    (he : ∀ (c : C) v, f (ρ c v) = σ (eC c) (f v))
    (τ : Representation (ZMod 2) D U) (eD : C ≃* D)
    (hm : HasCentralSectionModel ρ C τ eD) :
    HasCentralSectionModel σ K τ (eC.symm.trans eD) := by
  classical
  obtain ⟨hs, em, hem⟩ := hm
  let I := subspaceCommutator ρ ⊤ C
  let J := subspaceCommutator σ ⊤ K
  let e : I ≃ₗ[ZMod 2] J :=
    (Submodule.equivMapOfInjective f hf I).trans (LinearEquiv.ofEq _ _ hI)
  have ev (v : I) : (e v : F) = f v := rfl
  have hsJ (k : K) (v : J) : σ k v ∈ J := by
    obtain ⟨c, rfl⟩ := eC.surjective k
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [ev, ← he]
    change f (ρ c w) ∈ subspaceCommutator σ ⊤ K
    rw [← hI]
    exact ⟨_, hs c w, rfl⟩
  have heact (c : C) (v : I) :
      e ⟨ρ c v, hs c v⟩ = ⟨σ (eC c) (e v), hsJ (eC c) (e v)⟩ := by
    apply Subtype.ext
    exact he c v
  let P := (fixedSpace ρ C).comap I.subtype
  let Q := (fixedSpace σ K).comap J.subtype
  have hfix (v : I) : v ∈ P ↔ e v ∈ Q := by
    change (∀ c : C, ρ c v = v) ↔ (∀ k : K, σ k (e v) = e v)
    constructor
    · intro hv k
      obtain ⟨c, rfl⟩ := eC.surjective k
      rw [ev, ← he, hv c]
    · intro hv c
      apply hf
      rw [he]
      exact hv (eC c)
  have hPQ : P.map e.toLinearMap = Q := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hfix w).mp hw
    · intro hv
      obtain ⟨w, rfl⟩ := e.surjective v
      exact ⟨w, (hfix w).mpr hv, rfl⟩
  let eqv := Submodule.Quotient.equiv P Q e hPQ
  have hmk (v : I) : eqv (Submodule.Quotient.mk v) = Submodule.Quotient.mk (e v) := rfl
  refine ⟨hsJ, eqv.symm.trans em, ?_⟩
  intro k v
  obtain ⟨c, rfl⟩ := eC.surjective k
  obtain ⟨w, rfl⟩ := e.surjective v
  change em (eqv.symm (Submodule.Quotient.mk _)) =
    τ (eD (eC.symm (eC c))) (em (eqv.symm (Submodule.Quotient.mk (e w))))
  rw [← heact, ← hmk, ← hmk, eqv.symm_apply_apply, eqv.symm_apply_apply,
    eC.symm_apply_apply]
  exact hem c w

/-- Transport the perfect component section from the actual displacement
submodule of a subgroup actor back into the original actor and module. -/
theorem naturalSection_of_displacement
    (ρ : Representation (ZMod 2) A E) (J : Subgroup A) (t : J)
    (hgen : normalClosure ({t} : Set J) = ⊤)
    (C : Subgroup J) [Group.IsPerfect C]
    (hm : NaturalSection (displacementRepresentation (ρ.comp J.subtype) t).toRepresentation C) :
    NaturalSection ρ (C.map J.subtype) := by
  let σ := (displacementRepresentation (ρ.comp J.subtype) t).toRepresentation
  let eC := C.equivMapOfInjective J.subtype J.subtype_injective
  let f := (displacementOrbit (ρ.comp J.subtype) t).subtype
  have hcomp : subspaceCommutator (ρ.comp J.subtype) ⊤ C =
      subspaceCommutator ρ ⊤ (C.map J.subtype) := by
    simpa only [Submodule.map_id] using
      ModelComponents.commutator_map (ρ.comp J.subtype) ρ C (C.map J.subtype)
        eC LinearMap.id Function.surjective_id (fun _ _ => rfl)
  have hI : (subspaceCommutator σ ⊤ C).map f =
      subspaceCommutator ρ ⊤ (C.map J.subtype) :=
    (displacement_perfect_commutator (ρ.comp J.subtype) t hgen C).symm.trans hcomp
  rcases hm with ⟨n, hn, hn5, eD, hm⟩ | ⟨n, hn, hn8, eD, hm⟩
  · exact Or.inl ⟨n, hn, hn5, eC.symm.trans eD,
      centralSectionModel_transport σ ρ C _ eC f Subtype.val_injective hI
        (fun _ _ => rfl) _ eD hm⟩
  · exact Or.inr ⟨n, hn, hn8, eC.symm.trans eD,
      centralSectionModel_transport σ ρ C _ eC f Subtype.val_injective hI
        (fun _ _ => rfl) _ eD hm⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
