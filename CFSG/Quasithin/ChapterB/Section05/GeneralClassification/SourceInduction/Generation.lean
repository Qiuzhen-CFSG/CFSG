module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ModuleDecomposition
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.Restriction
/-!
# Offender generation on the actual complementary factor

B.1.5 carries each moving best offender to a best offender of the faithful
subspace action image. Centralizing offenders map to the identity. Hence an
offender-generated actor has an offender-generated invariant action image.
An actual internal product, opposite-factor centralization and faithfulness
identify that image with the original complementary subgroup. Transporting
weights along this isomorphism proves generation on that subgroup itself.

This is the generation assertion needed at both recursive steps B.5.8 and
B.5.11; it assumes no classification or reduced list of models.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.5(1), p.69,
and B.5.8/B.5.11, printed pp.106 and 109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D E V : Type*} [Group D] [Group E] [AddCommGroup V] [Module (ZMod 2) V]

private theorem bestOffender_map_equiv (σ : Representation (ZMod 2) E V) (e : D ≃* E)
    {A : Subgroup D} (hA : IsBestOffender (σ.comp e.toMonoidHom) A) :
    IsBestOffender σ (A.map e.toMonoidHom) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map e.toMonoidHom⟩, ?_⟩
  · intro hz
    apply hA.1.1
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hz
  · intro C hC
    have hCA : C.comap e.toMonoidHom ≤ A := by
      intro d hd
      obtain ⟨a, ha, he⟩ := hC hd
      exact e.injective he ▸ ha
    have hm : (C.comap e.toMonoidHom).map e.toMonoidHom = C :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective C
    calc
      weight σ C = weight (σ.comp e.toMonoidHom) (C.comap e.toMonoidHom) := by
        rw [weight_comp_map σ e.toMonoidHom e.injective, hm]
      _ ≤ weight (σ.comp e.toMonoidHom) A := hA.2 _ hCA
      _ = weight σ (A.map e.toMonoidHom) := weight_comp_map σ _ e.injective A

private theorem generated_comp_equiv (σ : Representation (ZMod 2) E V) (e : D ≃* E)
    (hgen : offenderSubgroup (σ.comp e.toMonoidHom) = ⊤) : offenderSubgroup σ = ⊤ := by
  have hle : offenderSubgroup (σ.comp e.toMonoidHom) ≤
      (offenderSubgroup σ).comap e.toMonoidHom := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩ a ha
    have hm : A.map e.toMonoidHom ≤ offenderSubgroup σ :=
      le_iSup_of_le (A.map e.toMonoidHom)
        (le_iSup_of_le ⟨bestOffender_map_equiv σ e hA, le_top⟩ le_rfl)
    exact hm (Subgroup.mem_map_of_mem e.toMonoidHom ha)
  apply top_unique
  intro g _
  obtain ⟨d,rfl⟩ := e.surjective g
  exact hle (hgen ▸ Subgroup.mem_top d)

/-- Generation descends to the literal invariant action image. -/
theorem invariant_image_generated [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Submodule (ZMod 2) V)
    (hW : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W)
    (hgen : offenderSubgroup ρ = ⊤) :
    offenderSubgroup (subspaceImageRepresentation ρ W) = ⊤ := by
  let f := invariantActionHom ρ W hW
  have hle : offenderSubgroup ρ ≤
      (offenderSubgroup (subspaceImageRepresentation ρ W)).comap f := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩ a ha
    change f a ∈ offenderSubgroup (subspaceImageRepresentation ρ W)
    by_cases hc : W ≤ fixedSpace ρ A
    · have hz : f a = 1 := by
        apply subspaceImageRepresentation_injective ρ W
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        exact hc w.property ⟨a, ha⟩
      rw [hz]
      exact Subgroup.one_mem _
    · have hAr := hA.restricted ρ W (le_top.trans hW) hc
      have hmem : f a ∈ restrictedSubgroup ρ W A := by
        rw [← invariantActionHom_map ρ W hW]
        exact Subgroup.mem_map_of_mem f ha
      have hm : restrictedSubgroup ρ W A ≤ offenderSubgroup (subspaceImageRepresentation ρ W) :=
        le_iSup_of_le (restrictedSubgroup ρ W A) (le_iSup_of_le ⟨hAr, le_top⟩ le_rfl)
      exact hm hmem
  apply top_unique
  intro g _
  obtain ⟨d,rfl⟩ := invariantActionHom_surjective ρ W hW g
  exact hle (hgen ▸ Subgroup.mem_top d)

/-- Generation on the original second subgroup, with the actual restricted action. -/
theorem second_generated [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {A B : Subgroup D} (h : InternalProduct A B)
    (W : Subrepresentation ρ) (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (hf : Function.Injective (W.toRepresentation.comp B.subtype))
    (hgen : offenderSubgroup ρ = ⊤) :
    offenderSubgroup (W.toRepresentation.comp B.subtype) = ⊤ := by
  let hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun g _ v hv => W.apply_mem_toSubmodule g hv)
  let f := invariantActionHom ρ W.toSubmodule hs
  let γ : B →* subspaceActionImage ρ W.toSubmodule := f.comp B.subtype
  have hi : Function.Injective γ := by
    intro b c he
    apply hf
    exact congrArg (subspaceImageRepresentation ρ W.toSubmodule) he
  have hsurj : Function.Surjective γ := by
    intro x
    obtain ⟨g,rfl⟩ := invariantActionHom_surjective ρ W.toSubmodule hs x
    obtain ⟨a,b,rfl⟩ := h.exists_mul g
    refine ⟨b, ?_⟩
    have ha : f (a : D) = 1 := by
      apply subspaceImageRepresentation_injective ρ W.toSubmodule
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact hW w.property a
    change f (b : D) = f ((a : D) * (b : D))
    rw [map_mul, ha, one_mul]
  let e : B ≃* subspaceActionImage ρ W.toSubmodule := MulEquiv.ofBijective γ ⟨hi,hsurj⟩
  have hact : subspaceImageRepresentation ρ W.toSubmodule =
      (W.toRepresentation.comp B.subtype).comp e.symm.toMonoidHom := by
    ext x w
    have he := e.apply_symm_apply x
    exact congrArg (fun y => (subspaceImageRepresentation ρ W.toSubmodule y w : V)) he.symm
  apply generated_comp_equiv (W.toRepresentation.comp B.subtype) e.symm
  rw [← hact]
  exact invariant_image_generated ρ W.toSubmodule hs hgen
end CFSG.Quasithin.ChapterB.SourceInduction
