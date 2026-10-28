module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Linear
public import Theory.Representation.SimpleHeadQuotient

/-!
# Chief factors as literal quotient representations

Restrict the lower invariant space to the upper one, then take its actual
quotient action. Irreducibility of this action is equivalent to the absence
of an intermediate invariant subspace. This makes the chief-factor assertion
in Aschbacher--Smith H.16.4(1), p.403, available in both lattice and action form.
-/

@[expose] public section
noncomputable section
open Representation
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
  {ρ : Representation (ZMod 2) G X}

/-- The lower member of an invariant section, inside its upper member. -/
def sectionSubrepresentation (A B : Subrepresentation ρ) : Subrepresentation B.toRepresentation where
  toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := A.apply_mem_toSubmodule g hv

theorem covBy_of_irreducible_section {A B : Subrepresentation ρ} (hAB : A < B)
    (hi : IsIrreducible (sectionSubrepresentation A B).quotientRepresentation) : A ⋖ B := by
  refine ⟨hAB, ?_⟩
  intro P hAP hPB
  let N := sectionSubrepresentation A B
  let T := sectionSubrepresentation P B
  have hk : N.toSubmodule.mkQ.ker ≤ T.toSubmodule := by
    rw [Submodule.ker_mkQ]
    exact Submodule.comap_mono hAP.le
  rcases eq_ker_or_top B.toRepresentation N.quotientRepresentation N.toSubmodule.mkQ
    (fun _ _ => rfl) hi T hk with he | he
  · have hPA : P ≤ A := by
      intro v hv
      have hm : (⟨v, hPB.le hv⟩ : B.toSubmodule) ∈ T.toSubmodule := hv
      rw [he, Submodule.ker_mkQ] at hm
      exact hm
    exact (not_le_of_gt hAP) hPA
  · have hBP : B ≤ P := by
      intro v hv
      have hm : (⟨v, hv⟩ : B.toSubmodule) ∈ T.toSubmodule := by rw [he]; trivial
      exact hm
    exact (not_le_of_gt hPB) hBP

/-- Covers in the invariant-subspace lattice are genuine irreducible quotient actions. -/
theorem irreducible_section_of_covBy {A B : Subrepresentation ρ} (hAB : A ⋖ B) :
    IsIrreducible (sectionSubrepresentation A B).quotientRepresentation := by
  apply SimpleHeadQuotient.irreducible_quotient_of_isCoatom
  refine ⟨?_, ?_⟩
  · intro he
    have hBA : B ≤ A := by
      intro v hv
      have hm : (⟨v, hv⟩ : B.toSubmodule) ∈ sectionSubrepresentation A B := by rw [he]; trivial
      exact hm
    exact (not_le_of_gt hAB.lt) hBA
  · intro P hP
    let T : Subrepresentation ρ := {
      toSubmodule := P.toSubmodule.map B.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨B.toRepresentation g v, P.apply_mem_toSubmodule g hv, rfl⟩ }
    have hAT : A ≤ T := by
      intro v hv
      exact ⟨⟨v, hAB.le hv⟩, hP.le hv, rfl⟩
    have hTB : T ≤ B := Submodule.map_subtype_le _ _
    rcases hAB.eq_or_eq hAT hTB with ht | ht
    · have hPN : P ≤ sectionSubrepresentation A B := by
        intro v hv
        have : v.val ∈ T := ⟨v, hv, rfl⟩
        rw [ht] at this
        exact this
      exact ((not_le_of_gt hP) hPN).elim
    · apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v _
      have : v.val ∈ T := by rw [ht]; exact v.property
      obtain ⟨w, hw, he⟩ := this
      exact (Subtype.ext he : w = v) ▸ hw

end MathieuCode.Hexad.ChiefFlag.Actions
