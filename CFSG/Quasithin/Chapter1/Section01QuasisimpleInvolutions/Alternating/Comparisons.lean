module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Centers
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Genuine model comparisons for the alternating branch of 1.1.5

Compose the proved permutation/matrix equivalences with the given model.
In the binary symplectic case the commutator is taken after the projective
quotient, exactly as in the canonical source interface. The degree bound
then leaves A₆, A₇, and the two precise even-characteristic reductions
PSL₂(4) and PSL₄(2). No automorphism or covering classification is asserted
by these comparisons.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed pp.502--503.
The imported exceptional comparisons retain their ATLAS attribution.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
open Chapter15.Section03.Candidates.ComponentStructure

variable {H L : Type*} [Group H] [Group L]

/-- The exact A₅-to-PSL₂(4) reduction. -/
theorem psl_four_of_equiv_five (e : H ≃* alternatingGroup (Fin 5)) :
    ClassicalGroup.IsPSL H 2 4 := by
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  rw [GaloisField.card 2 2 (by decide)]
  norm_num

/-- The exact A₈-to-PSL₄(2) reduction. The even-family owner must also treat
its double cover when this is applied to a central quotient. -/
theorem psl_binary_four_of_equiv_eight (e : H ≃* alternatingGroup (Fin 8)) :
    ClassicalGroup.IsPSL H 4 2 :=
  ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

/-- Every actual PSL₂(9) model supplies an actual A₆ model. -/
theorem equiv_six_of_psl_nine (h : ClassicalGroup.IsPSL H 2 9) :
    Nonempty (H ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, iF, fF, hc, ⟨e⟩⟩ := h
  exact ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩

/-- The actual derived projective symplectic model supplies the marked A₆
quotient; the order of taking quotient and commutator is retained. -/
def equiv_six_of_projective_derived
    (e : H ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    H ≃* alternatingGroup (Fin 6) :=
  e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix

/-- A₆ is one of the canonical characteristic-two derived models. -/
theorem lie_model_of_equiv_six (e : H ≃* alternatingGroup (Fin 6)) :
    LieTypeTwoModel H :=
  Or.inr (Or.inl (.symplectic_derived
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩))

/-- Exhaust all degrees at most eight using inherited perfectness/simplicity
and actual exceptional equivalences. -/
theorem small_quotient_cases [IsQuasisimple L] {n : ℕ}
    (hn : n ≤ 8) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    ClassicalGroup.IsPSL (L ⧸ center L) 2 4 ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 7)) ∨
      ClassicalGroup.IsPSL (L ⧸ center L) 4 2 := by
  have hl := five_le_degree e
  interval_cases n
  · exact Or.inl (psl_four_of_equiv_five e)
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inr (Or.inr (psl_binary_four_of_equiv_eight e)))

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
