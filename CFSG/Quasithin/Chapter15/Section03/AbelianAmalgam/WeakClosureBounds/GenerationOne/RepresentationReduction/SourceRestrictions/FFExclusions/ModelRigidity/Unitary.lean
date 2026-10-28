module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.LinearModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels.RootInvariants
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Excluding PSU₃ at odd field exponent

The actual unitary root Sylow has order q³ and elementary rank at most f,
where q = 2^f is the fixed-field order. The matrix field has order q².
Equality with PSL₂ or PSL₃ contradicts these two invariants. For Sp₄
and full G₂, the order's two-part already contradicts Odd f. The actual
small derived, alternating and binary linear orders are handled separately.
Triviality of the projective center also gives the result on the literal
central quotient; no assertion about a representation kernel is needed.

Source: Aschbacher--Smith, B.4.2, printed p.86, and the comparison of
E.2.2's Bender groups in 15.3.65, printed p.1152.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {f : ℕ} {family : Family} {q : ℕ}

/-- No entry in the complete central component catalogue is PSU₃(2^f),
with f > 1 odd. Here 2^f is the fixed-field order, not the matrix-field order. -/
theorem unitary_not_componentModel (hf : 1 < f) (ho : Odd f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    ¬ ComponentModel (ProjectiveSpecialUnitaryMatrixGroup J) family q := by
  obtain ⟨hr, hp⟩ :=
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels.projective_invariants
      J (by omega) hF hconj
  intro h
  rcases h.invariant_cases with ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | hs
  · omega
  · omega
  · obtain ⟨k, hk⟩ := ho
    omega
  · obtain ⟨k, hk⟩ := ho
    omega
  · exact not_smallOrder_of_ternary_part hf ho hp hs

/-- The actual center quotient is compared through its canonical projection. -/
theorem unitary_centralQuotient_not_componentModel (hf : 1 < f) (ho : Odd f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    ¬ ComponentModel (ProjectiveSpecialUnitaryMatrixGroup J ⧸
      center (ProjectiveSpecialUnitaryMatrixGroup J)) family q := by
  let e : (ProjectiveSpecialUnitaryMatrixGroup J ⧸
      center (ProjectiveSpecialUnitaryMatrixGroup J)) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq
      (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hF hconj)).trans
        QuotientGroup.quotientBot
  intro h
  exact unitary_not_componentModel J hf ho hF hconj (h.transport e.symm)

/-- The same exclusion for the faithful image of any nontrivial action of a
quasisimple group whose specified central quotient is PSU₃. -/
theorem unitary_actionImage_not_componentModel_of_central_quotient
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (e : D ⧸ center D ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    ¬ ComponentModel (Representation.BinaryOffender.actionImage ρ ⧸
      center (Representation.BinaryOffender.actionImage ρ)) family q := by
  intro h
  exact unitary_not_componentModel J hf ho hF hconj
    (h.transport (e.symm.trans (actionImageCentralQuotientEquiv ρ hn)))

/-- A genuine unitary model of the acting group gives the same exclusion,
without requiring faithfulness before passing to its image. -/
theorem unitary_actionImage_not_componentModel
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (e : D ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    ¬ ComponentModel (Representation.BinaryOffender.actionImage ρ ⧸
      center (Representation.BinaryOffender.actionImage ρ)) family q := by
  rw [componentModel_actionImage_iff ρ hn e]
  exact unitary_centralQuotient_not_componentModel J hf ho hF hconj

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
