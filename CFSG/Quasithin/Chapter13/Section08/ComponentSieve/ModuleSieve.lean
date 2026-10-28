module

public import Theory.Representation.BinaryOffender.CodimensionSieve

/-!
# Module arguments for the component sieve

These are conditional linear arguments in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.22–23, printed pp.957–958
(combined manuscript, 1 March 2004). The representation is intended to be
`H*` on `Ũ_H`; the subrepresentation and its literal quotient are `W̃`
and `Û_H`. All faithfulness and critical-subspace inputs are explicit.

A one-dimensional commutator target either lies in `W̃` or meets it
trivially. The fixed-codimension inequalities then produce the appropriate
FF-star offender. If no strong offender occurs, equality forces containment
or a supplement; faithfulness makes the resulting commutator exactly the
given line. The separate fixed-subspace result covers the case where the
source commutator bound has trivial intersection with the ambient module.

The source application must still identify these vector spaces with the
actual subgroup sections, establish the component hypotheses and critical
pair properties, and treat the two cases of 13.8.8. This module does not
assert any group-family exclusion or the endpoint 13.8.27.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

omit [Finite H] in
private theorem not_fixed_of_faithful (W : Subrepresentation ρ)
    (hW : Function.Injective W.toRepresentation) {A : Subgroup H} (hA : A ≠ ⊥) :
    ¬ W.toSubmodule ≤ fixedSpace ρ A := by
  intro hfix
  have ht : fixedSpace W.toRepresentation A = ⊤ := by
    apply top_unique
    intro w _ a
    exact Subtype.ext (hfix w.property a)
  have hz := (fixedCodim_eq_zero_iff W.toRepresentation A).mpr ht
  have hp := fixedCodim_pos_of_faithful W.toRepresentation hW hA
  omega

/-- The two offender alternatives when the critical commutator line lies
in the ambient module. The equality conclusions use the actual commutator
subspaces of the induced submodule and quotient actions. -/
theorem offender_alternatives_of_critical_line
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U)
    (hS : IsAtom S) (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup H}
    (hA : IsElementaryTwo A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A) :
    (S ≤ W.toSubmodule ∧ IsFFModule W.quotientRepresentation ∧
      (∃ B ≤ A, IsBestOffender W.quotientRepresentation B) ∧
      ((∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
          IsStrongOffender W.quotientRepresentation B) ∨
        (W.toSubmodule ≤ D ∧ subspaceCommutator ρ W.toSubmodule A = S))) ∨
    (¬ S ≤ W.toSubmodule ∧ IsFFModule W.toRepresentation ∧
      (∃ B ≤ A, IsBestOffender W.toRepresentation B) ∧
      ((∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
          IsStrongOffender W.toRepresentation B) ∨
        (W.toSubmodule ⊔ D = ⊤ ∧
          subspaceCommutator W.quotientRepresentation ⊤ A = S.map W.toSubmodule.mkQ))) := by
  have hSdim : Module.finrank (ZMod 2) S = 1 :=
    Submodule.isAtom_iff_finrank_eq_one.mp hS
  by_cases hSW : S ≤ W.toSubmodule
  · obtain ⟨hoff, hbest, hstrong | ⟨hWD, _, _, _⟩⟩ :=
      quotient_offender_sieve ρ W D hA
        (fun a ha d hd => hSW (hcomm a ha d hd)) hdim
    · exact Or.inl ⟨hSW, ⟨A, hoff⟩, hbest, Or.inl hstrong⟩
    · refine Or.inl ⟨hSW, ⟨A, hoff⟩, hbest, Or.inr ⟨hWD, ?_⟩⟩
      apply subspaceCommutator_eq_of_le_one_dimensional ρ W.toSubmodule S A
        (not_fixed_of_faithful ρ W hW hA.1) _ hSdim.le
      apply Submodule.span_le.mpr
      rintro v ⟨a, ha, w, hw, rfl⟩
      exact hcomm a ha w (hWD hw)
  · have hdisjoint : S ⊓ W.toSubmodule = ⊥ :=
      disjoint_iff.mp (hS.not_le_iff_disjoint.mp hSW)
    have hfixed : W.toSubmodule ⊓ D ≤ fixedSpace ρ A := by
      intro w hw a
      have hm : ρ a w - w ∈ S ⊓ W.toSubmodule :=
        ⟨hcomm a a.property w hw.2,
          W.toSubmodule.sub_mem (W.apply_mem_toSubmodule a hw.1) hw.1⟩
      rw [hdisjoint] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨hoff, hbest, hstrong | ⟨hWD, _, _, _⟩⟩ :=
      submodule_offender_sieve ρ W D hA hfixed hdim
    · exact Or.inr ⟨hSW, ⟨A, hoff⟩, hbest, Or.inl hstrong⟩
    · refine Or.inr ⟨hSW, ⟨A, hoff⟩, hbest, Or.inr ⟨hWD, ?_⟩⟩
      have hnontrivial : ¬ (⊤ : Submodule (ZMod 2) (U ⧸ W.toSubmodule)) ≤
          fixedSpace W.quotientRepresentation A := by
        intro htop
        have he := (fixedCodim_eq_zero_iff W.quotientRepresentation A).mpr
          (top_unique htop)
        have hp := fixedCodim_pos_of_faithful W.quotientRepresentation hQ hA.1
        omega
      apply subspaceCommutator_eq_of_le_one_dimensional W.quotientRepresentation
        ⊤ (S.map W.toSubmodule.mkQ) A hnontrivial
      · apply Submodule.span_le.mpr
        rintro v ⟨a, ha, q, _, rfl⟩
        induction q using Submodule.Quotient.induction_on with
        | _ u =>
          have hu : u ∈ W.toSubmodule ⊔ D := by rw [hWD]; trivial
          obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hu
          refine ⟨ρ a d - d, hcomm a ha d hd, ?_⟩
          have hw0 : W.toSubmodule.mkQ w = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hw
          have haw0 : W.toSubmodule.mkQ (ρ a w) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr (W.apply_mem_toSubmodule a hw)
          change W.toSubmodule.mkQ (ρ a d - d) =
            W.toSubmodule.mkQ (ρ a (w + d)) - W.toSubmodule.mkQ (w + d)
          simp only [map_add, map_sub, hw0, haw0, zero_add]
      · exact (Submodule.finrank_map_le W.toSubmodule.mkQ S).trans hSdim.le

/-- If the critical subspace is fixed, the submodule alternative must be
strong: otherwise its supplement would make the faithful quotient trivial.
In the source this applies when the critical line meets `U_H` trivially. -/
theorem strong_submodule_offender_of_fixed_subspace
    (W : Subrepresentation ρ) (D : Submodule (ZMod 2) U)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup H}
    (hA : IsElementaryTwo A) (hD : D ≤ fixedSpace ρ A)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A) :
    ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧ IsStrongOffender W.toRepresentation B := by
  obtain ⟨_, _, hstrong | ⟨hWD, _, _, _⟩⟩ :=
    submodule_offender_sieve ρ W D hA (inf_le_right.trans hD) hdim
  · exact hstrong
  · have hsup : W.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
      apply top_unique
      rw [← hWD]
      exact sup_le_sup_left hD _
    have htrivial := quotient_trivial_of_sup_fixedSpace ρ W A hsup
    have ht : fixedSpace W.quotientRepresentation A = ⊤ := by
      apply top_unique
      intro q _ a
      exact htrivial a a.property q
    have hz := (fixedCodim_eq_zero_iff W.quotientRepresentation A).mpr ht
    have hp := fixedCodim_pos_of_faithful W.quotientRepresentation hQ hA.1
    omega

omit [Finite H] in
/-- The faithful-section and fixed-vector-lifting deductions in 13.8.23.
The normal-subgroup condition expresses the monolith consequence of a
simple generalized Fitting subgroup. Nontriviality of its action on each
section remains explicit, rather than being inferred from a family label. -/
theorem rank_one_faithful_sections
    (W : Subrepresentation ρ) (K A : Subgroup H)
    (hK : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hKQ : ∃ k ∈ K, ∃ q : U ⧸ W.toSubmodule, W.quotientRepresentation k q ≠ q)
    (hA : A ≠ ⊥) (hrank : rank A = 1) (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    Function.Injective W.toRepresentation ∧ Function.Injective W.quotientRepresentation ∧
      fixedCodim W.toRepresentation A = 1 ∧ fixedCodim W.quotientRepresentation A = 1 ∧
      fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A := by
  have hW := faithful_of_nontrivial_on_monolith W.toRepresentation K hK hKW
  have hQ := faithful_of_nontrivial_on_monolith W.quotientRepresentation K hK hKQ
  obtain ⟨hw, hq, hu⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA (by omega)
  exact ⟨hW, hQ, hw, hq, hu,
    fixedSpace_quotient_eq_map_of_fixedCodim_eq ρ W A (by omega)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve
