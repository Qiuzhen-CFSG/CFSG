module
public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Theory.GroupAction.NativeCoprimeQuotientFixedCard

/-!
# Coprime fixed lifts on literal normal sections

A fixed element of A/B under a coprime actor E has a representative in
C_A(E), when A is solvable. Apply native coprime fixed-point lifting to
the section action and retain the exact quotient projection. No change
of carrier or abstract isomorphism is required by the consumer.

Source application: Aschbacher--Smith, 11.1.2, printed pp.763--764,
comparison of the original cubic centralizer with the chosen chief section.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

/-- Every fixed section element has a fixed representative under the original
quotient map and ambient conjugation action. -/
theorem section_fixed_lift (B A : NormalNode H) (hBA : B ≤ A)
    (E : Subgroup H) (hA : Group.IsSolvable A.val)
    (hc : Nat.Coprime (Nat.card E) (Nat.card A.val))
    (w : Section B A) (hw : ∀ e : E, sectionAction B A e w = w) :
    ∃ a : A.val, (a : H) ∈ centralizer (E : Set H) ∧
      QuotientGroup.mk' (B.val.subgroupOf A.val) a = w := by
  have hh := (native_coprime_quotient_fixed_card ⊤ A.val B.val E hBA
    le_normalizer_of_normal le_normalizer_of_normal le_top hA hc inferInstance
    ((sectionAction B A).comp (⊤ : Subgroup H).subtype) (fun _ _ => rfl)).1
  let _ : MulDistribMulAction E (Section B A) := MulDistribMulAction.compHom _
    (((sectionAction B A).comp (⊤ : Subgroup H).subtype).comp (inclusion le_top))
  have hf : w ∈ FixedPoints.subgroup E (Section B A) := hw
  rw [hh] at hf
  obtain ⟨a,ha,he⟩ := hf
  exact ⟨a,ha.2,he⟩
end NoncentralChiefRefinement
