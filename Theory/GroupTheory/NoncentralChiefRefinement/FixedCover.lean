module
public import Theory.GroupTheory.NoncentralChiefRefinement.FixedIndex

/-!
# Fixed representatives and central kernels on a normal section

Restrict the literal A -> A/B projection to C_A(E). Coprime lifting
makes its image all of C_(A/B)(E), and its kernel is exactly C_B(E).
Conjugation by the original normalizer of C_J(E) commutes with this map.
A subgroup centralizing a second actor H maps into the H-fixed subgroup
of the same section.

These maps support the actual chief-section comparison in Aschbacher--Smith,
combined manuscript, 1 March 2004, 11.1.2, printed pp.763--764. No chiefness
or recognition of the section's representation is assumed.
-/

open Subgroup
namespace NoncentralChiefRefinement
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Group J]

/-- The original fixed representatives, before taking the selected quotient. -/
abbrev fixedRepresentatives (A : NormalNode J) (E : Subgroup J) :=
  (centralizer (E : Set J)).subgroupOf A.val

/-- The literal section projection restricted to fixed representatives. -/
def fixedProjection (B A : NormalNode J) (E : Subgroup J) :
    fixedRepresentatives A E →* sectionFixed B A E where
  toFun a := ⟨QuotientGroup.mk' (B.val.subgroupOf A.val) a.val,by
    intro e
    rw [sectionAction_mk]
    congr 1
    apply Subtype.ext
    change (e : J) * (a.val : J) * (e : J)⁻¹ = (a.val : J)
    have hc : (e : J) * (a.val : J) = (a.val : J) * (e : J) := a.property e e.property
    rw [hc,mul_inv_cancel_right]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

@[simp] theorem fixedProjection_val (B A : NormalNode J) (E : Subgroup J)
    (a : fixedRepresentatives A E) :
    (fixedProjection B A E a).val = QuotientGroup.mk' (B.val.subgroupOf A.val) a.val := rfl

theorem fixedProjection_surjective [Finite J]
    (B A : NormalNode J) (hBA : B ≤ A) (E : Subgroup J)
    (hsolv : Group.IsSolvable A.val)
    (hcop : Nat.Coprime (Nat.card E) (Nat.card A.val)) :
    Function.Surjective (fixedProjection B A E) := by
  intro w
  obtain ⟨a,ha,he⟩ := section_fixed_lift B A hBA E hsolv hcop w.val w.property
  exact ⟨⟨a,ha⟩,Subtype.ext he⟩

/-- The first kernel is the original lower endpoint's cubic centralizer. -/
theorem fixedProjection_ker (B A : NormalNode J) (E : Subgroup J) :
    (fixedProjection B A E).ker =
      (B.val.subgroupOf A.val).subgroupOf (fixedRepresentatives A E) := by
  ext a
  change fixedProjection B A E a = 1 ↔ (a.val : J) ∈ B.val
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (N := B.val.subgroupOf A.val) a.val

/-- Centralization before the quotient gives pointwise fixed images on the
same section, with its original endpoints and conjugation action. -/
theorem fixedProjection_image_fixed (B A : NormalNode J) (E H : Subgroup J)
    (R : Subgroup (fixedRepresentatives A E))
    (hR : ∀ a, a ∈ R → (a.val : J) ∈ centralizer (H : Set J)) :
    R.map (fixedProjection B A E) ≤ (sectionFixed B A H).subgroupOf (sectionFixed B A E) := by
  rintro _ ⟨a,ha,rfl⟩ h
  change sectionAction B A h (QuotientGroup.mk' (B.val.subgroupOf A.val) a.val) =
    QuotientGroup.mk' (B.val.subgroupOf A.val) a.val
  rw [sectionAction_mk]
  congr 1
  apply Subtype.ext
  change (h : J) * (a.val : J) * (h : J)⁻¹ = (a.val : J)
  rw [hR a ha h h.property,mul_inv_cancel_right]

/-- Conjugation on the fixed representatives, keeping the ambient actor. -/
def conjugateFixed (A : NormalNode J) (E : Subgroup J)
    (j : J) (hj : j ∈ normalizer (centralizer (E : Set J) : Set J))
    (a : fixedRepresentatives A E) : fixedRepresentatives A E :=
  ⟨MulAut.conjNormal j a.val,
    (mem_normalizer_iff.mp hj (a.val : J)).mp a.property⟩

/-- The fixed-representative projection intertwines literal conjugation. -/
theorem fixedProjection_conjugate (B A : NormalNode J) (E : Subgroup J)
    (j : J) (hj : j ∈ normalizer (centralizer (E : Set J) : Set J))
    (a : fixedRepresentatives A E) :
    (fixedProjection B A E (conjugateFixed A E j hj a)).val =
      sectionAction B A j (fixedProjection B A E a).val := rfl

end
end NoncentralChiefRefinement
