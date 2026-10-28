module

public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.BinaryOffender.Basic
public import Theory.LinearAlgebra.SubspaceRatio

/-!
# Fixed codimensions of invariant sections

Restriction to an invariant subspace cannot increase fixed codimension, and
its equality case says that the subspace supplements the ambient fixed space.
For an invariant quotient, rank-nullity on the map from ambient fixed vectors
to quotient fixed vectors bounds the sum of the two fixed codimensions.

The section representation is the actual quotient of the upper subspace by
the lower subspace, realized by its comap along the inclusion. These are the
linear inequalities used in Aschbacher–Smith, *The Classification of Quasithin
Groups*, B.1.5(8), printed pp. 69–70 (1 March 2004 manuscript).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

noncomputable def subrepresentationFixedEquiv (W : Subrepresentation ρ) (A : Subgroup G) :
    fixedSpace W.toRepresentation A ≃ₗ[ZMod 2]
      (W.toSubmodule ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) where
  toFun w := ⟨w.val, w.val.property, fun a => congrArg Subtype.val (w.property a)⟩
  invFun w := ⟨⟨w, w.property.1⟩, fun a => Subtype.ext (w.property.2 a)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional (ZMod 2) V]

theorem fixedCodim_subrepresentation_le (W : Subrepresentation ρ) (A : Subgroup G) :
    fixedCodim W.toRepresentation A ≤ fixedCodim ρ A := by
  have hc := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have he := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hs := W.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  have ht := (W.toSubmodule ⊔ fixedSpace ρ A).finrank_le
  omega

theorem fixedCodim_subrepresentation_eq_iff (W : Subrepresentation ρ) (A : Subgroup G) :
    fixedCodim W.toRepresentation A = fixedCodim ρ A ↔
      W.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
  have hc := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have he := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hs := W.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    omega
  · intro h
    rw [h] at hs
    simp only [finrank_top] at hs
    omega

theorem fixedCodim_quotient_add_subrepresentation_le (U : Subrepresentation ρ)
    (A : Subgroup G) :
    fixedCodim U.quotientRepresentation A + fixedCodim U.toRepresentation A ≤
      fixedCodim ρ A := by
  let C := fixedSpace ρ A
  let f := U.toSubmodule.mkQ.domRestrict C
  have hr : LinearMap.range f ≤ fixedSpace U.quotientRepresentation A := by
    rintro _ ⟨v, rfl⟩ a
    change U.toSubmodule.mkQ (ρ a v) = U.toSubmodule.mkQ v
    exact congrArg U.toSubmodule.mkQ (v.property a)
  let e : LinearMap.ker f ≃ₗ[ZMod 2]
      (U.toSubmodule ⊓ C : Submodule (ZMod 2) V) :=
    { toFun := fun v => ⟨v.val, (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp v.property,
          v.val.property⟩
      invFun := fun v => ⟨⟨v, v.property.2⟩,
          (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr v.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hnull := f.finrank_range_add_finrank_ker
  have hker := e.finrank_eq
  have hfixed := (subrepresentationFixedEquiv ρ U A).finrank_eq
  have hle := Submodule.finrank_mono hr
  have hv := fixedCodim_add_finrank ρ A
  have hu := fixedCodim_add_finrank U.toRepresentation A
  have hq := fixedCodim_add_finrank U.quotientRepresentation A
  have hdim := U.toSubmodule.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (LinearMap.range f) +
    Module.finrank (ZMod 2) (LinearMap.ker f) = Module.finrank (ZMod 2) C at hnull
  change _ = Module.finrank (ZMod 2) (U.toSubmodule ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) at hker
  change fixedCodim ρ A + Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) V at hv
  omega

theorem fixedCodim_eq_zero_iff (A : Subgroup G) :
    fixedCodim ρ A = 0 ↔ fixedSpace ρ A = ⊤ := by
  have h := fixedCodim_add_finrank ρ A
  constructor
  · intro hz
    apply Submodule.eq_top_of_finrank_eq
    omega
  · intro ht
    rw [ht] at h
    simp only [finrank_top] at h
    omega

omit [FiniteDimensional (ZMod 2) V] in
theorem quotient_trivial_of_sup_fixedSpace (W : Subrepresentation ρ) (A : Subgroup G)
    (h : W.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    ∀ a ∈ A, ∀ v, W.quotientRepresentation a v = v := by
  intro a ha v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hv : v ∈ W.toSubmodule ⊔ fixedSpace ρ A := by rw [h]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    change W.toSubmodule.mkQ (ρ a (w + c)) = W.toSubmodule.mkQ (w + c)
    have hcw : ρ a c = c := hc ⟨a, ha⟩
    have hw0 : W.toSubmodule.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
    have haw0 : W.toSubmodule.mkQ (ρ a w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (W.apply_mem_toSubmodule a hw)
    simp only [map_add, hcw, hw0, haw0]

/-- The lower invariant subspace inside the upper invariant subspace. -/
def sectionLower (U W : Subrepresentation ρ) : Subrepresentation W.toRepresentation where
  toSubmodule := U.toSubmodule.comap W.toSubmodule.subtype
  apply_mem_toSubmodule g := fun {_w} hw => U.apply_mem_toSubmodule g hw

/-- The literal representation on `W / (U ∩ W)`, and hence on `W/U` when `U ≤ W`. -/
def sectionRepresentation (U W : Subrepresentation ρ) :=
  (sectionLower ρ U W).quotientRepresentation

/-- Under containment, the denominator of the literal section is the given lower space. -/
def sectionLowerEquiv {U W : Subrepresentation ρ} (hUW : U ≤ W) :
    (sectionLower ρ U W).toSubmodule ≃ₗ[ZMod 2] U.toSubmodule :=
  Submodule.comapSubtypeEquivOfLe hUW

omit [FiniteDimensional (ZMod 2) V] in
/-- The section kernel consists exactly of transformations whose displacements
on the upper space lie in the lower space. -/
theorem sectionRepresentation_trivial_iff (U W : Subrepresentation ρ) (g : G) :
    (∀ s, sectionRepresentation ρ U W g s = s) ↔
      ∀ w ∈ W.toSubmodule, ρ g w - w ∈ U.toSubmodule := by
  constructor
  · intro h w hw
    have he := h ((sectionLower ρ U W).toSubmodule.mkQ ⟨w, hw⟩)
    exact (Submodule.Quotient.eq (sectionLower ρ U W).toSubmodule).mp he
  · intro h s
    induction s using Submodule.Quotient.induction_on with
    | _ w =>
      exact (Submodule.Quotient.eq (sectionLower ρ U W).toSubmodule).mpr
        (h w w.property)

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem sectionRepresentation_mk (U W : Subrepresentation ρ) (g : G)
    (w : W.toSubmodule) :
    sectionRepresentation ρ U W g ((sectionLower ρ U W).toSubmodule.mkQ w) =
      (sectionLower ρ U W).toSubmodule.mkQ (W.toRepresentation g w) := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem sectionLower_trivial_iff {U W : Subrepresentation ρ} (hUW : U ≤ W)
    (A : Subgroup G) :
    fixedSpace (sectionLower ρ U W).toRepresentation A = ⊤ ↔
      U.toSubmodule ≤ fixedSpace ρ A := by
  constructor
  · intro h u hu a
    let v : (sectionLower ρ U W).toSubmodule := ⟨⟨u, hUW hu⟩, hu⟩
    have hv : v ∈ fixedSpace (sectionLower ρ U W).toRepresentation A := by rw [h]; trivial
    exact congrArg (fun x : (sectionLower ρ U W).toSubmodule => (x.val : V)) (hv a)
  · intro h
    apply top_unique
    intro v _ a
    apply Subtype.ext
    apply Subtype.ext
    exact h v.property a

theorem fixedCodim_section_le (U W : Subrepresentation ρ) (A : Subgroup G) :
    fixedCodim (sectionRepresentation ρ U W) A ≤ fixedCodim ρ A := by
  have hq := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation
    (sectionLower ρ U W) A
  have hw := fixedCodim_subrepresentation_le ρ W A
  change fixedCodim (sectionRepresentation ρ U W) A + _ ≤ _ at hq
  omega
end Representation.BinaryOffender
