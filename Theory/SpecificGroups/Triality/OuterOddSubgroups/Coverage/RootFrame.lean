module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.RootData

/-!
# Signed root coordinates for triality automorphism coverage

The coefficient action already defined on the elementary central quotient
preserves each of the four signed simple-root curves. On the arm curves it
uses the full cubic coefficient automorphism, and on the central curves it
uses its restriction to the actual q-Frobenius fixed field. We verify these
formulas before using them to identify automorphisms from root coordinates.

The generation and root-frame recognition needed for full coverage remain
explicit in the conditional extensionality results. No automorphism
classification is asserted in this module, including at q = 2.

Source: GLS3 2.5.1 and 2.5.8 (`refs/KGroup/GLS3/chapter2.tex`), and
Steinberg, Theorem 36 and Theorem 30, steps (1)--(4)
(`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage
open Parabolics ConcreteBruhat ElementaryCentralKernel

/-- The literal four signed simple-root curves in the central quotient. -/
def rootGenerators (P : Parameters) (hp : P.prime = 2) : Set (Carrier P) :=
  {x | ∃ s a t, x = rootElement P hp s a t}

/-- Preservation of each signed simple-root group, with its original parametrization. -/
def PreservesRootFrame (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) : Prop :=
  ∀ s i, a '' Set.range (rootElement P hp s i) = Set.range (rootElement P hp s i)

theorem coefficient_frobenius (P : Parameters) (e : CoefficientAut P)
    (t : ExtensionField P) : e (fieldFrobenius P t) = fieldFrobenius P (e t) := by
  simp only [fieldFrobenius_apply, map_pow]

/-- Cubic coefficient automorphisms preserve the actual q-Frobenius fixed field. -/
theorem coefficient_mem_fixedField (P : Parameters) (e : CoefficientAut P)
    (t : fixedField P) : e t.val ∈ fixedField P := by
  exact (coefficient_frobenius P e t.val).symm.trans
    (congrArg e (show fieldFrobenius P t.val = t.val from t.property))

/-- Restriction of the cubic coefficient automorphism to the actual fixed field. -/
def coefficientFixedField (P : Parameters) (e : CoefficientAut P) :
    fixedField P ≃+* fixedField P where
  toFun t := ⟨e t.val, coefficient_mem_fixedField P e t⟩
  invFun t := ⟨e.symm t.val, coefficient_mem_fixedField P e.symm t⟩
  left_inv t := Subtype.ext (e.symm_apply_apply t.val)
  right_inv t := Subtype.ext (e.apply_symm_apply t.val)
  map_mul' t u := Subtype.ext (map_mul e t.val u.val)
  map_add' t u := Subtype.ext (map_add e t.val u.val)

/-- The coefficient map on each of the two different root fields. -/
def coefficientRootField (P : Parameters) (e : CoefficientAut P) :
    (i : Node) → RootField P i ≃+* RootField P i
  | .arms => e
  | .central => coefficientFixedField P e

private theorem coefficient_simpleRoot (P : Parameters) (e : CoefficientAut P)
    (s : Bool) (i : Fin 4) (t : ExtensionField P) :
    coefficientSplit P e (simpleRoot P s i t) = simpleRoot P s i (e t) := by
  cases s
  · exact coefficientSplit_negative P e _ t
  · exact coefficientSplit_positive P e _ t

private theorem coefficient_rootElementary (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (s : Bool) (i : Node) (t : RootField P i) :
    coefficientElementary P e (rootElementary P hp s i t) =
      rootElementary P hp s i (coefficientRootField P e i t) := by
  apply Subtype.ext
  apply Subtype.ext
  cases i with
  | central => exact coefficient_simpleRoot P e s 1 t.val
  | arms =>
    change coefficientSplit P e (foldedRoot P s t) = foldedRoot P s (e t)
    simp only [foldedRoot, map_mul, coefficient_simpleRoot, coefficient_frobenius]

/-- The actual coefficient action has the expected formula on both signs and fields. -/
theorem coefficientAction_rootElement (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (s : Bool) (i : Node) (t : RootField P i) :
    coefficientAction P e (rootElement P hp s i t) =
      rootElement P hp s i (coefficientRootField P e i t) := by
  exact congrArg (toCarrier P) (coefficient_rootElementary P hp e s i t)

theorem coefficientAction_preservesRootFrame (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) : PreservesRootFrame P hp (coefficientAction P e) := by
  intro s i
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (coefficientAction_rootElement P hp e s i t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := (coefficientRootField P e i).surjective t
    exact ⟨rootElement P hp s i u, ⟨u, rfl⟩,
      coefficientAction_rootElement P hp e s i u⟩

/-- Agreement on the signed root curves extends to the carrier once generation is supplied. -/
theorem ext_of_rootGenerators (P : Parameters) (hp : P.prime = 2)
    (hgen : Subgroup.closure (rootGenerators P hp) = ⊤)
    {a b : MulAut (Carrier P)}
    (h : ∀ s i t, a (rootElement P hp s i t) = b (rootElement P hp s i t)) : a = b := by
  apply MulEquiv.ext
  intro x
  have he : Subgroup.closure (rootGenerators P hp) ≤
      MonoidHom.eqLocus a.toMonoidHom b.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s, i, t, rfl⟩
    exact h s i t
  exact he (hgen.symm ▸ Subgroup.mem_top x)

/-- Scalar and common-field root formulas yield the actual inner--coefficient expression. -/
theorem eq_inner_coefficient_of_root_formulas (P : Parameters) (hp : P.prime = 2)
    (hgen : Subgroup.closure (rootGenerators P hp) = ⊤)
    (a : MulAut (Carrier P)) (g : Carrier P) (e : CoefficientAut P)
    (h : ∀ s i t, a (rootElement P hp s i t) =
      g * rootElement P hp s i (coefficientRootField P e i t) * g⁻¹) :
    a = MulAut.conj g * coefficientAction P e := by
  apply ext_of_rootGenerators P hp hgen
  intro s i t
  change _ = g * coefficientAction P e (rootElement P hp s i t) * g⁻¹
  rw [coefficientAction_rootElement]
  exact h s i t

end Triality.Standard.OuterOdd.Coverage
