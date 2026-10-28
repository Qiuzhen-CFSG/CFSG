module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The binary natural module for SL₂(4)

We use the computable field `F₂[a]`, with `a² = a + 1`, and restrict the
natural column-vector action of SL₂ to F₂. The field and vector identifications
with `GaloisField 2 2` are actual equivalences, and `standard_equivariant`
identifies the actions. Coordinatewise squaring is an F₂-linear involution
intertwining the natural action with entrywise Frobenius on SL₂.

The fixed space of Frobenius has four elements; the common fixed space of
all upper unipotents is the F₄-line with second coordinate zero. Intersecting
these two fixed spaces leaves two elements. Explicit determinant-one matrices
prove transitivity on nonzero vectors. The determinant of two columns is
SL₂-invariant and transforms by squaring under Frobenius; it is the coordinate
input for the binary-plane orbit calculations.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §6.2, printed pp.680--681 (PDF pp.697--698),
especially the natural-module calculations in 6.2.2 and 6.2.5. This module
does not assert the ambient-group conclusions or the plane orbit counts.
The quadratic field implementation also occurs in
`Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Coordinates`; we use its
underlying Mathlib construction directly to avoid a dependency on the Witt
design.
-/

@[expose] public section

namespace Representation.SL2FourNatural
/-- A concrete field of four elements. -/
abbrev F := QuadraticAlgebra (ZMod 2) 1 1
instance noRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩
instance fieldFintype : Fintype F :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm
instance fieldCharP : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
/-- The natural two-dimensional F₄-space, also carrying its binary structure. -/
abbrev V := Fin 2 → F
/-- The actual determinant-one matrix group on the natural module. -/
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) F
lemma card_field : Fintype.card F = 4 := by decide +kernel
lemma card_vector : Fintype.card V = 16 := by decide +kernel
/-- Identification of the concrete quadratic field with the canonical finite field. -/
noncomputable def fieldEquiv : F ≃+* GaloisField 2 2 := by
  letI := Fintype.ofFinite (GaloisField 2 2)
  apply FiniteField.ringEquivOfCardEq
  rw [card_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  norm_num

/-- The natural matrix action restricted to F₂. -/
def action : SL →* (V ≃ₗ[ZMod 2] V) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun Matrix.SpecialLinearGroup.toLin'.map_one v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun (Matrix.SpecialLinearGroup.toLin'.map_mul g h) v
lemma action_apply (g : SL) (v : V) : action g v = g.val.mulVec v := rfl
lemma action_natural (g : SL) (v : V) : action g v = specialLinearNatural 2 g v := rfl
lemma action_faithful : Function.Injective action := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact LinearEquiv.congr_fun he v

lemma pow_four (x : F) : x ^ 4 = x := by
  simpa only [card_field] using FiniteField.pow_card x

/-- The nontrivial field automorphism, given by squaring. -/
def fieldFrobenius : F ≃+* F :=
  { frobenius F 2 with
    invFun := frobenius F 2
    left_inv := fun x => by
      change (x ^ 2) ^ 2 = x
      simpa only [← pow_mul] using pow_four x
    right_inv := fun x => by
      change (x ^ 2) ^ 2 = x
      simpa only [← pow_mul] using pow_four x }
lemma fieldFrobenius_apply (x : F) : fieldFrobenius x = x ^ 2 := rfl
lemma fieldFrobenius_involutive (x : F) : fieldFrobenius (fieldFrobenius x) = x := by
  simpa only [fieldFrobenius_apply, ← pow_mul] using pow_four x
lemma fieldFrobenius_fixed (x : F) : fieldFrobenius x = x ↔ x = 0 ∨ x = 1 := by
  revert x
  decide +kernel

/-- Coordinatewise Frobenius as a binary linear equivalence. -/
def frobeniusLinear : V ≃ₗ[ZMod 2] V where
  toFun v i := fieldFrobenius (v i)
  invFun v i := fieldFrobenius (v i)
  left_inv v := by funext i; exact fieldFrobenius_involutive _
  right_inv v := by funext i; exact fieldFrobenius_involutive _
  map_add' v w := by funext i; exact map_add fieldFrobenius _ _
  map_smul' c v := by
    funext i
    change fieldFrobenius (c • v i) = c • fieldFrobenius (v i)
    fin_cases c
    · change fieldFrobenius ((0 : ZMod 2) • v i) = (0 : ZMod 2) • fieldFrobenius (v i)
      simp
    · change fieldFrobenius ((1 : ZMod 2) • v i) = (1 : ZMod 2) • fieldFrobenius (v i)
      simp
lemma frobeniusLinear_apply (v : V) (i : Fin 2) : frobeniusLinear v i = (v i)^2 := rfl
lemma frobeniusLinear_involutive (v : V) : frobeniusLinear (frobeniusLinear v) = v := by
  funext i
  exact fieldFrobenius_involutive _

/-- Entrywise Frobenius as an automorphism of SL₂(4). -/
def slFrobenius : MulAut SL :=
  { Matrix.SpecialLinearGroup.map fieldFrobenius.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map fieldFrobenius.toRingHom
    left_inv := fun A => by apply Subtype.ext; funext i j; exact fieldFrobenius_involutive (A i j)
    right_inv := fun A => by apply Subtype.ext; funext i j; exact fieldFrobenius_involutive (A i j) }
lemma slFrobenius_apply (A : SL) (i j : Fin 2) : slFrobenius A i j = (A i j)^2 := rfl
lemma frobenius_action (A : SL) (v : V) :
    frobeniusLinear (action A v) = action (slFrobenius A) (frobeniusLinear v) := by
  funext i
  change fieldFrobenius (∑ j, A i j * v j) = ∑ j, fieldFrobenius (A i j) * fieldFrobenius (v j)
  simp only [map_sum, map_mul]

/-- The fixed binary plane of coordinatewise Frobenius. -/
def fieldFixed : Submodule (ZMod 2) V := frobeniusLinear.toLinearMap.fixedSubmodule
lemma mem_fieldFixed (v : V) : v ∈ fieldFixed ↔ ∀ i, v i = 0 ∨ v i = 1 := by
  change (frobeniusLinear v = v) ↔ _
  rw [funext_iff]
  exact forall_congr' fun i => fieldFrobenius_fixed (v i)
lemma card_fieldFixed : Nat.card fieldFixed = 4 := by
  change Nat.card {v : V // frobeniusLinear v = v} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The upper unipotent matrix with the specified off-diagonal entry. -/
def upper (a : F) : SL := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
lemma upper_action (a : F) (v : V) : action (upper a) v = ![v 0 + a * v 1, v 1] := by
  rw [action_apply]
  funext i
  fin_cases i <;> simp [upper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma upper_fixed_iff (v : V) : (∀ a : F, action (upper a) v = v) ↔ v 1 = 0 := by
  constructor
  · intro h
    have := congrFun (h 1) 0
    simpa [upper_action] using this
  · intro h a
    rw [upper_action]
    funext i
    fin_cases i <;> simp [h]

/-- The common fixed space of all upper unipotent matrices. -/
def upperFixed : Submodule (ZMod 2) V := ⨅ a : F, (action (upper a)).toLinearMap.fixedSubmodule
lemma mem_upperFixed (v : V) : v ∈ upperFixed ↔ v 1 = 0 := by
  simp only [upperFixed, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
  exact upper_fixed_iff v
lemma card_upperFixed : Nat.card upperFixed = 4 := by
  have he : upperFixed ≃ {v : V // v 1 = 0} :=
    Equiv.subtypeEquivRight (fun v => mem_upperFixed v)
  rw [Nat.card_congr he, Nat.card_eq_fintype_card]
  decide +kernel
lemma card_upperFixed_inf_fieldFixed : Nat.card (upperFixed ⊓ fieldFixed : Submodule (ZMod 2) V) = 2 := by
  have he : (upperFixed ⊓ fieldFixed : Submodule (ZMod 2) V) ≃
      {v : V // v 1 = 0 ∧ ∀ i, v i = 0 ∨ v i = 1} :=
    Equiv.subtypeEquivRight (fun v => by simp [mem_upperFixed, mem_fieldFixed])
  rw [Nat.card_congr he, Nat.card_eq_fintype_card]
  decide +kernel

lemma finrank_vector : Module.finrank (ZMod 2) V = 4 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [Nat.card_eq_fintype_card, card_vector, Nat.card_eq_fintype_card, ZMod.card] at h
  have hp : (2 : ℕ) ^ 4 = 2 ^ Module.finrank (ZMod 2) V := h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hp).symm

/-- A nonzero vector can be completed to a determinant-one matrix. -/
lemma exists_first_column (v : V) (hv : v ≠ 0) : ∃ A : SL, action A ![1, 0] = v := by
  by_cases h : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h, h1]
    refine ⟨⟨(!![0, -(v 1)⁻¹; v 1, 0] : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · change ( !![0, -(v 1)⁻¹; v 1, 0] : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]
  · refine ⟨⟨(!![v 0, 0; v 1, (v 0)⁻¹] : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h]
    · change ( !![v 0, 0; v 1, (v 0)⁻¹] : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- SL₂(4) is transitive on the fifteen nonzero natural-module vectors. -/
lemma transitive_nonzero (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ A : SL, action A u = v := by
  obtain ⟨A, hA⟩ := exists_first_column u hu
  obtain ⟨B, hB⟩ := exists_first_column v hv
  refine ⟨B * A⁻¹, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, ← hA]
  simpa using hB

/-- The determinant of the two columns, the eventual invariant of binary planes. -/
def wedge (u v : V) : F := u 0 * v 1 - u 1 * v 0
lemma wedge_mulVec (A : Matrix (Fin 2) (Fin 2) F) (u v : V) :
    wedge (A.mulVec u) (A.mulVec v) = A.det * wedge u v := by
  simp only [wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring
lemma wedge_action (A : SL) (u v : V) : wedge (action A u) (action A v) = wedge u v := by
  rw [action_apply, action_apply, wedge_mulVec, A.property, one_mul]
lemma wedge_frobenius (u v : V) :
    wedge (frobeniusLinear u) (frobeniusLinear v) = fieldFrobenius (wedge u v) := by
  change fieldFrobenius (u 0) * fieldFrobenius (v 1) -
    fieldFrobenius (u 1) * fieldFrobenius (v 0) = fieldFrobenius (u 0 * v 1 - u 1 * v 0)
  rw [map_sub, map_mul, map_mul]

/-- Binary four-subgroups are actual subspaces of the scalar-restricted module. -/
abbrev Plane := {U : Submodule (ZMod 2) V // Nat.card U = 4}
/-- An actual F₄-line, viewed as a binary plane, not a group-family label. -/
def IsFieldLine (U : Submodule (ZMod 2) V) : Prop :=
  ∃ W : Submodule F V, Module.finrank F W = 1 ∧ W.restrictScalars (ZMod 2) = U

/-- The chosen field identification induces an actual group isomorphism. -/
noncomputable def standardGroupEquiv :
    SL ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  { Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map fieldEquiv.symm.toRingHom
    left_inv := fun A => by
      apply Subtype.ext
      funext i j
      exact fieldEquiv.symm_apply_apply (A i j)
    right_inv := fun A => by
      apply Subtype.ext
      funext i j
      exact fieldEquiv.apply_symm_apply (A i j) }

/-- Coordinates over the canonical field, with the binary linear structure retained. -/
noncomputable def standardVectorEquiv : V ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) where
  toFun v i := fieldEquiv (v i)
  invFun v i := fieldEquiv.symm (v i)
  left_inv v := by funext i; exact fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add fieldEquiv _ _
  map_smul' c v := by
    funext i
    change fieldEquiv (c • v i) = c • fieldEquiv (v i)
    fin_cases c
    · change fieldEquiv ((0 : ZMod 2) • v i) = (0 : ZMod 2) • fieldEquiv (v i)
      simp
    · change fieldEquiv ((1 : ZMod 2) • v i) = (1 : ZMod 2) • fieldEquiv (v i)
      simp

lemma standard_equivariant (A : SL) (v : V) :
    standardVectorEquiv (action A v) =
      specialLinearNatural 2 (standardGroupEquiv A) (standardVectorEquiv v) := by
  funext i
  change fieldEquiv (∑ j, A i j * v j) = ∑ j, fieldEquiv (A i j) * fieldEquiv (v j)
  simp only [map_sum, map_mul]

/-- The same map is semilinear over F₄, with coefficient automorphism Frobenius. -/
lemma frobeniusLinear_smul (a : F) (v : V) :
    frobeniusLinear (a • v) = fieldFrobenius a • frobeniusLinear v := by
  funext i
  exact map_mul fieldFrobenius a (v i)

lemma slFrobenius_involutive (A : SL) : slFrobenius (slFrobenius A) = A := by
  apply Subtype.ext
  funext i j
  exact fieldFrobenius_involutive (A i j)

/-- The coordinate identification also intertwines the actual field automorphisms. -/
lemma standard_frobenius (v : V) (i : Fin 2) :
    standardVectorEquiv (frobeniusLinear v) i = (standardVectorEquiv v i) ^ 2 :=
  map_pow fieldEquiv (v i) 2

end Representation.SL2FourNatural
