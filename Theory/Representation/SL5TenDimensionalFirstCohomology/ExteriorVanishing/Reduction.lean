module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.FirstCohomology
public import Mathlib.Algebra.Field.ZMod

/-!
# Finite relation system for exterior-power cocycles of SL₅(2)

The standard exterior basis identifies the action with its matrix of minors.
The elementary transvections generate SL₅(2), so their values determine a
crossed homomorphism. Their square, commuting, and Steinberg relations impose
an explicit finite linear system on those values. Exactness of this system
therefore implies that every crossed homomorphism is principal.

This module proves the coordinate identification, generation, relation equations,
and the reduction to first cohomology. It does not assert exactness of the finite
system; the exterior-square and exterior-cube calculations supply that input.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419, citing Jones--Parshall [JP76].
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL5TenDimensional
/-- Increasing exterior-basis indices, represented by fixed-size subsets. -/
abbrev ExteriorIndex (r : ℕ) := Set.powersetCard (Fin 5) r
/-- Coordinate vectors in the standard exterior basis. -/
abbrev ExteriorCoordinates (r : ℕ) := ExteriorIndex r → ZMod 2
/-- The exterior basis induced by the standard basis of the natural module. -/
noncomputable def exteriorBasis (r : ℕ) := (Pi.basisFun (ZMod 2) (Fin 5)).exteriorPower r
/-- The standard exterior-basis coordinate equivalence. -/
noncomputable def exteriorCoordinates (r : ℕ) :
    ExteriorModule r ≃ₗ[ZMod 2] ExteriorCoordinates r := (exteriorBasis r).equivFun

/-- Matrix of minors, with columns indexed by source exterior-basis vectors. -/
def exteriorMatrix (r : ℕ) (g : Group) :
    Matrix (ExteriorIndex r) (ExteriorIndex r) (ZMod 2) := fun s t =>
  (Matrix.of fun a b : Fin r => g.val
    (Set.powersetCard.ofFinEmbEquiv.symm s b)
    (Set.powersetCard.ofFinEmbEquiv.symm t a)).det

/-- The coefficient of the image of an exterior-basis vector is a minor. -/
theorem exteriorCoordinates_action_basis (r : ℕ) (g : Group) (s t : ExteriorIndex r) :
    exteriorCoordinates r (exteriorAction r g (exteriorBasis r t)) s =
      exteriorMatrix r g s t := by
  simp only [exteriorCoordinates, Module.Basis.equivFun_apply, exteriorBasis,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorAction_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, Module.Basis.coord_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, Function.comp_apply,
    Matrix.mulVec_single, exteriorMatrix]
  simp

/-- The coordinate equivalence intertwines the actual action and the minor matrix. -/
theorem exteriorCoordinates_action (r : ℕ) (g : Group) (v : ExteriorModule r) :
    exteriorCoordinates r (exteriorAction r g v) =
      (exteriorMatrix r g).mulVec (exteriorCoordinates r v) := by
  classical
  have hv := (exteriorBasis r).sum_equivFun v
  change (∑ t, exteriorCoordinates r v t • exteriorBasis r t) = v at hv
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul]
  ext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    exteriorCoordinates_action_basis]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

open OneCohomology
open Matrix.SpecialLinearGroup

/-- Binary elementary transvections, extended by the identity on the diagonal. -/
def elementary (i j : Fin 5) : Group :=
  if h : i ≠ j then transvection h 1 else 1

/-- A crossed homomorphism vanishes at the identity. -/
theorem cocycle_one {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) (f : cocycles ρ) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

/-- The elementary transvections generate SL₅(2). -/
theorem elementary_induction (P : Group → Prop) (hone : P 1)
    (he : ∀ i j, P (elementary i j))
    (hmul : ∀ g h, P g → P h → P (g * h)) (g : Group) : P g := by
  refine diagonal_transvection_induction' (ι := Fin 5) (F := ZMod 2) P g ?_ ?_ hmul
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : diag2n hij c hc = (1 : Group) := by
      apply Subtype.ext
      simp [diag2n_coe, hc1]
    rwa [hd]
  · intro i j hij a
    have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases ha with rfl | rfl
    · simpa using hone
    · simpa [elementary, hij] using he i j

/-- Crossed homomorphisms are determined by their elementary-generator values. -/
theorem cocycles_ext_elementary {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) (f h : cocycles ρ)
    (he : ∀ i j, f.val (elementary i j) = h.val (elementary i j)) : f = h := by
  apply Subtype.ext
  funext g
  apply elementary_induction (fun g => f.val g = h.val g)
    (by rw [cocycle_one, cocycle_one]) he _ g
  intro a b ha hb
  rw [f.property, h.property, ha, hb]

/-- Every elementary generator has square one. -/
theorem elementary_square (i j : Fin 5) : elementary i j * elementary i j = 1 := by
  unfold elementary
  split_ifs with hij
  · have h : -(1 : ZMod 2) = 1 := by decide
    simpa [h] using (transvection_mul_neg (F := ZMod 2) hij 1)
  · exact one_mul _

/-- Elementary generators with disjoint source-target incidences commute. -/
theorem elementary_commute (i j k l : Fin 5) (hil : i ≠ l) (hjk : j ≠ k) :
    elementary i j * elementary k l = elementary k l * elementary i j := by
  unfold elementary
  split_ifs with hij hkl
  · apply Subtype.ext
    simp only [coe_mul, transvection_coe, mul_add, add_mul, one_mul, mul_one,
      Matrix.single_mul_single_of_ne _ _ _ _ hjk,
      Matrix.single_mul_single_of_ne _ _ _ _ hil.symm, add_zero]
    abel
  · simp
  · simp
  · simp

/-- The elementary Steinberg relation in characteristic two. -/
theorem elementary_steinberg (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    elementary i j * (elementary j k * elementary i j) =
      elementary j k * elementary i k := by
  apply Subtype.ext
  simp only [elementary, dif_pos hij, dif_pos hjk, dif_pos hik, coe_mul,
    transvection_coe]
  simp only [mul_add, add_mul, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm,
    Matrix.single_mul_single_same, mul_one, add_zero]
  have h (a : Matrix (Fin 5) (Fin 5) (ZMod 2)) : a + a = 0 := by
    ext x y
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (a x y)
  abel_nf
  simp [two_smul, h]

/-- The elementary action in determinant coordinates. -/
def elementaryAction (r : ℕ) (i j : Fin 5) (v : ExteriorCoordinates r) :
    ExteriorCoordinates r := (exteriorMatrix r (elementary i j)).mulVec v

/-- Necessary linear relations for values of a crossed homomorphism on generators. -/
structure ElementaryRelations (r : ℕ) (x : Fin 5 → Fin 5 → ExteriorCoordinates r) : Prop where
  diagonal : ∀ i, x i i = 0
  square : ∀ i j, elementaryAction r i j (x i j) + x i j = 0
  commute : ∀ i j k l, i ≠ l → j ≠ k →
    elementaryAction r i j (x k l) + x i j =
      elementaryAction r k l (x i j) + x k l
  steinberg : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    elementaryAction r i j (elementaryAction r j k (x i j) + x j k) + x i j =
      elementaryAction r j k (x i k) + x j k

/-- Coordinates of the values of a crossed homomorphism on elementary generators. -/
noncomputable def cocycleCoordinates (r : ℕ) (f : cocycles (exteriorAction r)) :
    Fin 5 → Fin 5 → ExteriorCoordinates r :=
  fun i j => exteriorCoordinates r (f.val (elementary i j))

/-- The diagonal entries of the generator family are identities. -/
@[simp] theorem elementary_self (i : Fin 5) : elementary i i = 1 := by
  simp [elementary]

/-- Every actual crossed homomorphism satisfies the finite relation system. -/
theorem cocycleCoordinates_relations (r : ℕ) (f : cocycles (exteriorAction r)) :
    ElementaryRelations r (cocycleCoordinates r f) := by
  have hm (g h : Group) :
      exteriorCoordinates r (f.val (g * h)) =
        (exteriorMatrix r g).mulVec (exteriorCoordinates r (f.val h)) +
          exteriorCoordinates r (f.val g) := by
    rw [f.property, map_add, exteriorCoordinates_action]
  constructor
  · intro i
    simp [cocycleCoordinates, cocycle_one]
  · intro i j
    have h := hm (elementary i j) (elementary i j)
    rw [elementary_square, cocycle_one, map_zero] at h
    exact h.symm
  · intro i j k l hil hjk
    have h := congrArg (fun g => exteriorCoordinates r (f.val g))
      (elementary_commute i j k l hil hjk)
    rw [hm, hm] at h
    exact h
  · intro i j k hij hjk hik
    have h := congrArg (fun g => exteriorCoordinates r (f.val g))
      (elementary_steinberg i j k hij hjk hik)
    rw [hm, hm, hm] at h
    exact h

/-- Exactness of the finite relation system suffices for the full cocycle calculation. -/
theorem cocycles_principal_of_elementaryRelations (r : ℕ)
    (hexact : ∀ x : Fin 5 → Fin 5 → ExteriorCoordinates r,
      ElementaryRelations r x → ∃ v : ExteriorCoordinates r,
        ∀ i j, elementaryAction r i j v - v = x i j)
    (f : cocycles (exteriorAction r)) :
    ∃ v, principal (exteriorAction r) v = f := by
  obtain ⟨v, hv⟩ := hexact (cocycleCoordinates r f) (cocycleCoordinates_relations r f)
  refine ⟨(exteriorCoordinates r).symm v, ?_⟩
  apply cocycles_ext_elementary
  intro i j
  apply (exteriorCoordinates r).injective
  change exteriorCoordinates r
    (exteriorAction r (elementary i j) ((exteriorCoordinates r).symm v) -
      (exteriorCoordinates r).symm v) = cocycleCoordinates r f i j
  rw [map_sub, exteriorCoordinates_action, LinearEquiv.apply_symm_apply]
  exact hv i j

/-- Pass from exactness of the finite relation system to vanishing of H¹. -/
theorem h1_subsingleton_of_elementaryRelations (r : ℕ)
    (hexact : ∀ x : Fin 5 → Fin 5 → ExteriorCoordinates r,
      ElementaryRelations r x → ∃ v : ExteriorCoordinates r,
        ∀ i j, elementaryAction r i j v - v = x i j) :
    Subsingleton (H1 (exteriorAction r)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr (cocycles_principal_of_elementaryRelations r hexact)

end Representation.SL5TenDimensional
