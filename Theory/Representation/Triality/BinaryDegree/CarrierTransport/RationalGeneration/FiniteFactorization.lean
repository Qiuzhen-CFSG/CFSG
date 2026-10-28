module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.RootWords
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.FiniteFactorization.Hyperbolic
import Mathlib.Tactic

/-!
# Rational symmetry factorization of the natural Spin action

An entrywise rational hyperbolic isometry restricts to an isometry over the
finite coefficient subfield. The inverse is rational because the injective
restriction acts on a finite vector space. Factoring this restricted isometry
and extending its anisotropic vectors gives symmetries over the same field.
Compatibility of the quadratic form, polar form and symmetry formula proves
that the ordered products agree on the rational basis, hence everywhere.

The final theorem supplies the rational factorization premise of
`CarrierTransport.RationalGeneration` directly from the literal natural matrix.
The cubic coefficient field has cardinality 2^(3*n), greater than two even at
n = 1. The induction in `FiniteFactorization.Hyperbolic` thus applies without
algebraic closure of the coefficient field or an additional generation premise.

Sources: GLS3, Remarks 2.2.5 and §2.7, and §§1.10–1.12 of Chapter 1.
The symmetry convention is Clifford conjugation; `List.prod` acts by foldr,
with the rightmost symmetry first.
-/

open scoped BigOperators
noncomputable section
namespace Theory.AlgebraicGroup.RationalOrthogonal.FiniteFactorization
open Triality.SimplyConnected
variable {k : Type*} [Field k] (F : Subfield k)

private def includeVector (v : HyperbolicSpace F 4) : HyperbolicSpace k 4 :=
  (fun i => (v.1 i : k), fun i => (v.2 i : k))

private theorem includeVector_injective : Function.Injective (includeVector F) := by
  intro v w h
  apply Prod.ext <;> funext i <;> apply Subtype.ext
  · exact congrArg (fun z => z.1 i) h
  · exact congrArg (fun z => z.2 i) h

private theorem includeVector_add (v w : HyperbolicSpace F 4) :
    includeVector F (v + w) = includeVector F v + includeVector F w := by
  ext <;> simp [includeVector]

private theorem includeVector_sub (v w : HyperbolicSpace F 4) :
    includeVector F (v - w) = includeVector F v - includeVector F w := by
  ext <;> simp [includeVector]

private theorem includeVector_smul (c : F) (v : HyperbolicSpace F 4) :
    includeVector F (c • v) = (c : k) • includeVector F v := by
  ext <;> simp [includeVector]

private theorem includeVector_form (v : HyperbolicSpace F 4) :
    hyperbolicForm 4 (includeVector F v) = (hyperbolicForm 4 v : F) := by
  simp [hyperbolicForm_apply, includeVector]

private theorem includeVector_polar (v w : HyperbolicSpace F 4) :
    QuadraticMap.polar (hyperbolicForm 4) (includeVector F v) (includeVector F w) =
      (QuadraticMap.polar (hyperbolicForm 4) v w : F) := by
  simp only [QuadraticMap.polar, ← includeVector_add, includeVector_form, Subfield.coe_sub]

private theorem includeVector_coordinates (v : HyperbolicSpace F 4) :
    HasCoordinates F (includeVector F v) :=
  ⟨fun i => (v.1 i).property, fun i => (v.2 i).property⟩

private def descendVector (v : HyperbolicSpace k 4) (hv : HasCoordinates F v) :
    HyperbolicSpace F 4 :=
  (fun i => ⟨v.1 i, hv.1 i⟩, fun i => ⟨v.2 i, hv.2 i⟩)

private theorem includeVector_descend (v : HyperbolicSpace k 4) (hv : HasCoordinates F v) :
    includeVector F (descendVector F v hv) = v := rfl

private theorem coordinates_iff_repr (v : HyperbolicSpace k 4) :
    HasCoordinates F v ↔ ∀ i, (hyperbolicBasis k).repr v i ∈ F := by
  constructor
  · intro hv i
    cases i with
    | inl i => simpa [hyperbolicBasis, Pi.basisFun_repr] using hv.1 i
    | inr i => simpa [hyperbolicBasis, Pi.basisFun_repr] using hv.2 i
  · intro hv
    constructor
    · intro i
      simpa [hyperbolicBasis, Pi.basisFun_repr] using hv (Sum.inl i)
    · intro i
      simpa [hyperbolicBasis, Pi.basisFun_repr] using hv (Sum.inr i)

private theorem preserves_coordinates
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F)
    (v : HyperbolicSpace k 4) (hv : HasCoordinates F v) :
    HasCoordinates F (g.1 v) := by
  apply (coordinates_iff_repr F _).mpr
  intro i
  have hr := (coordinates_iff_repr F v).mp hv
  rw [← (hyperbolicBasis k).sum_repr v, map_sum, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hr j) (hg i j)

private def restrictedLinearMap
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F) :
    HyperbolicSpace F 4 →ₗ[F] HyperbolicSpace F 4 where
  toFun v := descendVector F (g.1 (includeVector F v))
    (preserves_coordinates F g hg _ (includeVector_coordinates F v))
  map_add' v w := by
    apply includeVector_injective F
    simp only [includeVector_descend, includeVector_add, map_add]
  map_smul' c v := by
    apply includeVector_injective F
    simp only [includeVector_descend, includeVector_smul, map_smul, RingHom.id_apply]

private theorem includeVector_restrict
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F)
    (v : HyperbolicSpace F 4) :
    includeVector F (restrictedLinearMap F g hg v) = g.1 (includeVector F v) := rfl

private theorem restricted_injective
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F) :
    Function.Injective (restrictedLinearMap F g hg) := by
  intro v w h
  apply includeVector_injective F
  apply g.1.injective
  exact congrArg (includeVector F) h

/-- The rational restriction is injective on a finite vector space, hence
surjective. Its inverse therefore has coordinates in the same field. -/
private theorem inverse_coordinates [Fintype F]
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F)
    (v : HyperbolicSpace k 4) (hv : HasCoordinates F v) :
    HasCoordinates F (g.1.symm v) := by
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective (restricted_injective F g hg)
    (descendVector F v hv)
  have hw' : g.1 (includeVector F w) = v := congrArg (includeVector F) hw
  rw [← hw', g.1.symm_apply_apply]
  exact includeVector_coordinates F w

private def restrictedIsometry [Fintype F]
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F) :
    (hyperbolicForm (k := F) 4).IsometryEquiv (hyperbolicForm 4) where
  toLinearEquiv :=
    { restrictedLinearMap F g hg with
      invFun v := descendVector F (g.1.symm (includeVector F v))
        (inverse_coordinates F g hg _ (includeVector_coordinates F v))
      left_inv v := by
        apply includeVector_injective F
        change g.1.symm (g.1 (includeVector F v)) = includeVector F v
        exact g.1.symm_apply_apply _
      right_inv v := by
        apply includeVector_injective F
        change g.1 (g.1.symm (includeVector F v)) = includeVector F v
        exact g.1.apply_symm_apply _ }
  map_app' v := by
    apply Subtype.val_injective
    change ((hyperbolicForm 4 (restrictedLinearMap F g hg v) : F) : k) =
      (hyperbolicForm 4 v : F)
    rw [← includeVector_form, includeVector_restrict, ← includeVector_form]
    exact (mem_quadraticIsometrySubgroup _ _).mp g.2 _

private def liftAnisotropic (a : AnisotropicVector (hyperbolicForm (k := F) 4)) :
    AnisotropicVector (hyperbolicForm (k := k) 4) :=
  ⟨includeVector F a.1, by
    rw [includeVector_form]
    exact_mod_cast a.2⟩

private theorem includeVector_symmetry
    (a : AnisotropicVector (hyperbolicForm (k := F) 4)) (v : HyperbolicSpace F 4) :
    includeVector F (conjugationSymmetry (hyperbolicForm 4) a.1 a.2 v) =
      conjugationSymmetry (hyperbolicForm 4) (liftAnisotropic F a).1
        (liftAnisotropic F a).2 (includeVector F v) := by
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  change includeVector F (((hyperbolicForm 4 a.1)⁻¹ *
    QuadraticMap.polar (hyperbolicForm 4) a.1 v) • a.1 - v) =
      ((hyperbolicForm 4 (includeVector F a.1))⁻¹ *
        QuadraticMap.polar (hyperbolicForm 4) (includeVector F a.1)
          (includeVector F v)) • includeVector F a.1 - includeVector F v
  rw [includeVector_sub, includeVector_smul, includeVector_form, includeVector_polar]
  rfl

private theorem includeVector_product
    (as : List (AnisotropicVector (hyperbolicForm (k := F) 4))) (v : HyperbolicSpace F 4) :
    includeVector F ((symmetryProductPoint as).1 v) =
      (symmetryProductPoint (as.map (liftAnisotropic F))).1 (includeVector F v) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      change includeVector F (conjugationSymmetry (hyperbolicForm 4) a.1 a.2
        ((symmetryProductPoint as).1 v)) =
          conjugationSymmetry (hyperbolicForm 4) (liftAnisotropic F a).1
            (liftAnisotropic F a).2
            ((symmetryProductPoint (as.map (liftAnisotropic F))).1 (includeVector F v))
      rw [includeVector_symmetry, ih]

private theorem includeVector_basis (j : Fin 4 ⊕ Fin 4) :
    includeVector F (hyperbolicBasis F j) = hyperbolicBasis k j := by
  classical
  cases j <;> ext i <;>
    simp [includeVector, hyperbolicBasis, Pi.basisFun_apply, Pi.single_apply, apply_ite]

/-- A rational hyperbolic isometry factors into symmetries over the same
finite coefficient field, with the literal ordered-product convention. -/
public theorem factorization [Fintype F] (hcard : 2 < Fintype.card F)
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (hg : ∀ i j, (hyperbolicBasis k).repr (g.1 (hyperbolicBasis k j)) i ∈ F) :
    ∃ as : List (AnisotropicVector (hyperbolicForm (k := k) 4)),
      (∀ a ∈ as, HasCoordinates F a.1) ∧ symmetryProductPoint as = g := by
  obtain ⟨as, has⟩ := FiniteSymmetryFactorization.hyperbolic_factorization hcard 4
    (restrictedIsometry F g hg)
  have hfac (v : HyperbolicSpace F 4) :
      (symmetryProductPoint as).1 v = restrictedIsometry F g hg v := by
    rw [symmetryProductPoint_apply]
    simpa only [conjugationSymmetry_apply] using (has v).symm
  refine ⟨as.map (liftAnisotropic F), ?_, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact includeVector_coordinates F b.1
  · apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (hyperbolicBasis k).ext
    intro j
    change (symmetryProductPoint (as.map (liftAnisotropic F))).1 (hyperbolicBasis k j) =
      g.1 (hyperbolicBasis k j)
    rw [← includeVector_basis F j, ← includeVector_product, hfac]
    exact includeVector_restrict F g hg _

end Theory.AlgebraicGroup.RationalOrthogonal.FiniteFactorization

namespace Triality.BinaryDegree.CarrierTransport
open Triality.Standard Triality.SimplyConnected Theory.AlgebraicGroup
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Every actual Spin point whose natural matrix is rational over GF(2^(3*n))
has a symmetry factorization with all anisotropic vectors over that field.
No parity or root-generation premise is required. -/
public theorem exists_rational_symmetryFactorization [CharP k 2] {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) (g : Points k)
    (hg : ∀ i j : Fin 4 ⊕ Fin 4, naturalMatrix k g i j ∈ f.range) :
    ∃ as : List (AnisotropicVector (quadraticForm k)),
      (∀ a ∈ as, RationalOrthogonal.HasCoordinates f.fieldRange a.1) ∧
        symmetryProductPoint as = naturalAction k g := by
  classical
  let K := ExtensionField (binaryParameters n hn)
  let : Fintype K := Fintype.ofFinite K
  let : Fintype f.fieldRange := RingHom.fintypeFieldRange f
  have hcardK : Fintype.card K = 2 ^ (3 * n) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (3 * n) (by omega)
  have hcardF : Fintype.card f.fieldRange = Fintype.card K :=
    (Fintype.card_congr (Equiv.ofInjective f f.injective)).symm
  have hlarge : 2 < Fintype.card f.fieldRange := by
    rw [hcardF, hcardK]
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact RationalOrthogonal.FiniteFactorization.factorization f.fieldRange hlarge
    (naturalAction k g) hg

end Triality.BinaryDegree.CarrierTransport
