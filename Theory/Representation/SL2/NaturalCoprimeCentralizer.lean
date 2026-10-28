module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import Theory.SpecificGroups.SL2.AffineFreeAction

/-!
# Odd actors on literal natural SL₂ sections

A nonidentity odd-order determinant-one matrix in characteristic two
fixes no nonzero vector: a matrix fixing such a vector is unipotent.
Equivariance therefore puts the centralizer of an odd actor in the
actual denominator of a natural conjugation section. No choice of a
split torus or alteration of the coordinate map is required.

This is the natural-layer step in DGS, Groups and Graphs (1985),
proof of (12.9), printed p.189, applied to Z_alpha, W/H and Q_alpha/C.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL2
variable {G k : Type*} [Group G] [Field k] [Algebra (ZMod 2) k]

/-- An odd-order nonidentity matrix has no nonzero natural fixed vector. -/
theorem natural_odd_fixed_eq_zero (g : SL(2,k)) (ho : Odd (orderOf g))
    (hne : g ≠ 1) (v : Fin 2 → k) (hv : Matrix.mulVec g.val v = v) : v = 0 := by
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  by_contra hn
  exact hne (Matrix.SpecialLinearGroup.AffineFreeAction.eq_one_of_fixed_vector_of_coprime
    g (p := 2) (Nat.coprime_two_left.mpr ho) (pow_orderOf_eq_one g) v hn hv)

/-- The centralizer of an odd actor in a natural section lies in its literal kernel. -/
theorem natural_section_odd_centralizer_le
    {A U N : Subgroup G} (π : A →* SL(2,k))
    (d : BinaryConjugationSection A U N (SL2NaturalOffenders.NoStrong.natural.comp π))
    (a : A) (ho : Odd (orderOf a)) (hne : π a ≠ 1) :
    U ⊓ centralizer ({(a : G)} : Set G) ≤ N := by
  rintro u ⟨hu,hc⟩
  let z : U := ⟨u,hu⟩
  have hconj : (⟨(a : G) * z * (a : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized a.property) z).mp z.property⟩ : U) = z := by
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_singleton_iff.mp hc).symm
  have hv : Matrix.mulVec (π a).val (d.coordinates z).toAdd = (d.coordinates z).toAdd := by
    have hh := (d.equivariant a z).symm
    rw [hconj] at hh
    exact hh
  have hz := natural_odd_fixed_eq_zero (π a) (ho.of_dvd_nat (orderOf_map_dvd π a)) hne _ hv
  exact (d.coordinates_eq_one_iff z).mp (Multiplicative.toAdd.injective hz)
end Representation.SL2
