module

public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A displacement kernel of index at most two

Suppose every displacement of a supplied point lies in a subgroup M fixed
pointwise by the actor group. If the quotient of M by the native intersection
with R has order at most two, there is an actor subgroup of index at most two
whose displacements lie in R. Its explicit cardinal lower bound is retained.
No commutativity, elementary-group, or faithful-action hypothesis is needed.

The point displacement is a homomorphism because its values are fixed by
all actors. Restrict its codomain to M, compose with the actual quotient, and
take the kernel. The kernel quotient identifies with a subgroup of M/R;
the ordinary subgroup index/cardinality formula gives the cardinal bound.

This is the elementary kernel construction used in Stellmacher (9.10),
printed p.57, after the displacement bound modulo the terminal center. An
index-at-most-two subgroup suffices for the later intersection obstruction,
so no arbitrary coatom is selected when the displacement map is trivial.
-/

public theorem exists_large_subgroup_of_fixed_displacement_quotient
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (M R : Subgroup V) [(R.subgroupOf M).Normal]
    (hfixed : ∀ a : A, ∀ m ∈ M, a • m = m)
    (point : V) (hdisplacement : ∀ a : A, point⁻¹ * (a • point) ∈ M)
    (hquotient : Nat.card (M ⧸ R.subgroupOf M) ≤ 2) :
    ∃ K : Subgroup A, K.index ≤ 2 ∧ Nat.card A ≤ 2 * Nat.card K ∧
      ∀ a ∈ K, point⁻¹ * (a • point) ∈ R := by
  let displacement : A →* M :=
    { toFun := fun a => ⟨point⁻¹ * (a • point), hdisplacement a⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change point⁻¹ * ((a * b) • point) =
          (point⁻¹ * (a • point)) * (point⁻¹ * (b • point))
        calc
          point⁻¹ * ((a * b) • point) = point⁻¹ * (a • (b • point)) := by rw [mul_smul]
          _ = point⁻¹ * (a • (point * (point⁻¹ * (b • point)))) := by
            rw [mul_inv_cancel_left]
          _ = (point⁻¹ * (a • point)) * (a • (point⁻¹ * (b • point))) := by
            rw [smul_mul', mul_assoc]
          _ = (point⁻¹ * (a • point)) * (point⁻¹ * (b • point)) := by
            rw [hfixed a _ (hdisplacement b)] }
  let quotient : A →* M ⧸ R.subgroupOf M :=
    (QuotientGroup.mk' (R.subgroupOf M)).comp displacement
  have hindex : quotient.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group quotient.range).trans hquotient
  have hcard : Nat.card A ≤ 2 * Nat.card quotient.ker := by
    have hproduct := quotient.ker.index_mul_card
    rw [← hproduct]
    exact Nat.mul_le_mul_right _ hindex
  refine ⟨quotient.ker, hindex, hcard, ?_⟩
  intro a ha
  change QuotientGroup.mk' (R.subgroupOf M) (displacement a) = 1 at ha
  exact (QuotientGroup.eq_one_iff (N := R.subgroupOf M) (displacement a)).mp ha
