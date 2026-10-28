module
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates

/-!
# Coordinates for elementary quotients of nonabelian subgroups

An elementary binary quotient of a normalized subgroup has canonical
conjugation coordinates, even when its numerator is nonabelian. The
coordinate homomorphism is the original quotient projection, and its
kernel is the original relative denominator. This supplies the critical
central quotient in the nonblock component argument.

Source: the induced conjugation action on an invariant quotient.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] (H U Z : Subgroup G)
  [(Z.subgroupOf U).Normal] [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
  (hUH : U ≤ H) (hHU : H ≤ normalizer (U : Set G))
  (hZU : Z ≤ U) (hHZ : H ≤ normalizer (Z : Set G))
include hUH hHU hZU hHZ

theorem exists_elementary_quotient_coordinates :
    ∃ ρ : Representation (ZMod 2) H (Additive (U ⧸ Z.subgroupOf U)),
      Nonempty (BinaryConjugationSection H U Z ρ) := by
  let : Normalizes H U := ⟨hHU⟩
  let N := Z.subgroupOf U
  let : IsInvariant H U N := ⟨by
    intro h u
    exact (hHZ h.property) u⟩
  let : MulDistribMulAction H (U ⧸ N) := quotientMulDistribMulAction N inferInstance
  let ρ := elementaryRepresentation (p := 2) (MulDistribMulAction.toMulAut H (U ⧸ N))
  refine ⟨ρ,⟨{
    section_le := hUH
    kernel_le := hZU
    normalized := hHU
    coordinates := {
      toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' N u))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }⟩⟩
  · intro v
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective N v.toAdd.toMul
    exact ⟨u,congrArg (fun w => Multiplicative.ofAdd (Additive.ofMul w)) hu⟩
  · ext u
    change QuotientGroup.mk' N u = 1 ↔ u ∈ N
    exact QuotientGroup.eq_one_iff u
  · intro h u
    rfl
end Representation.BinaryConjugationSection
