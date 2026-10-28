module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Canonical coordinates of a normalized elementary binary section

The coordinate space is the additive copy of the literal quotient U/Z.
Its action is induced by the original H-conjugation action, so the section
marking introduces no model-identification premise.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] (H U Z : Subgroup G)
  [IsElementaryAbelian 2 U]
  (hUH : U ≤ H) (hHU : H ≤ normalizer (U : Set G))
  (hZU : Z ≤ U) (hHZ : H ≤ normalizer (Z : Set G))

include hUH hHU hZU hHZ

theorem exists_conjugation_coordinates :
    let N := Z.subgroupOf U
    ∃ ρ : Representation (ZMod 2) H (Additive (U ⧸ N)),
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
