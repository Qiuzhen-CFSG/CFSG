module
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Normal moved groups from normal quotient images

For a normal elementary binary subgroup U and its faithful quotient action,
normality of the image of X implies normality of [U,X]. This uses the actual
conjugation formula and the identified displacement space; X itself need not
be normal. The terminal S₅ × S₃ module in Aschbacher--Smith 12.3.1, p.812,
uses this result for the original second residual subgroup.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (U : Set G))

include hq hker in
/-- Normality of an actor image suffices for normality of its literal moved group. -/
theorem commutator_normal_of_image_normal (X : Subgroup G) [(X.map q).Normal] :
    (⁅U,X⁆ : Subgroup G).Normal := by
  let ρ := representation U q hq hker
  refine ⟨fun x hx g => ?_⟩
  let v : Additive U := Additive.ofMul ⟨x, (commutator_le_left U X) hx⟩
  have hv : v ∈ commutatorSpace U X := hx
  rw [commutatorSpace_eq U q hq hker X] at hv
  have hg := subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
    (show (⊤ : Subgroup H) ≤ normalizer (X.map q : Set H) from le_normalizer_of_normal)
    (mem_top (q g)) v
  have hm := hg.mpr hv
  change ρ (q g) v ∈ subspaceCommutator (representation U q hq hker) ⊤ (X.map q) at hm
  rw [← commutatorSpace_eq U q hq hker X] at hm
  change ((ρ (q g) v).toMul : G) ∈ ⁅U,X⁆ at hm
  rwa [representation_apply] at hm

end Representation.NormalElementaryQuotient
