module

public import Theory.SpecificGroups.JankoTwo.TwoRank
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound
public import Theory.GroupTheory.TwoKernelAbelianBounds

/-!
# Elementary subgroups in actual perfect central covers of Hall--Janko

The proved central-kernel bound is at most two, and the native quotient
has two-rank at most four. Thus every finite perfect central cover has
two-rank at most five and cannot contain an elementary group of order 64.
The quotient map and its whole kernel are retained. In particular, the
ordinary quasisimple source needs no assumed multiplier or odd-center
bound in order to apply the obstruction.

Source application: Aschbacher--Smith 12.7.5, printed p.840.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2

/-- The entire finite perfect central cover of J₂ has two-rank at most five. -/
theorem perfect_central_cover_primeRank_two_le_five
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) : primeRank 2 E ≤ 5 := by
  exact primeRank_le_succ_of_kernel_card_le_two f
    (Theory.SpecificGroups.J2HSMultipliers.J2.kernel_card_le_two f hf hk)
    primeRank_two_le_four

/-- Every elementary subgroup of the original perfect cover has order at most 32. -/
theorem perfect_central_cover_elementary_card_le_thirty_two
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (A : Subgroup E) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 32 :=
  (primeRank_le_iff_elementary_card_le E).mp
    (perfect_central_cover_primeRank_two_le_five f hf hk) A inferInstance

/-- The original elementary 64 cannot lie in a quasisimple J₂ component. -/
theorem quasisimple_elementary_sixty_four_false
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (e : (E ⧸ center E) ≃* Carrier)
    (A : Subgroup E) [IsElementaryAbelian 2 A] (hA : Nat.card A = 64) : False := by
  let f : E →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hsmall := perfect_central_cover_elementary_card_le_thirty_two f hf hk.le A
  omega

end Sporadic.LeechRelated.J2
