module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The actual Sylow two-subgroups of an odd triple cover of A₆

The quotient map is injective on every two-subgroup because its kernel has
order three. Its Sylow image is a Sylow subgroup of A₆, giving a literal
isomorphism with D8, and hence the exact orders eight and two for the Sylow
subgroup and its center.

Source application: Aschbacher–Smith B.4.2(8) and 13.7.15(1).
-/

public section
open Subgroup
namespace Representation.TripleSixSmallMoved
variable {G : Type*} [Group G] [Finite G]
  (q : G →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
  (hk : Nat.card q.ker = 3)
include q hq hk

/-- The given quotient map identifies every Sylow two-subgroup with D8. -/
theorem sylow_dihedral (T : Sylow 2 G) : Nonempty (T ≃* DihedralGroup 4) := by
  let S := T.mapSurjective hq
  have hf := injective_comp_subtype_of_coprime_ker q
    (show Nat.Coprime 2 (Nat.card q.ker) by rw [hk]; decide) (T : Subgroup G) T.isPGroup'
  let e : T ≃* S := MulEquiv.ofBijective (q.subgroupMap (T : Subgroup G))
    ⟨fun x y h => hf (congrArg Subtype.val h),q.subgroupMap_surjective _⟩
  obtain ⟨d⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral S
  exact ⟨e.trans d⟩

/-- The two cardinalities used by the common-center obstruction. -/
theorem sylow_card_and_center (T : Sylow 2 G) :
    Nat.card T = 8 ∧ Nat.card (center T) = 2 := by
  obtain ⟨e⟩ := sylow_dihedral q hq hk T
  constructor
  · rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,Nat.card_eq_fintype_card]
    decide +kernel
end Representation.TripleSixSmallMoved
