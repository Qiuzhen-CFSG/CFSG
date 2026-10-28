module
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension

/-!
# Three-free solvable radicals in normal two-extensions

Restrict the quotient map to the ambient solvable radical. Its kernel
embeds in the normal subgroup's radical, while its image is a two-group.
The order formula proves that divisibility by three cannot appear in the
extension. The literal kernel inclusion is retained.

Source application: Aschbacher–Smith 15.2.4, printed p.1107.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal two-extension preserves a solvable radical of order prime to three. -/
theorem radical_primeTo_three_of_normal_two_quotient (K : Subgroup G) [K.Normal]
    (hK : ¬ 3 ∣ Nat.card (solvableRadical K)) (hq : IsPGroup 2 (G ⧸ K)) :
    ¬ 3 ∣ Nat.card (solvableRadical G) := by
  let A := solvableRadical G
  let f := (QuotientGroup.mk' K).subgroupMap A
  let j : f.ker →* solvableRadical K :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp
        (congrArg Subtype.val x.property)⟩, by
        rw [←radical_subgroupOf_normal K]
        exact x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  have hk : ¬ 3 ∣ Nat.card f.ker := fun h => hK (h.trans (Subgroup.card_dvd_of_injective j hj))
  have hi : ¬ 3 ∣ Nat.card (A.map (QuotientGroup.mk' K)) := by
    obtain ⟨n,hn⟩ := (hq.to_subgroup (A.map (QuotientGroup.mk' K))).exists_card_eq
    rw [hn]
    intro h
    have hh := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at hh
  have hc := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr ((QuotientGroup.mk' K).subgroupMap_surjective A),card_top] at hc
  exact fun h => (Nat.prime_three.dvd_mul.mp (hc.symm ▸ h)).elim hk hi

end Theory.GroupTheory
