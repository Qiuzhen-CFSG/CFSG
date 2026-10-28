module
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.CComponent.SolvableQuotient

/-!
# Perfect factors in a normal supplement

Distinct C-components commute modulo the solvable radical. More generally,
a perfect subgroup A of N B lies in the normal subgroup N whenever [A,B]
is solvable: in the quotient by N its perfect image is also solvable.

The consumer is the exchanged-component comparison in Aschbacher--Smith
14.6.15, printed p.1035. It upgrades the literal action-kernel placement
K₁ ≤ J K₂ to K₁ ≤ J without identifying J with an ordinary centralizer.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A perfect subgroup of a normal supplement lies in the normal subgroup
when its commutator with the supplement is solvable. -/
theorem perfect_le_normal_of_le_sup_of_solvable_commutator
    (A B N : Subgroup G) [Group.IsPerfect A] [N.Normal]
    [Group.IsSolvable (⁅A,B⁆ : Subgroup G)] (h : A ≤ N ⊔ B) : A ≤ N := by
  let q := QuotientGroup.mk' N
  let : Group.IsPerfect (A.map q) := Group.IsPerfect.map q
  have hab : A.map q ≤ B.map q := by
    have hm := map_mono (f := q) h
    have hn : N.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    simpa only [Subgroup.map_sup,hn,bot_sup_eq] using hm
  have hc : A.map q ≤ (⁅A,B⁆ : Subgroup G).map q := by
    rw [←commutator_eq_self (H := A.map q),map_commutator]
    exact commutator_mono le_rfl hab
  let : Group.IsSolvable ((⁅A,B⁆ : Subgroup G).map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let : Group.IsSolvable (A.map q) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)
  have hb : A.map q = ⊥ := by
    by_contra hn
    let : Nontrivial (A.map q) := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (A.map q) inferInstance
  simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hb

/-- Distinct C-components commute modulo the solvable radical. -/
theorem IsCComponent.commutator_le_solvableRadical_of_ne [Finite G]
    {A B : Subgroup G} (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B) :
    ⁅A,B⁆ ≤ solvableRadical G := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hc := (hA.map_quotient (solvableRadical G)).commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G)) (hB.map_quotient (solvableRadical G))
    (fun he => hne (hA.eq_of_map_quotient_eq hB (solvableRadical G) he))
  simpa only [←map_commutator,Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hc

end Subgroup
