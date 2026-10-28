module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.Nilpotent

/-!
# The nonabelian three-primary part of a central extension

If a finite nonabelian group has central derived subgroup of exponent dividing
three, it is nilpotent of class at most two. Its Sylow three-subgroup is
therefore characteristic. The central derived subgroup lies in this Sylow
subgroup, and transfer puts it in the Sylow subgroup's own derived subgroup.
Thus that characteristic three-subgroup is nonabelian.

This isolates the group-theoretic part of the central extraspecial-three case
in GLS3, Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`. No minimal-normal
subgroup choice or identification of a group of order 27 is needed for the
solvability consumer.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

/-- A nonabelian characteristic three-subgroup detects the central cubic derived subgroup. -/
public theorem exists_characteristic_nonabelian_three_subgroup
    {G : Type*} [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (hcube : ∀ x ∈ commutator G, x ^ 3 = 1)
    (hnonab : ¬ IsMulCommutative G) :
    ∃ Q : Subgroup G, Q.Characteristic ∧ IsPGroup 3 Q ∧ ¬ IsMulCommutative Q := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Group.IsNilpotent G := by
    apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    refine ⟨2, Subgroup.lowerCentralSeries_succ_eq_bot ⊤ ?_⟩
    simpa only [Subgroup.top_lowerCentralSeries_one] using hcentral
  let S : Sylow 3 G := default
  have hchar : (S : Subgroup G).Characteristic := S.characteristic_of_normal inferInstance
  have hd : IsPGroup 3 (commutator G) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hcube x.val x.property
  have hle : commutator G ≤ (S : Subgroup G) := hd.le_sylow_of_normal S
  refine ⟨S, hchar, S.isPGroup', ?_⟩
  intro hcomm
  have hz : ⁅(S : Subgroup G), (S : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr hcomm
  apply hnonab
  apply (commutator_eq_bot_iff G).mp
  apply le_bot_iff.mp
  intro x hx
  have h := Subgroup.center_inf_commutator_inf_sylow_le_commutator S
    (show x ∈ (Subgroup.center G ⊓ commutator G) ⊓ (S : Subgroup G) from
      ⟨⟨hcentral hx, hx⟩, hle hx⟩)
  rwa [hz] at h

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian
