module

public import Theory.SpecificGroups.MinusExtraspecial.CubicAction

/-!
# The fixed subgroup of the standard cubic automorphism

In quaternion–dihedral coordinates, the fixed elements are precisely the
embedded dihedral factor. Thus the fixed subgroup has order eight. The
calculation takes place on the actual extraspecial group, including its center.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262,
and the quaternion–dihedral coordinates on p.265.
-/

@[expose] public section
namespace MinusExtraspecial.CubicAction

def fixedSubgroup : Subgroup Model := cycle.toMonoidHom.eqLocus (MonoidHom.id Model)

theorem mem_fixedSubgroup (q : Model) : q ∈ fixedSubgroup ↔ cycle q = q := Iff.rfl

theorem fixedSubgroup_eq_dihedral_range : fixedSubgroup = dihedral.range := by
  ext q
  exact (show ∀ q : Model, cycle q = q ↔ ∃ d : DihedralGroup 4, dihedral d = q from
    by decide +kernel) q

theorem fixedSubgroup_card : Nat.card fixedSubgroup = 8 := by
  rw [fixedSubgroup_eq_dihedral_range,
    ← Nat.card_congr (MonoidHom.ofInjective dihedral_injective).toEquiv,
    DihedralGroup.nat_card]

end MinusExtraspecial.CubicAction
