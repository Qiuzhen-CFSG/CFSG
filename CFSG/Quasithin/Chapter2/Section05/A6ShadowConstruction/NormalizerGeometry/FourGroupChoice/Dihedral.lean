module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral

/-!
# The actual inner dihedral factor in the terminal construction

Source: Aschbacher–Smith, printed pp.569–570. The compatible action identifies
`S_K` with the intersection of its image Sylow subgroup and the inner A₆.
The existing concrete permutation proof identifies this intersection with D₈.
Thus neither the dihedral identification nor its order is an extra model input.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- The inner Sylow factor is dihedral, through the actual compatible A₆ action. -/
public theorem Setup.sk_dihedral [Finite G] (d : Setup G) :
    Nonempty (d.sk ≃* DihedralGroup 4) := by
  let P := CoreReduction.imageSylow d
  let swap : CoreReduction.innerSylow P ≃* AlternatingSix.ShadowLocal.sylowInner P := {
    toFun a := ⟨⟨a, a.property.1⟩, a.property.2⟩
    invFun a := ⟨a.1, a.1.property, a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  obtain ⟨f⟩ := AlternatingSix.ShadowLocal.sylowInner_dihedral P
  exact ⟨(CoreReduction.skEquiv d).trans (swap.trans f)⟩

/-- The order of the actual inner Sylow factor. -/
public theorem Setup.sk_card [Finite G] (d : Setup G) : Nat.card d.sk = 8 := by
  obtain ⟨f⟩ := d.sk_dihedral
  rw [Nat.card_congr f.toEquiv, DihedralGroup.nat_card]

/-- A four-group cannot be contained in the distinguished cyclic line. -/
public theorem Setup.four_exists_noncentral (d : Setup G)
    (E : Subgroup G) [IsKleinFour E] : ∃ e ∈ E, e ∉ zpowers d.zK := by
  by_contra! h
  let f := inclusion (show E ≤ zpowers d.zK from h)
  exact IsKleinFour.not_isCyclic (isCyclic_of_injective f (inclusion_injective _))

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
