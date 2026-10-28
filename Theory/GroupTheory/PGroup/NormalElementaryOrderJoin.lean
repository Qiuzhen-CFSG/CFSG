module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The join of normal elementary subgroups of a fixed order

An isomorphism permutes the normal elementary abelian subgroups of a specified
order. Their join is therefore characteristic. This construction does not
require choosing one member of that family, and remains invariant when an
automorphism exchanges its members.

The Held application uses the two normal elementary subgroups of order 64 in
a Sylow two-subgroup; their individual normalizers need not be invariant.
Source context: GLS3, interpretation of Tables 5.3a--z and Table 5.3p.
-/

@[expose] public section

namespace Subgroup

variable (p n : ℕ) (G : Type*) [Group G]

/-- The join of all normal elementary abelian `p`-subgroups of order `n`. -/
def normalElementaryOrderJoin : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E.Normal) (_ : IsElementaryAbelian p E)
    (_ : Nat.card E = n), E

theorem le_normalElementaryOrderJoin (E : Subgroup G) (hn : E.Normal)
    (he : IsElementaryAbelian p E) (hc : Nat.card E = n) :
    E ≤ normalElementaryOrderJoin p n G :=
  le_iSup_of_le E (le_iSup_of_le hn (le_iSup_of_le he (le_iSup_of_le hc le_rfl)))

variable {G} {H : Type*} [Group H] [Fact p.Prime]

private theorem map_normalElementaryOrderJoin_le (e : G ≃* H) :
    (normalElementaryOrderJoin p n G).map e.toMonoidHom ≤
      normalElementaryOrderJoin p n H := by
  simp only [normalElementaryOrderJoin, map_iSup, iSup_le_iff]
  intro E hn he hc
  let := he
  apply le_normalElementaryOrderJoin
  · exact hn.map e.toMonoidHom e.surjective
  · exact IsElementaryAbelian.map e.toMonoidHom
  · rw [card_map_of_injective e.injective, hc]

/-- The construction is functorial under actual group isomorphisms. -/
theorem map_normalElementaryOrderJoin (e : G ≃* H) :
    (normalElementaryOrderJoin p n G).map e.toMonoidHom =
      normalElementaryOrderJoin p n H := by
  apply le_antisymm (map_normalElementaryOrderJoin_le p n e)
  have h := map_mono (f := e.toMonoidHom)
    (map_normalElementaryOrderJoin_le p n e.symm)
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  simpa only [map_map, hid, map_id] using h

instance normalElementaryOrderJoin_characteristic :
    (normalElementaryOrderJoin p n G).Characteristic :=
  characteristic_iff_map_eq.mpr (map_normalElementaryOrderJoin p n)

end Subgroup
