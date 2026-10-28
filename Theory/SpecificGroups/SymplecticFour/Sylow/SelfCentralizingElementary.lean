module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CommutatorRows
public import Theory.ElementaryAbelian.Injective

/-!
# Self-centralizing elementary subgroups of an even symplectic four-group

Every elementary subgroup of the standard Sylow group lies in one of its two
elementary wings. A noncentral involution identifies its wing as its centralizer;
a central subgroup lies in both wings. Each wing has order q³. Extending an
arbitrary elementary subgroup to a Sylow group therefore shows that a
self-centralizing elementary subgroup has order at least q³.

Source: the symplectic Sylow calculation in Aschbacher--Smith, 2.5.7,
printed pp.555--556; used in the model inspection in 13.5.15, printed p.921.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The two root wings contain every elementary subgroup of the standard Sylow. -/
theorem elementary_le_wing (A : Subgroup (unipotent (F := F)))
    [IsElementaryAbelian 2 A] : ∃ i : Bool, A ≤ wing i := by
  by_cases hz : A ≤ center (unipotent (F := F))
  · exact ⟨false, hz.trans (center_le_wings.trans inf_le_left)⟩
  · obtain ⟨a, ha, haz⟩ := SetLike.not_le_iff_exists.mp hz
    have hp : a ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩)
    have hA : A ≤ centralizer ({a} : Set (unipotent (F := F))) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (A.le_centralizer ha b hb)
    rcases centralizer_involution a hp haz with h | h
    · exact ⟨false, h ▸ hA⟩
    · exact ⟨true, h ▸ hA⟩

/-- The actual symplectic model forces a self-centralizing elementary subgroup
to contain an entire root wing of a Sylow group. -/
theorem card_ge_of_selfCentralizing_elementary
    {G : Type*} [Group G] [Finite G] (e : G ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hC : centralizer (E : Set G) ≤ E) : Nat.card F ^ 3 ≤ Nat.card E := by
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let s : S ≃* unipotent (F := F) :=
    ((S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
      (Sylow.equiv P (unipotentSylow hF hn))
  let A := E.subgroupOf S
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hES
  let _ : IsElementaryAbelian 2 (A.map s.toMonoidHom) := IsElementaryAbelian.map _
  obtain ⟨i, hi⟩ := elementary_le_wing (A.map s.toMonoidHom)
  let W := (wing (F := F) i).comap s.toMonoidHom
  let _ : IsElementaryAbelian 2 (wing (F := F) i) := wing_elementary i
  let _ : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.comap_of_injective s.toMonoidHom s.injective _
  let B := W.map (S : Subgroup G).subtype
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hEB : E ≤ B := by
    intro a ha
    refine mem_map.mpr ⟨⟨a, hES ha⟩, ?_, rfl⟩
    exact hi (mem_map_of_mem s.toMonoidHom (show (⟨a, hES ha⟩ : S) ∈ A from ha))
  have hBE : B ≤ E :=
    (B.le_centralizer.trans (centralizer_le hEB)).trans hC
  have hW : W.map s.toMonoidHom = wing i :=
    map_comap_eq_self_of_surjective s.surjective _
  have hcard : Nat.card B = Nat.card F ^ 3 := by
    rw [show B = W.map (S : Subgroup G).subtype from rfl,
      card_map_of_injective (S : Subgroup G).subtype_injective]
    rw [← card_map_of_injective (f := s.toMonoidHom) s.injective, hW, card_wing]
  exact hcard ▸ Nat.card_le_card_of_injective (inclusion hBE) (inclusion_injective hBE)

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
