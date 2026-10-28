module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.NoncentralPoint

/-!
# The Sylow size obstruction to singular fusion

Conjugating a two-subgroup of one element centralizer into another bounds its
order by the actual Sylow subgroup there. When the suitable centralizer has
index four in T, a two-subgroup of order at least half of T cannot centralize
a conjugate of the suitable vector. This is the comparison used with the
singular centralizers; it does not assume fusion control.

Source: Aschbacher--Smith, 14.6.17(4), printed p.1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
variable {G : Type*} [Group G] [Finite G]

theorem conjugate_centralizer_card_le
    (u w : G) (Tu B : Subgroup G)
    (hTu : Chapter1.IsSylowIn 2 Tu (centralizer ({u} : Set G)))
    (hB : IsPGroup 2 B) (hBc : B ≤ centralizer ({w} : Set G))
    (hc : IsConj u w) : Nat.card B ≤ Nat.card Tu := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let C := centralizer ({u} : Set G)
  let K := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hKC : K ≤ C := by
    rintro x ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := mem_centralizer_singleton_iff.mp (hBc hb)
    rw [←hg] at he
    have he' := congrArg (MulAut.conj g⁻¹) he
    simpa [MulAut.conj_apply,mul_assoc] using he'
  obtain ⟨R,hR⟩ := hTu
  obtain ⟨P,hP⟩ := ((hB.map (MulAut.conj g⁻¹).toMonoidHom).comap_subtype :
    IsPGroup 2 (K.subgroupOf C)).exists_le_sylow
  calc
    Nat.card B = Nat.card K := (card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ = Nat.card (K.subgroupOf C) := (Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv).symm
    _ ≤ Nat.card P := Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)
    _ = Nat.card R := by rw [P.card_eq_multiplicity,R.card_eq_multiplicity]
    _ = Nat.card Tu := by rw [←hR,card_map_of_injective C.subtype_injective]

theorem not_isConj_of_centralizer_size
    (T : Subgroup G) (u w : G)
    (hTu : Chapter1.IsSylowIn 2 (T ⊓ centralizer ({u} : Set G))
      (centralizer ({u} : Set G)))
    (hi : (T ⊓ centralizer ({u} : Set G)).relIndex T = 4)
    (B : Subgroup G) (hB : IsPGroup 2 B)
    (hBc : B ≤ centralizer ({w} : Set G))
    (hlarge : Nat.card T ≤ 2 * Nat.card B) : ¬ IsConj u w := by
  intro hc
  let Tu := T ⊓ centralizer ({u} : Set G)
  have hb := conjugate_centralizer_card_le u w Tu B hTu hB hBc hc
  have he := (Tu.subgroupOf T).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Tu ≤ T from inf_le_left)).toEquiv] at he
  change Nat.card Tu * Tu.relIndex T = Nat.card T at he
  rw [hi] at he
  have hp : 0 < Nat.card Tu := Nat.card_pos
  omega

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
