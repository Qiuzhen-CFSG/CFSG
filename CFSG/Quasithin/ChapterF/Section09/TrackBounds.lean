module

public import CFSG.Quasithin.ChapterF.Section09.TrackSetup
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.IntersectingCommutativity

/-!
# Original F.9 track bounds from commuting intersecting conjugates

The actual F.7 seed maps back to V, including after conjugation. Thus
intersection commutativity in the original ambient group excludes an even
critical pair. Containment in the actual O₂(H) gives track greater than one.
Together these prove the original odd lower bound, with no assumed parity
or critical-length conclusion. Source: F.7.11(2), F.9.11 and 13.8.3--4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
open Section07
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

private theorem seed_conjugate_map (g : G₀ (D:=D)) :
    (h.f7Setup.seed.map (MulAut.conj g).toMonoidHom).map (D.LT⊔D.H).subtype =
      D.V.map (MulAut.conj (g:G)).toMonoidHom := by
  rw [map_map]
  have he : (D.LT⊔D.H).subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g:G)).toMonoidHom.comp (D.LT⊔D.H).subtype := by ext; rfl
  rw [he,←map_map,h.f7Seed_map]

theorem odd_b_of_intersecting_conjugates_commute
    (hc : ∀g:G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) : Odd h.b := by
  apply CriticalPairs.odd_track_of_intersecting_conjugates_commute
    (family (D:=D)) h.f7Setup h.f7V_ne_bot
  intro g hg
  have hmap : (h.f7Setup.seed ⊓ h.f7Setup.seed.map (MulAut.conj g).toMonoidHom).map
      (D.LT⊔D.H).subtype = D.V ⊓ D.V.map (MulAut.conj (g:G)).toMonoidHom := by
    rw [map_inf _ _ _ (D.LT⊔D.H).subtype_injective,h.f7Seed_map,h.seed_conjugate_map]
  have hi : D.V ⊓ D.V.map (MulAut.conj (g:G)).toMonoidHom ≠⊥ := by
    intro he
    apply hg
    exact (map_eq_bot_iff_of_injective _ (D.LT⊔D.H).subtype_injective).mp (hmap.trans he)
  apply (map_eq_bot_iff_of_injective _ (D.LT⊔D.H).subtype_injective).mp
  rw [map_commutator,h.f7Seed_map,h.seed_conjugate_map]
  exact hc g hi

theorem f7Seed_le_true_core (hc : D.V≤D.QH) :
    h.f7Setup.seed ≤ (family (D:=D) true).pCoreIn 2 := by
  apply (map_le_map_iff_of_injective (D.LT⊔D.H).subtype_injective).mp
  rw [h.f7Seed_map,←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (D.LT⊔D.H).subtype_injective,
    show (family (D:=D) true).map (D.LT⊔D.H).subtype=D.H from map_subgroupOf_eq_of_le le_sup_right]
  exact hc

theorem b_bounds_of_intersecting_conjugates_commute (hcore : D.V≤D.QH)
    (hc : ∀g:G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) : 3≤h.b ∧ Odd h.b := by
  have ho:=h.odd_b_of_intersecting_conjugates_commute hc
  have hb:=CriticalPairs.Completion.one_lt_track_of_true_core
    (family (D:=D)) h.f7Setup h.f7V_ne_bot (h.f7Seed_le_true_core hcore)
  exact ⟨by obtain ⟨k,hk⟩:=ho; change 1<h.b at hb; omega,ho⟩
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
