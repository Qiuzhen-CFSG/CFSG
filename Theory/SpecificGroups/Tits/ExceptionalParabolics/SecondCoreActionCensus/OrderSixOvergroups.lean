module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterModel
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic
/-!
# Marked order-six overgroups in the second-core outer model

An order-six subgroup containing the specified transposition has an element
of order three. Its central coordinate is trivial. The order of its product
with the transposition rules out the two cubic subgroups producing a
four-cycle. The remaining cubic subgroups are exchanged by (2 3), which fixes
the marked transposition, including its central coordinate. Each resulting
subgroup contains the same standard pair, whose orders force equality.

Only the 24 permutations of four points and the four central coordinates
are checked by finite kernel reduction; subgroups are not enumerated.
This is the small conjugacy input to the actual core-action reduction.
Source context: Aschbacher--Smith F.1.12 and14.2.21, printed pp.263,988--989.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open Subgroup
private def cycle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
private def exchange : OuterModel := (1, Equiv.swap 2 3)
private def cubic : OuterModel := (1, cycle)
private def standard (w : BinaryPair) : Subgroup OuterModel :=
  closure {markedTransposition w, cubic}
private theorem central_cube : ∀ x : BinaryPair, x ^ 3 = 1 → x = 1 := by decide +kernel
private theorem cycle_order : orderOf cubic = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel
private theorem marking_order (w : BinaryPair) : orderOf (markedTransposition w) = 2 := by
  apply orderOf_eq_prime
  · revert w; decide +kernel
  · revert w; decide +kernel
private theorem cubic_cases : ∀ p : Equiv.Perm (Fin 4),
    p ^ 3 = 1 → p ≠ 1 → (Equiv.swap 0 1 * p) ^ 6 = 1 →
    (p = cycle ∨ p = cycle⁻¹) ∨
    ((Equiv.swap 2 3 * p * (Equiv.swap 2 3)⁻¹) = cycle ∨
      (Equiv.swap 2 3 * p * (Equiv.swap 2 3)⁻¹) = cycle⁻¹) := by
  decide +kernel
private theorem exchange_marking (w : BinaryPair) :
    MulAut.conj exchange (markedTransposition w) = markedTransposition w := by
  revert w
  decide +kernel
private theorem cubic_normalize (w : BinaryPair) (x : OuterModel)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (htx : (markedTransposition w * x) ^ 6 = 1) :
    ∃ b : OuterModel, MulAut.conj b (markedTransposition w) = markedTransposition w ∧
      (MulAut.conj b x = cubic ∨ MulAut.conj b x = cubic⁻¹) := by
  have hxcentral : x.1 = 1 := central_cube x.1 (congrArg Prod.fst hx3)
  have hxp : x.2 ≠ 1 := by
    intro h
    exact hx1 (Prod.ext hxcentral h)
  have hc := cubic_cases x.2 (congrArg Prod.snd hx3) hxp (congrArg Prod.snd htx)
  rcases hc with hc | hc
  · refine ⟨1, by simp, ?_⟩
    rcases hc with hc | hc
    · left; simpa [cubic] using Prod.ext hxcentral hc
    · right; simpa [cubic] using Prod.ext hxcentral hc
  · refine ⟨exchange, exchange_marking w, ?_⟩
    exact hc.imp (fun h => Prod.ext (by simp [exchange, cubic, hxcentral]) h)
      (fun h => Prod.ext (by simp [exchange, cubic, hxcentral]) h)

private theorem standard_card_lower (w : BinaryPair) : 6 ≤ Nat.card (standard w) := by
  have ht : markedTransposition w ∈ standard w := subset_closure (by simp)
  have hc : cubic ∈ standard w := subset_closure (by simp)
  have htord : orderOf (⟨markedTransposition w, ht⟩ : standard w) = 2 :=
    ((orderOf_injective (standard w).subtype (standard w).subtype_injective _).symm).trans
      (marking_order w)
  have hcord : orderOf (⟨cubic, hc⟩ : standard w) = 3 :=
    ((orderOf_injective (standard w).subtype (standard w).subtype_injective _).symm).trans
      cycle_order
  have htwo : 2 ∣ Nat.card (standard w) := by
    simpa only [htord] using _root_.orderOf_dvd_natCard
      (x := (⟨markedTransposition w, ht⟩ : standard w))
  have hthree : 3 ∣ Nat.card (standard w) := by
    simpa only [hcord] using _root_.orderOf_dvd_natCard
      (x := (⟨cubic, hc⟩ : standard w))
  exact Nat.le_of_dvd Nat.card_pos ((show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd
    htwo hthree)

private theorem normalize_order_six (w : BinaryPair) (U : Subgroup OuterModel)
    (ht : markedTransposition w ∈ U) (hU : Nat.card U = 6) :
    ∃ b : OuterModel, U.map (MulAut.conj b).toMonoidHom = standard w := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 (by rw [hU]; decide)
  have hx3 : (x : OuterModel) ^ 3 = 1 :=
    congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  have hx1 : (x : OuterModel) ≠ 1 := by
    intro h
    have he : x = 1 := Subtype.ext h
    simp [he] at hx
  have htx : (markedTransposition w * (x : OuterModel)) ^ 6 = 1 :=
    congrArg Subtype.val (hU ▸ pow_card_eq_one' (x := (⟨markedTransposition w, ht⟩ : U) * x))
  obtain ⟨b, hbt, hbx⟩ := cubic_normalize w x hx3 hx1 htx
  refine ⟨b, ?_⟩
  have hle : standard w ≤ U.map (MulAut.conj b).toMonoidHom := by
    apply (closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hbt ▸ mem_map_of_mem _ ht
    · obtain rfl := Set.mem_singleton_iff.mp ha
      rcases hbx with hbx | hbx
      · exact hbx ▸ mem_map_of_mem _ x.property
      · have hh : cubic⁻¹ ∈ U.map (MulAut.conj b).toMonoidHom :=
          hbx ▸ mem_map_of_mem _ x.property
        exact inv_mem_iff.mp hh
  apply (eq_of_le_of_card_ge hle _).symm
  rw [← Nat.card_congr (U.equivMapOfInjective (MulAut.conj b).toMonoidHom
    (MulAut.conj b).injective).toEquiv]
  exact hU ▸ standard_card_lower w

theorem marked_order_six_conjugacy (w : BinaryPair) (U V : Subgroup OuterModel)
    (htU : markedTransposition w ∈ U) (htV : markedTransposition w ∈ V)
    (hU : Nat.card U = 6) (hV : Nat.card V = 6) :
    ∃ b : OuterModel, U.map (MulAut.conj b).toMonoidHom = V := by
  obtain ⟨u, hu⟩ := normalize_order_six w U htU hU
  obtain ⟨v, hv⟩ := normalize_order_six w V htV hV
  refine ⟨v⁻¹ * u, ?_⟩
  have he := congrArg (Subgroup.map (MulAut.conj v⁻¹).toMonoidHom) (hu.trans hv.symm)
  have hleft : (MulAut.conj v⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (v⁻¹ * u)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hright : (MulAut.conj v⁻¹).toMonoidHom.comp (MulAut.conj v).toMonoidHom =
      MonoidHom.id OuterModel := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    group
  simpa only [Subgroup.map_map, hleft, hright, Subgroup.map_id] using he

end Tits.ExceptionalParabolics.SecondCoreAction
