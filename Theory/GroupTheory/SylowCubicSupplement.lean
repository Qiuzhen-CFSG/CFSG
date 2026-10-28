module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow and cubic generation for groups of order dividing twelve

A subgroup containing a Sylow two-subgroup has odd index. If it also contains
an element of order three, its index divides four, hence is one. The range
variant lifts this criterion through a homomorphism whose kernel is contained
in the subgroup. It applies to the actual outer action in the first paragraph
of Aschbacher--Smith 15.3.38, printed p.1136.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A Sylow two-subgroup and any cubic element generate a group of order dividing twelve. -/
theorem eq_top_of_card_dvd_twelve {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ∣ 12) (P : Sylow 2 H) (K : Subgroup H)
    (hPK : (P : Subgroup H) ≤ K) (x : H) (hx : x ∈ K) (hx3 : orderOf x = 3) :
    K = ⊤ := by
  have hxK : 3 ∣ Nat.card K := by
    have he : orderOf (⟨x, hx⟩ : K) = 3 :=
      (Subgroup.orderOf_coe ⟨x, hx⟩).symm.trans hx3
    rw [← he]
    exact orderOf_dvd_natCard _
  have hmul : 3 * K.index ∣ 3 * 4 :=
    (Nat.mul_dvd_mul_right hxK K.index).trans (K.card_mul_index ▸ hcard)
  have hi : K.index ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by decide) hmul
  have hc : Nat.Coprime 4 (P : Subgroup H).index := by
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr P.not_dvd_index).pow_left 2
  exact index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hc hi (index_dvd_of_le hPK))

/-- Pull back the Sylow and cubic generation criterion along an actual homomorphism. -/
theorem eq_top_of_range_card_dvd_twelve {H J : Type*} [Group H] [Group J] [Finite H]
    (f : H →* J) (hcard : Nat.card f.range ∣ 12) (P : Sylow 2 H) (K : Subgroup H)
    (hker : f.ker ≤ K) (hPK : (P : Subgroup H) ≤ K)
    (x : H) (hx : x ∈ K) (hx3 : orderOf (f x) = 3) : K = ⊤ := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have he : K.map f.rangeRestrict = ⊤ :=
    eq_top_of_card_dvd_twelve hcard (P.mapSurjective f.rangeRestrict_surjective)
      (K.map f.rangeRestrict) (map_mono hPK) (f.rangeRestrict x)
      (mem_map_of_mem _ hx) ((Subgroup.orderOf_coe (f.rangeRestrict x)).symm.trans hx3)
  have hker' : f.rangeRestrict.ker ≤ K := by
    simpa only [MonoidHom.ker_rangeRestrict] using hker
  have hh := congrArg (Subgroup.comap f.rangeRestrict) he
  rwa [comap_map_eq_self hker', comap_top] at hh

end Theory.GroupTheory
