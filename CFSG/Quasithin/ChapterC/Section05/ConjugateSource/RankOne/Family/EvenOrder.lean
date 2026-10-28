module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Pair
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Mathlib.GroupTheory.GroupAction.Period

/-!
# Even order from the natural two-member family

Conjugation preserves maximum elementary subgroups. The original x moves
Q because Uˣ does not centralize U, so it exchanges the two members of the
proved family. This orbit has period two, dividing the order of x.

Source: Aschbacher–Smith, C.5.6(5) and C.5.7, printed pp.157,160.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- The original conjugator exchanges the two literal cores. -/
theorem Setup.conjugate_core_swap (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) :
    ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = Q R L := by
  let e := MulAut.conj x⁻¹
  let Q' := (Q R L).map e.toMonoidHom
  have hne : Q' ≠ Q R L := by
    intro he
    exact hnc (((map_mono (f := e.toMonoidHom) h.module_le_core).trans_eq he).trans
      (h.core ▸ inf_le_right))
  have hm : Q' ∈ elementaryAbelianMaxSubgroups (S R) := by
    rw [h.maximum_family hx hnc hphi]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hmap := (maxFamily_map_injective_iff e.toMonoidHom e.injective (S R) Q').mpr hm
  rw [h.stable hx, h.maximum_family hx hnc hphi] at hmap
  rcases Set.mem_insert_iff.mp hmap with he | he
  · exact he
  · have he := Set.mem_singleton_iff.mp he
    exact (hne ((map_injective e.injective) he)).elim

/-- In the Φ(D)=1 source case, the original x has even order. -/
theorem Setup.even_order_of_frattini_eq_bot (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) : Even (orderOf x) := by
  let e := MulAut.conj x⁻¹
  have hswap := h.conjugate_core_swap hx hnc hphi
  have hfix : e ^ 2 • Q R L = Q R L := by
    rw [pow_two, mul_smul]
    exact hswap
  have hd := MulAction.pow_smul_eq_iff_period_dvd.mp hfix
  have hn : MulAction.period e (Q R L) ≠ 1 := by
    intro he
    have hm := MulAction.period_eq_one_iff.mp he
    have hQ : (Q R L).map e.toMonoidHom = Q R L := hm
    exact hnc (((map_mono (f := e.toMonoidHom) h.module_le_core).trans_eq hQ).trans
      (h.core ▸ inf_le_right))
  have hp : MulAction.period e (Q R L) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  apply even_iff_two_dvd.mpr
  have he := (hp ▸ MulAction.period_dvd_orderOf e (Q R L)).trans
    (orderOf_map_dvd MulAut.conj x⁻¹)
  simpa only [orderOf_inv] using he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
