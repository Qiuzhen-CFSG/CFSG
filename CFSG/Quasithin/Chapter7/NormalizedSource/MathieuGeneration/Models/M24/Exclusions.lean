module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Words
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Cubic
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Cosets
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction

/-!
# Excluding the native M₂₄ Cartan overgroups

The short obstruction words and cubic fusion exclude every double coset
except the small certified coset cover. This contradicts the three possible
Cartan product orders. Sylow conjugacy transfers the marked calculation to
an arbitrary ambient Sylow subgroup, preserving the actual subgroup and its
odd-order witness through a conjugation isomorphism.

Source: Aschbacher--Smith, Definition E.3.37 and Table 7.3.4,
printed pp.239 and 699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
open Subgroup Sporadic.Mathieu M24LocalGeometry
open SylowNormalizer PairOvergroups.Placement.TransitiveCoverage

private theorem prime_dvd_orderOf_of_cycle {p : ℕ} [Fact (Nat.Prime p)]
    (g : Equiv.Perm (Fin 24)) (x : Fin 24)
    (hfix : g x ≠ x) (hper : (g ^ p) x = x) : p ∣ orderOf g := by
  have he : Function.minimalPeriod g x = p := Function.minimalPeriod_eq_prime hper hfix
  rw [← he]
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  change (g ^ orderOf g) x = x
  rw [pow_orderOf_eq_one]
  rfl

private theorem cycle_dvd (H : Subgroup M24) (hS : candidate ≤ H)
    (i : Fin 510) (hi : representativePerm i ∈ H.map M24.subtype)
    (w : List (Fin 5)) (p : ℕ) [Fact p.Prime] (x : Fin 24)
    (hn : localWord i w x ≠ x) (hp : (localWord i w ^ p) x = x) :
    p ∣ Nat.card H :=
  (prime_dvd_orderOf_of_cycle _ _ hn hp).trans
    (((H.map M24.subtype).orderOf_dvd_natCard (localWord_mem H hS i hi w)).trans
      (H.card_map_dvd M24.subtype))

private theorem no_wrong_cubic (H : Subgroup M24) (h9 : ¬ 9 ∣ Nat.card H)
    (g : H) (u : Equiv.Perm (Fin 24)) (hu : u ∈ H.map M24.subtype)
    (hcube : u ^ 3 = 1)
    (hbad : (orderOf g = 15 ∧ u.supportᶜ.card = 0) ∨
      (orderOf g = 21 ∧ u.supportᶜ.card = 6)) : False := by
  have hne : u ≠ 1 := by
    intro h
    rcases hbad with hbad | hbad <;> rw [h] at hbad <;> norm_num at hbad
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ho : orderOf u = 3 := orderOf_eq_prime hcube hne
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.mp hu
  let X : H := ⟨x, hx⟩
  have hxorder : orderOf X = 3 := by
    change orderOf (⟨x, hx⟩ : H) = 3
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact (congrArg orderOf he).trans ho
  change x.val = u at he
  rcases hbad with hbad | hbad
  · have hp := cubic_fixed_nonempty H h9 g hbad.1 X hxorder
    change x.val.supportᶜ.Nonempty at hp
    rw [he] at hp
    have hpos := Finset.card_pos.mpr hp
    omega
  · have hp := cubic_fixed_card_zero H h9 g hbad.1 X hxorder
    change x.val.supportᶜ.card = 0 at hp
    rw [he] at hp
    omega

private theorem marked_no_seven (H : Subgroup M24) (hS : candidate ≤ H)
    (hcard : Nat.card H = 7168) : False := by
  have hb := identity_card_bound H hS (by
    intro i hi
    rcases seven_obstruction i with h | ⟨w, p, x, hp, hn, hx⟩
    · exact h
    have hprime : p.Prime := by rcases hp with rfl | rfl | rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hprime⟩
    have hd := cycle_dvd H hS i hi w p x hn hx
    rw [hcard] at hd
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num at hd)
  omega

private theorem marked_no_fifteen (H : Subgroup M24) (hS : candidate ≤ H)
    (hcard : Nat.card H = 15360) (g : H) (hg : orderOf g = 15) : False := by
  have hb := exceptional_card_bound H hS (by
    intro i hi
    rcases fifteen_obstruction i with h | ⟨w, hc, hf⟩ | ⟨w, p, x, hp, hn, hx⟩
    · rcases h with h | h | h | h | h <;> simp only [h] <;> tauto
    · exact (no_wrong_cubic H (by rw [hcard]; decide) g _
        (localWord_mem H hS i hi w) hc (Or.inl ⟨hg, hf⟩)).elim
    · have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
      let : Fact p.Prime := ⟨hprime⟩
      have hd := cycle_dvd H hS i hi w p x hn hx
      rw [hcard] at hd
      rcases hp with rfl | rfl | rfl <;> norm_num at hd)
  omega

private theorem marked_no_twentyone (H : Subgroup M24) (hS : candidate ≤ H)
    (hcard : Nat.card H = 21504) (g : H) (hg : orderOf g = 21) : False := by
  have hb := exceptional_card_bound H hS (by
    intro i hi
    rcases twentyone_obstruction i with h | ⟨w, hc, hf⟩ | ⟨w, p, x, hp, hn, hx⟩
    · rcases h with h | h <;> simp only [h] <;> tauto
    · exact (no_wrong_cubic H (by rw [hcard]; decide) g _
        (localWord_mem H hS i hi w) hc (Or.inr ⟨hg, hf⟩)).elim
    · have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
      let : Fact p.Prime := ⟨hprime⟩
      have hd := cycle_dvd H hS i hi w p x hn hx
      rw [hcard] at hd
      rcases hp with rfl | rfl | rfl <;> norm_num at hd)
  omega

/-- None of the three Cartan product orders occurs over a native Sylow subgroup
with its required odd element. -/
theorem no_cartan_overgroup (H : Subgroup M24) (S : Sylow 2 M24)
    (hS : (S : Subgroup M24) ≤ H)
    (hcase : Nat.card H = 7168 ∨
      (Nat.card H = 15360 ∧ ∃ g : H, orderOf g = 15) ∨
      (Nat.card H = 21504 ∧ ∃ g : H, orderOf g = 21)) : False := by
  have hs : Nat.card candidate = 2 ^ (Nat.card M24).factorization 2 := by
    rw [candidate_card, m24_order]
    decide +kernel
  let T : Sylow 2 M24 := Sylow.ofCard candidate hs
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq M24 S T
  let e := MulAut.conj a
  let K := H.map e.toMonoidHom
  have hSK : candidate ≤ K := by
    have he : (S : Subgroup M24).map e.toMonoidHom = candidate := by
      have h := congrArg Sylow.toSubgroup ha
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
      have hh : (MulDistribMulAction.toMonoidEnd (MulAut M24) M24) (MulAut.conj a) =
          e.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        exact MulAut.smul_def (MulAut.conj a) x
      rw [hh] at h
      exact h
    exact he ▸ Subgroup.map_mono hS
  have hcard : Nat.card K = Nat.card H := Subgroup.card_map_of_injective e.injective
  rcases hcase with h | ⟨h, g, hg⟩ | ⟨h, g, hg⟩
  · exact marked_no_seven K hSK (hcard.trans h)
  · exact marked_no_fifteen K hSK (hcard.trans h) ((e.subgroupMap H) g)
      (((e.subgroupMap H).orderOf_eq g).trans hg)
  · exact marked_no_twentyone K hSK (hcard.trans h) ((e.subgroupMap H) g)
      (((e.subgroupMap H).orderOf_eq g).trans hg)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
