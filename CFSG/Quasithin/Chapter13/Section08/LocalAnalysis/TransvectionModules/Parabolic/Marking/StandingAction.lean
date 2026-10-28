module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Standing
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Identify the original natural actor after quotient recognition

The standing action on V has a surjective actor of degree five or six,
with literal conjugation compatibility. Its coordinates do not assume
L/O₂(L) is A₆. Once that quotient is identified, simplicity makes the
induced actor map injective, and the orders of A₅ and A₆ select the degree.
The resulting equivalence agrees on representatives, so the earlier
natural-representation applicability is proved rather than added as a
new assumption of the parabolic marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Remark 13.5.3, p.916, and the application of 13.7.6(3) in 13.8.6, p.948.
The action below is the given action on V, distinct from U_H/V₁.
-/

public section
open Subgroup Module BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G]

/-- The original natural action from Remark 13.5.3. Its acting group is a
surjective image of L, with either of the source's alternating degrees.
No identification of L/O₂(L), centralizer kernel, or flag coordinates is
assumed. Compatibility is on actual conjugates of elements of V. -/
@[expose] def StandingNatural (L V : Subgroup G) (hLV : L ≤ normalizer (V : Set G)) : Prop :=
  ∃ n : ℕ, (n = 5 ∨ n = 6) ∧
    ∃ f : L →* alternatingGroup (Fin n), Function.Surjective f ∧
      ∃ E : V ≃* Multiplicative (natural (Fin n)),
        ∀ (l : L) (v : V),
          (E (V.normalizerMonoidHom ⟨l.val, hLV l.property⟩ v)).toAdd =
            alternatingNaturalRepresentation (Fin n) (f l) (E v).toAdd

private theorem alt_card {n : ℕ} (hn : n = 5 ∨ n = 6) :
    Nat.card (alternatingGroup (Fin n)) = if n = 5 then 60 else 360 := by
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

private theorem alt_not_two {n : ℕ} (hn : n = 5 ∨ n = 6) :
    ¬ IsPGroup 2 (alternatingGroup (Fin n)) := by
  intro hp
  obtain ⟨r, hr⟩ := hp.exists_card_dvd_pow
  have hd : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rw [alt_card hn]
    split <;> decide
  have hh := Nat.prime_three.dvd_of_dvd_pow (hd.trans hr)
  norm_num at hh

private theorem quotientEquiv_of_alt_action [Finite G] (L : Subgroup G)
    [IsSimpleGroup (L ⧸ pCore 2 L)] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (f : L →* alternatingGroup (Fin n)) (hf : Function.Surjective f) :
    ∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n),
      ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) = f l := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have hker : pCore 2 L ≤ f.ker := by
    have hn' : ((pCore 2 L).map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases hn'.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · have hp : IsPGroup 2 ((pCore 2 L).map f) := pCore_isPGroup.map f
      rw [h] at hp
      exact (alt_not_two hn (hp.of_equiv Subgroup.topEquiv)).elim
  let q := QuotientGroup.lift (pCore 2 L) f hker
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨l, rfl⟩ := hf a
    exact ⟨QuotientGroup.mk' (pCore 2 L) l, rfl⟩
  have hqi : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin n))
      obtain ⟨b, rfl⟩ := hq a
      exact (ha (h.ge (mem_top b))).elim
  exact ⟨MulEquiv.ofBijective q ⟨hqi, hq⟩, fun _ => rfl⟩

/-- Prove the ordinary representation implication from the actual standing
action. A simple ordinary quotient kills the remaining actor kernel and
forces the degree by the group orders. -/
theorem standing_natural_earlier [Finite G] {L V : Subgroup G}
    {hLV : L ≤ normalizer (V : Set G)} (h : StandingNatural L V hLV) :
    EarlierNatural L V hLV := by
  intro n hn hL
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  obtain ⟨eL⟩ := hL
  let : IsSimpleGroup (L ⧸ pCore 2 L) := eL.isSimpleGroup
  obtain ⟨m, hm, f, hf, E, hE⟩ := h
  obtain ⟨e, he⟩ := quotientEquiv_of_alt_action L hm f hf
  have hc := Nat.card_congr (e.symm.trans eL).toEquiv
  have hmn : m = n := by
    rw [alt_card hm, alt_card hn] at hc
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;> norm_num at *
  subst m
  refine ⟨e, E, ?_⟩
  intro l v
  rw [he]
  exact hE l v
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
