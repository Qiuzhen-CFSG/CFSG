module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Assembly
public import Theory.GroupTheory.CentralizerOddComplement

/-!
# J.2.10 from the Suzuki centralizer theorem

The corrected J.2.9 intersection makes S₀ Sylow in C_G(Y) and puts it
in the center of its normalizer there. Burnside transfer constructs a
normal odd complement. Two distinct nonidentity members of S₀ give
the three involution centralizers which generate that complement.
The already proved Suzuki torus calculation then gives every clause
of J.2.10 on the literal image of Y in G, with no complement premise.

The J.2.9 conclusion is an earlier-source input; its construction from
the remaining J.2.7 fusion clauses stays with the centralizer assembly.

Source: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- All clauses of J.2.10 from J.2.9, with the odd complement constructed by transfer. -/
theorem SuzukiSourceConclusion.oddPrime_source_conclusions
    [IsElementaryAbelian 2 c.S0] (r : c.SuzukiSourceConclusion)
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧ (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
      normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
      centralizer (YG : Set G) = YG ⊔ c.S0 ∧
      IsCyclic YG.normalizerMonoidHom.range ∧
      Nat.card YG.normalizerMonoidHom.range = p - 1 := by
  let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
  obtain ⟨_, _, hYG, hinter, _, _⟩ := r.oddPrime_local_consequences c hp Y
  have hoddY : Odd (Nat.card YG) := by
    rw [hYG]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨P, hodd, hnorm, hdecomp⟩ :=
    exists_odd_complement_of_centralizer_intersection YG c.S0
      (IsElementaryAbelian.isPGroup 2 c.S0) hoddY hinter
  have hEN : c.S0 ≤ normalizer (P : Set G) :=
    (show c.S0 ≤ centralizer (YG : Set G) by rw [hdecomp]; exact le_sup_right).trans hnorm
  have hEcard : Nat.card c.S0 = 4 := by
    have hc := r.cubic.card_E
    rw [r.cubic_E, Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv] at hc
    exact hc
  let : Nontrivial c.S0 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : c.S0)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := c.S0)
    (by simp only [ENat.card_eq_coe_natCard, hEcard]; decide) 1 a
  have hsquare (x : c.S0) : x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 c.S0) x
  have hab : a * b ≠ 1 := by
    intro he
    apply hba
    exact (eq_inv_of_mul_eq_one_right he).trans
      (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare a))
  let f : c.S0 →* normalizer (P : Set G) := inclusion hEN
  apply r.oddPrime_conclusions c hp Y P hodd (f a) (f b)
    (by rw [← map_pow, hsquare, map_one]) (by rw [← map_pow, hsquare, map_one])
    ((show Commute a b from mul_comm' a b).map f) hdecomp
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨a.property, fun h => ha (Subtype.ext h)⟩
  · exact ⟨b.property, fun h => hb (Subtype.ext h)⟩
  · exact ⟨c.S0.mul_mem a.property b.property, fun h => hab (Subtype.ext h)⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
