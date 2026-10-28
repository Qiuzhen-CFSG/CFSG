module

public import Theory.GroupTheory.Covering
public import Theory.SpecificGroups.ONan.LinearCoverKernel

/-!
# The O'Nan odd central-cover restriction: reduction to lifting

For a finite quasisimple group whose central quotient is the actual O'Nan
model, a compatible lift from the linear matrix construction forces its center
order to divide six. A nontrivial odd p-group of such order has p = 3 and order
three. Perfectness supplies surjectivity of the lift.

The remaining input is existence of this compatible lift. Thus the conditional
result below does not yet prove the unconditional cover restriction in A.2.19.
It avoids requiring global order or simplicity certification for `ONan.Model`.

Sources: Aschbacher--Smith, Lemma A.2.19, printed pp. 40--41, and Lemma I.2.1,
printed p. 409. The actual multiplier entry M(O'N) = C₃ is GLS3, Table 5.3s,
printed p. 280 (`refs/KGroup/GLS3/Chapter5(sec3-).tex`). O'Nan is absent from
I.1.4's displayed list, so that list alone cannot discharge the lifting input.
-/

namespace CFSG.Quasithin.ChapterA

/-- Conditional O'Nan odd-cover restriction: a compatible lift from the fixed
linear construction forces the nontrivial odd primary center to have order three.
The lift is a genuine additional premise, not yet a source theorem. -/
public theorem onan_odd_center_restriction_of_lift
    {G : Type*} [Group G] [Finite G] [Theory.GroupTheory.IsQuasisimple G]
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hP : IsPGroup p (Subgroup.center G)) [Nontrivial (Subgroup.center G)]
    (e : G ⧸ Subgroup.center G ≃* ONan.Model)
    (f : ONan.Cover.linearSubgroup →* G)
    (hfac : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp f =
      ONan.Cover.projection) :
    p = 3 ∧ Nat.card (Subgroup.center G) = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hd := ONan.Cover.center_card_dvd_six_of_lift e f
    (ONan.Cover.lift_surjective e f hfac) hfac
  have hlt : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
  have hpd : p ∣ Nat.card (Subgroup.center G) :=
    hP.card_eq_or_dvd.resolve_left (by omega)
  have hp3 : p = 3 := by
    have h6 : p ∣ 2 * 3 := hpd.trans hd
    rcases hp.dvd_mul.mp h6 with h2 | h3
    · exact (hpodd (((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h2).symm)).elim
    · exact ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp h3).symm
  subst p
  refine ⟨rfl, ?_⟩
  have hpow := (IsPGroup.iff_card.mp hP)
  obtain ⟨n, hn⟩ := hpow
  have hodd : Odd (Nat.card (Subgroup.center G)) := hn ▸ (by exact (by decide : Odd 3).pow)
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  rcases hodd with ⟨k, hk⟩
  omega

end CFSG.Quasithin.ChapterA
