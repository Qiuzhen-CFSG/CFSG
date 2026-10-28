module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.Sylow

/-!
# Central cosets and marked order-four lifts

Conjugation identifies the quotient by the center with the inner automorphisms.
For a perfect subgroup J, centralizing its inner action is equivalent to
centralizing J itself: the two homomorphisms from J agree modulo a central
kernel and hence agree. This makes the lift supplied by I.2.2 centralize J.
In a double cover, representatives of a central coset have the same square,
so the existential lifting clause controls every representative.

`NonTwoCentralInvolutionLifting` specifies only the lifting clauses of I.2.2(5b)
and (7b), with their non-2-central mark retained. These lemmas do not establish
the mark, the existence of an inner actor, or the covering theorem itself.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(5b),(7b), printed pp.409–410 / PDF pp.420–421, and the final paragraph
of 16.3.6, printed p.1179 / PDF p.1196.
-/

@[expose] public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup Theory.GroupTheory
variable {H A : Type*} [Group H] [Group A]

def TwoCentral (u : H) : Prop :=
  ∃ S : Sylow 2 H, ∃ hu : u ∈ S, (⟨u, hu⟩ : S) ∈ center S

def NonTwoCentralInvolutionLifting (H : Type*) [Group H] : Prop :=
  ∀ u : H ⧸ center H, orderOf u = 2 → ¬ TwoCentral u →
    ∃ f : H, QuotientGroup.mk' (center H) f = u ∧ orderOf f = 4

theorem conj_kernel : (MulAut.conj : H →* MulAut H).ker = center H := by
  ext x
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h y
    have he := DFunLike.congr_fun h y
    change x * y * x⁻¹ = y at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  · intro h
    ext y
    change x * y * x⁻¹ = y
    rw [← h y]
    group

/-- Inner conjugation is faithful on the actual quotient by the center. -/
noncomputable def quotientConj : (H ⧸ center H) →* MulAut H :=
  QuotientGroup.lift (center H) MulAut.conj (by rw [conj_kernel])

theorem quotientConj_mk (f : H) :
    quotientConj (QuotientGroup.mk' (center H) f) = MulAut.conj f := rfl

theorem quotientConj_injective : Function.Injective (quotientConj (H := H)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (eq_bot_iff_forall _).mpr
  intro u hu
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (center H) u
  apply (QuotientGroup.eq_one_iff f).mpr
  rw [← conj_kernel]
  exact hu

/-- An inner automorphism centralizes the inner action of a perfect subgroup
exactly when its representative centralizes that subgroup. -/
theorem conj_mem_centralizer_iff (J : Subgroup H) [Group.IsPerfect J] (f : H) :
    MulAut.conj f ∈ centralizer (J.map MulAut.conj : Set (MulAut H)) ↔
      f ∈ centralizer (J : Set H) := by
  constructor
  · intro hf
    have he : (MulAut.conj f).toMonoidHom.comp J.subtype = J.subtype := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
        (MulAut.conj : H →* MulAut H) (by rw [conj_kernel])
      apply MonoidHom.ext
      intro j
      have hj := mem_centralizer_iff.mp hf (MulAut.conj (j : H))
        (mem_map_of_mem MulAut.conj j.property)
      change MulAut.conj (f * (j : H) * f⁻¹) = MulAut.conj (j : H)
      rw [map_mul, map_mul, map_inv, ← hj]
      group
    intro j hj
    have heq := DFunLike.congr_fun he ⟨j, hj⟩
    change f * j * f⁻¹ = j at heq
    exact ((mul_inv_eq_iff_eq_mul).mp heq).symm
  · intro hf a ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hf j hj]

/-- Equality of cosets is sufficient to preserve the entire inner action. -/
theorem conj_eq_of_quotient_eq {f g : H}
    (h : QuotientGroup.mk' (center H) f = QuotientGroup.mk' (center H) g) :
    MulAut.conj f = MulAut.conj g := congrArg quotientConj h

/-- A marked non-2-central inner involution has an order-four representative
centralizing J. No inner representative or quotient mark is manufactured by
the lifting premise. -/
theorem lift_marked_inner (J : Subgroup H) [Group.IsPerfect J]
    (hlift : NonTwoCentralInvolutionLifting H) (a : MulAut H) (ha : orderOf a = 2)
    (haJ : a ∈ centralizer (J.map MulAut.conj : Set (MulAut H)))
    (u : H ⧸ center H) (hu : quotientConj u = a) (hmark : ¬ TwoCentral u) :
    ∃ f : H, f ∈ centralizer (J : Set H) ∧ orderOf f = 4 ∧
      f ^ 2 ∈ center H ∧ a = MulAut.conj f := by
  have hu2 : orderOf u = 2 :=
    (orderOf_injective quotientConj quotientConj_injective u).symm.trans (hu ▸ ha)
  obtain ⟨f, hf, hf4⟩ := hlift u hu2 hmark
  have hfa : MulAut.conj f = a := by
    rw [← quotientConj_mk, hf, hu]
  refine ⟨f, (conj_mem_centralizer_iff J f).mp (hfa.symm ▸ haJ), hf4, ?_, hfa.symm⟩
  apply (QuotientGroup.eq_one_iff (f ^ 2)).mp
  change QuotientGroup.mk' (center H) (f ^ 2) = 1
  rw [map_pow, hf, ← hu2, pow_orderOf_eq_one]

theorem square_eq_of_quotient_eq [Finite H] (hZ : Nat.card (center H) = 2)
    {f g : H} (h : QuotientGroup.mk' (center H) f = QuotientGroup.mk' (center H) g) :
    f ^ 2 = g ^ 2 := by
  have hd : f⁻¹ * g ∈ center H := QuotientGroup.eq.mp h
  have hd2 : (f⁻¹ * g) ^ 2 = 1 := by
    have hp : (⟨f⁻¹ * g, hd⟩ : center H) ^ Nat.card (center H) = 1 := pow_card_eq_one'
    rw [hZ] at hp
    exact congrArg Subtype.val hp
  have hc : Commute f (f⁻¹ * g) := mem_center_iff.mp hd f
  calc
    f ^ 2 = f ^ 2 * (f⁻¹ * g) ^ 2 := by rw [hd2, mul_one]
    _ = (f * (f⁻¹ * g)) ^ 2 := (hc.mul_pow 2).symm
    _ = g ^ 2 := by group

theorem order_four_of_marked_coset [Finite H] (hZ : Nat.card (center H) = 2)
    (hlift : NonTwoCentralInvolutionLifting H) (f : H)
    (hf2 : orderOf (QuotientGroup.mk' (center H) f) = 2)
    (hfmark : ¬ TwoCentral (QuotientGroup.mk' (center H) f)) : orderOf f = 4 := by
  obtain ⟨g, hg, hg4⟩ := hlift _ hf2 hfmark
  have hsq := square_eq_of_quotient_eq hZ hg
  have hfo : orderOf (f ^ 2) = 2 := by
    rw [← hsq, orderOf_pow, hg4]
    decide
  have hf4 : f ^ 4 = 1 := by
    have hp := pow_orderOf_eq_one (f ^ 2)
    rw [hfo, ← pow_mul] at hp
    exact hp
  have hd := orderOf_dvd_of_pow_eq_one hf4
  have hn : ¬ orderOf f ∣ 2 := by
    intro hh
    have hp := (orderOf_dvd_iff_pow_eq_one).mp hh
    rw [hp, orderOf_one] at hfo
    contradiction
  have hcases : orderOf f = 1 ∨ orderOf f = 2 ∨ orderOf f = 4 := by
    have hp := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf f ∣ 2 ^ 2 from hd)
    obtain ⟨k, hk, h⟩ := hp
    interval_cases k <;> simp_all
  rcases hcases with h | h | h
  · exact False.elim (hn (h ▸ one_dvd 2))
  · exact False.elim (hn (h ▸ dvd_rfl))
  · exact h

end Theory.GroupTheory.DoubleCoverCentralizer
