module

public import Theory.GroupTheory.PerfectCentralCoverPrimeDichotomy
public import Theory.SpecificGroups.SU3.PrimeCentralKernel

/-!
# Assembling the unitary central-cover alternatives from an actual lift

GLS4 Chapter 2 Lemma 16.3(a) retains both PSU₃ and SU₃. Its covering-group
input is Chapter 4 Lemma 2.8(a), using GLS3 Theorem 6.1.4. Here we prove the
assembly once a homomorphism from the literal SU₃ model to the given group
has been constructed over the specified projective quotient equivalence.
Perfectness makes this lift surjective, and the proved scalar-kernel bound
leaves exactly the projective and special alternatives. The latter has
center of order three and odd exponent if its center is nontrivial.

The special model is the actual subgroup `J.specialSubgroup` of GL₃.
The results work for arbitrary nondegenerate forms, including the required
antidiagonal form, and preserve the coefficient field of order `(2^n)^2`.

The lift is an explicit unproved premise of these conditional assembly
lemmas. Constructing it from the source hypotheses still requires the
PSU₃ universal-cover result. Neither lemma claims the unconditional source
theorem, and no universality or multiplier bound is encoded in a record.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup BenderSuzuki.MatrixGroups

/-- An actual compatible SU₃ lift gives the two source model alternatives.
The lift's surjectivity follows from perfectness of the given group. -/
public theorem unitary_centralCover_alternative_of_lift
    {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    (J : HermitianForm 3 E) (hperfect : commutator G = ⊤)
    (e : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (h : J.specialSubgroup →* G)
    (hh : (e.toMonoidHom.comp (QuotientGroup.mk' (center G))).comp h =
      J.specialToProjective) :
    Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (G ≃* J.specialSubgroup) := by
  let : Group.IsPerfect G := ⟨hperfect⟩
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hg : g.ker ≤ center G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    simpa only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, map_one] using
      (MonoidHom.mem_ker.mp hx)
  exact PerfectCentralCovering.nonempty_mulEquiv_or_of_prime_kernel_lift
    J.specialToProjective J.specialToProjective_surjective g hg h hh
    (by decide : Nat.Prime 3) J.card_specialToProjective_ker_dvd_three

/-- Under the same explicit lift, distinguish the centerless projective
alternative from the center-three special alternative. -/
public theorem unitary_centralCover_cases_of_lift
    {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hperfect : commutator G = ⊤)
    (e : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (h : J.specialSubgroup →* G)
    (hh : (e.toMonoidHom.comp (QuotientGroup.mk' (center G))).comp h =
      J.specialToProjective) :
    (center G = ⊥ ∧ Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) ∨
      (Nat.card (center G) = 3 ∧ Odd n ∧ Nonempty (G ≃* J.specialSubgroup)) := by
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hcard hconj
  rcases unitary_centralCover_alternative_of_lift J hperfect e h hh with ha | ha
  · obtain ⟨a⟩ := ha
    left
    refine ⟨(eq_bot_iff_card _).mpr ?_, ⟨a⟩⟩
    rw [Nat.card_congr (centerCongr a).toEquiv, hZ, card_bot]
  · obtain ⟨a⟩ := ha
    rcases J.special_center_eq_bot_or_card_three_odd hn hcard hfixed with hb | ⟨hc, ho⟩
    · left
      refine ⟨(eq_bot_iff_card _).mpr ?_,
        ⟨a.trans (J.specialProjectiveEquivOfCenterEqBot hb)⟩⟩
      rw [Nat.card_congr (centerCongr a).toEquiv, hb, card_bot]
    · exact Or.inr ⟨(Nat.card_congr (centerCongr a).toEquiv).trans hc, ho, ⟨a⟩⟩

end BenderSuzuki.ZD.RankOneModelGeometry
