module
public import Theory.Quasithin.HighRankOddCoreAction.FixedSpaces
public import Theory.GroupTheory.PGroup.ClassTwoFixedFrattiniRank
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.OddKernelCenter
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.Representation.ElementaryTwoFixedRank

/-!
# Two-rank bounded by local odd-prime rank

For a normal p-subgroup Q of rank greater than two, choose a supercritical
subgroup X. The actual conjugation action on X/Φ(X) has odd kernel, so
every elementary abelian two-subgroup acts faithfully there. Coprime fixed
lifting and the class-two exponent-p rank theorem bound every involution
fixed space by dimension two. Sign-character geometry then gives order at
most eight; at order eight it supplies inversion, central in the entire
automorphism image and hence central modulo the actual odd core.

Source: Aschbacher–Smith, Lemma A.1.28, printed p.26.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.Quasithin
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Every actual elementary two-subgroup has order at most eight; at equality
it contains an involution central modulo the actual odd core. -/
public theorem elementary_two_bound_of_large_normal_p_subgroup
    (hp : Odd p)
    (hlocal : ∀ a : G, orderOf a = 2 → primeRank p (centralizer ({a} : Set G)) ≤ 2)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) (hQrank : 2 < primeRank p Q)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 8 ∧ (Nat.card A = 8 →
      ∃ a : A, orderOf (a : G) = 2 ∧
        QuotientGroup.mk' (pPrimeCore 2 G) a ∈ center (G ⧸ pPrimeCore 2 G)) := by
  classical
  have hp2 : p ≠ 2 := fun he => by subst p; exact (by decide : ¬ Odd 2) hp
  obtain ⟨X, hX⟩ := hQ.exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup p X) := ⟨hQ.to_subgroup X⟩
  let : IsElementaryAbelian p (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  let f : G →* MulAut (X ⧸ frattini X) :=
    ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp MulAut.conjNormal
  have hodd : Odd (Nat.card f.ker) :=
    odd_card_supercritical_frattini_kernel hp hlocal Q hQ hQrank X hX
  let fA : A →* MulAut (X ⧸ frattini X) := f.comp A.subtype
  have hfA : Function.Injective fA := injective_comp_subtype_of_coprime_ker f
    hodd.coprime_two_left A (IsElementaryAbelian.isPGroup 2 A)
  let : MulDistribMulAction A (X ⧸ frattini X) :=
    MulDistribMulAction.compHom (X ⧸ frattini X) fA
  let ρ : Representation (ZMod p) A (Additive (X ⧸ frattini X)) :=
    Representation.ofElementaryAbelianAction
  have hρ : Function.Injective ρ := by
    intro a b he
    apply hfA
    ext x
    exact congrArg (fun r : Module.End (ZMod p) (Additive (X ⧸ frattini X)) => r (Additive.ofMul x)) he
  have hpow (a : A) : (a : G)^2=1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a)
  have ho (a : A) (ha : a ≠ 1) : orderOf (a : G)=2 :=
    orderOf_eq_prime (hpow a) (fun he => ha (Subtype.ext he))
  have hfix (a : A) (ha : a ≠ 1) :
      Module.finrank (ZMod p) (Module.End.eigenspace (ρ a) 1) ≤ 2 := by
    let α : MulAut X := MulAut.characteristic X (MulAut.conjNormal (a : G))
    have hα : α ^ 2 = 1 := by
      change (((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut Q)) (a : G)) ^ 2 = 1
      rw [← map_pow, hpow, map_one]
    have hr : primeRank p α.fixedSubgroup ≤ 2 :=
      (primeRank_fixed_characteristic_conjugation_le p Q X (a : G)).trans (hlocal a (ho a ha))
    have hc := MulAut.card_fixed_frattini_le_prime_sq (hQ.to_subgroup X) hp2
      hX.pow_eq_one hX.derived_le_center α hα hr
    exact finrank_eigenspace_one_le_of_fixed_card fA a hc
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp he
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
  obtain ⟨hcard, hinv⟩ := Representation.ElementaryTwoFixedRank.card_le_eight_and_inverter
    ρ hρ htwo hfix
  refine ⟨hcard, ?_⟩
  intro hA
  obtain ⟨a, ha, hai⟩ := hinv hA
  refine ⟨a, ho a ha, Theory.GroupTheory.mem_center_oddCore_of_mem_center_image f hodd a ?_⟩
  apply Theory.GroupTheory.mem_center_mulAut_of_inverts
  intro x
  have hh := hai (Additive.ofMul x)
  exact hh

/-- A large normal odd-prime subgroup forces two-rank at most three, with
nontrivial odd-core quotient center at equality. -/
public theorem two_rank_le_three_and_center_oddCore_of_large_normal_p_subgroup
    (hp : Odd p)
    (hlocal : ∀ a : G, orderOf a = 2 → primeRank p (centralizer ({a} : Set G)) ≤ 2)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) (hQrank : 2 < primeRank p Q) :
    primeRank 2 G ≤ 3 ∧
      (primeRank 2 G = 3 → center (G ⧸ pPrimeCore 2 G) ≠ ⊥) := by
  have hE (A : Subgroup G) (hA : IsElementaryAbelian 2 A) := by
    let : IsElementaryAbelian 2 A := hA
    exact elementary_two_bound_of_large_normal_p_subgroup hp hlocal Q hQ hQrank A
  refine ⟨(primeRank_le_iff_elementary_card_le G).mpr (fun A hA => by
    simpa using (hE A hA).1), ?_⟩
  intro hthree
  obtain ⟨A, hA, hAc⟩ := exists_elementaryAbelian_card_primeRank (G := G) (p := 2)
  have hA8 : Nat.card A = 8 := by simpa [hthree] using hAc
  obtain ⟨a, hao, ha⟩ := (hE A hA).2 hA8
  intro hb
  rw [hb, mem_bot] at ha
  have hm := (QuotientGroup.eq_one_iff (a : G)).mp ha
  have hdvd : 2 ∣ Nat.card (pPrimeCore 2 G) :=
    hao ▸ (pPrimeCore 2 G).orderOf_dvd_natCard hm
  exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) hdvd
end Theory.Quasithin
