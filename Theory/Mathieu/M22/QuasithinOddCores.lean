module
public import Theory.Mathieu.M22.CoverTwoRank
public import Theory.Mathieu.M22.OddKernelDegree
public import Theory.Quasithin.HighRankOddCoreAction.DegreeBound

/-!
# Odd prime cores in quasithin groups containing full M₂₂ covers

A large normal odd prime core gives a supercritical Frattini representation
with odd kernel. A full M₂₂ cover supplies two-rank at least three, so the
actual representation has degree at most four. Its restriction to the cover
still has odd kernel and degree at least five away from characteristic
eleven. Thus only the eleven-core can have rank greater than two.

Source: Aschbacher--Smith A.1.28, printed p.26; H.12.1, p.394. The consumer
is the full cubic-centralizer comparison of 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22CentralCover

/-- Every odd prime core other than the eleven-core has rank at most two. -/
theorem odd_core_rank_le_two_of_ne_eleven
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (B : Subgroup G) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hp11 : p ≠ 11) :
    primeRank p (pCore p G) ≤ 2 := by
  by_contra! hlarge
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hp
  let Q := pCore p G
  have hQ : IsPGroup p Q := pCore_isPGroup
  obtain ⟨X,hX⟩ := hQ.exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup p X) := ⟨hQ.to_subgroup X⟩
  let : IsElementaryAbelian p (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  have hlocal (a : G) (ha : orderOf a = 2) :
      primeRank p (centralizer ({a} : Set G)) ≤ 2 :=
    ((isTwoLocal_involution_centralizer ha).primeRank_le p).trans
      ((isQuasithin_iff_twoLocalPrimeRank.mp hqt) p Fact.out hp)
  let f : PerfectCentralCovering.Cover B M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hthree : 3 ≤ primeRank 2 G := (three_le_twoRank f).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 B.subtype B.subtype_injective)
  have hdim := Theory.Quasithin.supercritical_frattini_finrank_le_four
    hp hlocal Q hQ hlarge hthree X hX
  let a : G →* MulAut (X ⧸ frattini X) :=
    ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp MulAut.conjNormal
  have hodd : Odd (Nat.card a.ker) :=
    Theory.Quasithin.odd_card_supercritical_frattini_kernel hp hlocal Q hQ hlarge X hX
  let aB := a.comp B.subtype
  let : MulDistribMulAction B (X ⧸ frattini X) :=
    MulDistribMulAction.compHom (X ⧸ frattini X) aB
  let ρ : Representation (ZMod p) B (Additive (X ⧸ frattini X)) :=
    Representation.ofElementaryAbelianAction
  have hker : ρ.asGroupHom.ker = aB.ker := by
    ext b
    rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
    constructor
    · intro hb
      have hv := congrArg Units.val hb
      ext v
      exact congrArg (fun r : Module.End (ZMod p) (Additive (X ⧸ frattini X)) =>
        r (Additive.ofMul v)) hv
    · intro hb
      apply Units.ext
      ext v
      exact congrArg (fun z : MulAut (X ⧸ frattini X) => z (Additive.toMul v)) hb
  have hρodd : Odd (Nat.card ρ.asGroupHom.ker) := by
    rw [hker]
    exact hodd.of_dvd_nat (card_comap_dvd_of_injective a.ker B.subtype B.subtype_injective)
  have h11 : (11 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 11 := (CharP.cast_eq_zero_iff (ZMod p) p 11).mp hz
    exact hp11 ((Nat.dvd_prime Nat.prime_eleven).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
  have hd := degree_ge_five_of_odd_kernel e ρ hρodd h11
  omega
/-- A large odd prime core is the eleven-core, and the ambient two-rank is
exactly three with nontrivial center modulo the original odd core. -/
theorem large_odd_core_forces_eleven
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (B : Subgroup G) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22)
    (hlarge : ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 < primeRank p (pCore p G)) :
    primeRank 2 G = 3 ∧ center (G ⧸ pPrimeCore 2 G) ≠ ⊥ ∧
      2 < primeRank 11 (pCore 11 G) := by
  obtain ⟨p,hp,ho,hr⟩ := hlarge
  let : Fact p.Prime := ⟨hp⟩
  have he : p = 11 := by
    by_contra hne
    exact (not_le_of_gt hr) (odd_core_rank_le_two_of_ne_eleven hqt B e ho hne)
  subst p
  have hlocal (a : G) (ha : orderOf a = 2) :
      primeRank 11 (centralizer ({a} : Set G)) ≤ 2 :=
    ((isTwoLocal_involution_centralizer ha).primeRank_le 11).trans
      ((isQuasithin_iff_twoLocalPrimeRank.mp hqt) 11 hp ho)
  have hbound := Theory.Quasithin.two_rank_le_three_and_center_oddCore_of_large_normal_p_subgroup
    ho hlocal (pCore 11 G) pCore_isPGroup hr
  let f : PerfectCentralCovering.Cover B M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hthree : 3 ≤ primeRank 2 G := (three_le_twoRank f).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 B.subtype B.subtype_injective)
  have heq : primeRank 2 G = 3 := Nat.le_antisymm hbound.1 hthree
  exact ⟨heq,hbound.2 heq,hr⟩
end Sporadic.Mathieu.M22CentralCover
