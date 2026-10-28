module

public import Theory.Quasithin.CentralThreeLocalRank
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Involution-centralizer witnesses for odd exceptional covers

This is the local-rank assembly needed in the odd-central-cover branch of
Aschbacher--Smith A.2.17 (printed p. 39).  The ordinary-rank conclusion of
I.2.1 does not identify a two-local subgroup.  Here the required local object
is an involution `z`: an elementary nine whose image is injective modulo the
ambient three-center and which centralizes `z` normalizes `⟨z⟩`, and the
central three-element supplied by the center raises the rank to three.

The displayed lift and its quotient injectivity are explicit hypotheses;
none of the results below constructs them from the name of a covering group.
In particular this is not a uniform existence theorem for the exceptional
three-covers.  For 3.G₂(3), GLS III, printed p. 319, equation (6.3.1), says
that lifts of orthogonal root groups have nontrivial central commutator.
Thus the ordinary orthogonal-root E₉ downstairs does not give this lift.
Korchagina--Lyons, *A {2,3}-local shadow of O'Nan's simple group*, Pacific
J. Math. 235 (2008), Table 1 and Lemma 2.3, pp. 270--271, gives
involution-centralizer three-rank two for 3.G₂(3).

The printed A.2.17 invocation of I.2.1 therefore needs a source audit before
using these conditional lemmas.  Full Case II in A.2.13 includes failure of
Theorem A, in addition to the central-kernel hypotheses.  A counterexample
to the proposed uniform local-witness interface does not refute that full
minimal-counterexample argument.  I.2.1 itself asserts only ordinary rank.

Source: Aschbacher--Smith, A.2.17, printed p. 39, together with the
involution-centralizer local-rank convention of A.2.7, printed p. 34.
-/

public section

namespace CFSG.Quasithin.ChapterI

private theorem e9_cube (a : Multiplicative (ZMod 3 × ZMod 3)) : a ^ 3 = 1 := by
  change (3 • a.toAdd) = 0
  apply Prod.ext
  · change 3 • a.toAdd.1 = (0 : ZMod 3)
    simp only [nsmul_eq_mul]
    exact zero_mul _
  · change 3 • a.toAdd.2 = (0 : ZMod 3)
    simp only [nsmul_eq_mul]
    exact zero_mul _

private theorem e9_card : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 3 ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  norm_num [Nat.card_zmod]

private theorem zpowers_two_isPGroup {G : Type*} [Group G] [Finite G]
    {z : G} (hz : orderOf z = 2) : IsPGroup 2 (Subgroup.zpowers z) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, hz]
  norm_num

private theorem zpowers_two_ne_bot {G : Type*} [Group G] [Finite G]
    {z : G} (hz : orderOf z = 2) : Subgroup.zpowers z ≠ ⊥ := by
  intro h
  have hz1 : z = 1 := by
    have hzmem : z ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers z
    simpa using hzmem
  simp [hz1] at hz

/- The centralizer version is the useful interface for the exceptional cover
calculations.  The local two-subgroup is forced to be the cyclic subgroup of
the marked involution, so its existence is discharged in this theorem. -/
theorem oddCover_three_le_involutionCentralizer_of_e9_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (hZne : Subgroup.center G ≠ ⊥)
    {z : G} (hz : orderOf z = 2)
    (f : Multiplicative (ZMod 3 × ZMod 3) →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hc : ∀ a, f a ∈ Subgroup.centralizer ({z} : Set G)) :
    3 ≤ primeRank 3 (Subgroup.centralizer ({z} : Set G)) ∧
      3 ≤ twoLocalPrimeRank 3 G := by
  let Q : Subgroup G := Subgroup.zpowers z
  have hQ : IsPGroup 2 Q := zpowers_two_isPGroup hz
  have hQne : Q ≠ ⊥ := zpowers_two_ne_bot hz
  have hn : ∀ a, f a ∈ Subgroup.normalizer (Q : Set G) := by
    intro a
    rw [show Q = Subgroup.zpowers z from rfl,
      Subgroup.normalizer_zpowers_eq_centralizer_of_order_two z hz]
    exact hc a
  have hlocal := Theory.Quasithin.three_le_twoLocalPrimeRank_of_injective_central_projection
    hZ hZne Q hQ hQne f hf hn e9_cube e9_card
  have hnormal := Theory.Quasithin.three_le_primeRank_normalizer_of_injective_central_projection
    hZ hZne Q f hf hn e9_cube e9_card
  rw [show Q = Subgroup.zpowers z from rfl,
    Subgroup.normalizer_zpowers_eq_centralizer_of_order_two z hz] at hnormal
  exact ⟨hnormal, hlocal⟩

/-- Square-one form of the involution witness contract. -/
theorem oddCover_three_le_involutionCentralizer_of_e9_square_one
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (hZne : Subgroup.center G ≠ ⊥)
    {z : G} (hzsq : z ^ 2 = 1) (hzne : z ≠ 1)
    (f : Multiplicative (ZMod 3 × ZMod 3) →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hc : ∀ a, f a ∈ Subgroup.centralizer ({z} : Set G)) :
    3 ≤ primeRank 3 (Subgroup.centralizer ({z} : Set G)) ∧
      3 ≤ twoLocalPrimeRank 3 G := by
  apply oddCover_three_le_involutionCentralizer_of_e9_lift hZ hZne
    (orderOf_eq_prime hzsq hzne) f hf hc

/- This is the direct A.2.17 consumer once a concrete exceptional cover has
 supplied the lift.  Keeping it here makes the local obstruction explicit and
 prevents downstream users from accidentally appealing only to ordinary rank. -/
theorem oddCover_not_quasithin_of_e9_involution_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (hZne : Subgroup.center G ≠ ⊥)
    {z : G} (hz : orderOf z = 2)
    (f : Multiplicative (ZMod 3 × ZMod 3) →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hc : ∀ a, f a ∈ Subgroup.centralizer ({z} : Set G)) :
    ¬ IsQuasithin G := by
  intro hqt
  have hle := isQuasithin_iff_twoLocalPrimeRank.mp hqt 3 (by decide) (by decide)
  have hge := (oddCover_three_le_involutionCentralizer_of_e9_lift
    hZ hZne hz f hf hc).2
  omega

end CFSG.Quasithin.ChapterI
