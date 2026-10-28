module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceThompson
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceOddElements
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.OddSubgroups

/-!
# Small-subspace centralizers in the Hermitian source

An odd prime in the induced action supplies a prime-order element by Cauchy's
theorem. Its fixed space contains the prescribed subspace, contradicting the
proved odd-element displacement bound whenever that subspace has corank below
4n. Thus the induced action is a two-group and its odd Cartan parameter is one.
Together with the proved higher Thompson bound, E.6.27 gives r >= 4n once the
full ambient odd-normalizer hypothesis is supplied.

Only that ambient hypothesis remains explicit in the last theorem. The actual
chosen-module applications, including n = 1, are in the Chapter 12 Centralizers
extension. Its proof and the complete source exclusion remain with
qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.3.37,
E.6.27--28, H.4.2 and 7.4.1, printed pp.239,257--258,382,699--700
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
variable {G : Type*} [Group G] [Finite G]
  (V X : Subgroup G) [IsElementaryAbelian 2 V]

private theorem corank_antitone {B C : Subgroup G} (hBC : B ≤ C) (hCV : C ≤ V) :
    subgroupCorank V C ≤ subgroupCorank V B := by
  have h := offender_corank_add hBC hCV
  omega

private theorem fixedCodim_le_corank_of_mem_induced
    (hXN : X ≤ normalizer (V : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hXU : X ≤ centralizer (U : Set G))
    {a : Automizer V} (ha : a ∈ inducedAutomizer V X) :
    fixedCodim (automizerRepresentation V) (zpowers a) ≤ subgroupCorank V U := by
  have hm := fixedCodim_mono (automizerRepresentation V) (zpowers_le.mpr ha)
  rw [fixedCodim_inducedAutomizer V X hXN] at hm
  exact hm.trans (corank_antitone V
    (le_inf hUV (le_centralizer_iff.mp hXU)) inf_le_left)

variable (n : ℕ) [NeZero n]
  (e : Additive V ≃ₗ[ZMod 2] Space n)
  (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction n (binaryNormalizer n) (j a) (e v))

include hj he in
/-- The actual action of a small-subspace centralizer is a two-group. -/
theorem localCentralizer_image_isTwo
    (hXN : X ≤ normalizer (V : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hXU : X ≤ centralizer (U : Set G))
    (hc : subgroupCorank V U < 4*n) :
    IsPGroup 2 (inducedAutomizer V X) := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p = 2 := by
    by_contra hp2
    let : Fact p.Prime := ⟨hpp⟩
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := inducedAutomizer V X) p hpd
    have ho : Odd (orderOf a.val) := by
      rw [Subgroup.orderOf_coe,ha]
      exact hpp.odd_of_ne_two hp2
    have hne : a.val ≠ 1 := by
      intro h
      have h1 : a = 1 := Subtype.ext h
      rw [h1,orderOf_one] at ha
      exact hpp.ne_one ha.symm
    have hb := odd_fixedCodim_ge_four_mul_of_equivariant n (automizerRepresentation V)
      j hj e he a.val ho hne
    have hu := fixedCodim_le_corank_of_mem_induced V X hXN hUV hXU a.property
    omega
  simpa only [hp2] using (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩ :
    2 ∈ Nat.primeFactors 2)

include hj he in
/-- The odd Cartan parameter of this literal local action is exactly one. -/
theorem localCentralizer_nPrime_eq_one
    (hXN : X ≤ normalizer (V : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hXU : X ≤ centralizer (U : Set G))
    (hc : subgroupCorank V U < 4*n) :
    nPrime (inducedAutomizer V X) = 1 := by
  have hp := localCentralizer_image_isTwo V X n e j hj he hXN hUV hXU hc
  apply le_antisymm ?_ one_le_nPrime
  apply nPrime_le_iff.mpr
  intro c w
  have ho : Odd (Nat.card w.cyclicGroup) :=
    w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  obtain ⟨k,hk⟩ := (hp.to_subgroup w.cyclicGroup).exists_card_eq
  rw [hk] at ho
  have hk0 : k = 0 := by
    by_contra h
    exact (by decide : ¬ Odd (2 : ℕ)) ((Nat.odd_pow_iff h).mp ho)
  have hw : 1 = 2^c-1 := by simpa only [hk,hk0,pow_zero] using w.card
  have hpow : c+1 ≤ 2^c := c.lt_two_pow_self
  omega

include hj he in
/-- The Hermitian 7.4.1 deduction with only ambient abelian odd-normalizer
control remaining. All local action estimates are proved from the coordinates. -/
theorem globalR_ge_four_mul_of_odd_control
    {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hr : 1 < globalR V)
    (hcontrol : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card B) → IsMulCommutative B → normalizer (B : Set G) ≤ M) :
    ((4*n : ℕ) : ℕ∞) ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hescape⟩
  by_contra hbad
  have hsmall : subgroupCorank V U < 4*n := by exact_mod_cast lt_of_not_ge hbad
  have hUne : U ≠ ⊥ := by
    intro hz
    have hdim : subgroupCorank V (⊥ : Subgroup G) = 9*n := by
      rw [subgroupCorank, relIndex_bot_left]
      have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      change Nat.card V = _ at hcard
      rw [Nat.card_zmod, e.finrank_eq, finrank_binary] at hcard
      rw [hcard, Nat.log_pow (by decide)]
    rw [hz,hdim] at hsmall
    omega
  have hn := localCentralizer_nPrime_eq_one V (M ⊓ centralizer (U : Set G)) n e j hj he
    (h.localCentralizer_le_normalizer hUne hUV) hUV inf_le_right hsmall
  have hJ := localCentralizer_thompson_one V n e j hj he h hUne hUV hsmall
  have hC := Chapter4.Section04.NormalizedRankOneOddControl.centralizer_le_of_abelian_odd_control
    h hUne hUV (j := 1) (by decide) hr
    hn.le hJ hcontrol
  exact hescape ((h.centralizer_le_iff hUne hUV).mp hC)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
