module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms
public import BenderSuzuki.SE.PermutationQuotient
public import BenderSuzuki.SE.Borel
public import Theory.GroupAction.CharacteristicOddFixed
public import Theory.GroupAction.NormalizerFixedCentralizer

/-!
# Odd-core transport for the local Bender automorphism argument

Fixed points map onto fixed points under an odd characteristic quotient.
The kernel of that restricted map is odd, so Schur--Zassenhaus transfers
the absence of elementary fours to the quotient fixed subgroup. Separately,
a subgroup of a Borel inherits a normal Sylow two-subgroup. The actual
Bender automorphism theorem then forces any involutory automorphism with
fixed subgroup contained in that Borel to be inner.

Source: GLS, Volume 4, Chapter 2, the last paragraph of Proposition 4.4,
and Chapter 4, Lemma 3.4(c,e). No odd kernel is discarded.
-/

namespace BenderSuzuki.ZD
open PFAppendixIII PFchapter1section1

/-- Odd characteristic quotients preserve the absence of a four-group in the fixed subgroup. -/
public theorem not_twoRank_fixed_odd_quotient
    {G : Type*} [Group G] [Finite G]
    (O : Subgroup G) [O.Characteristic] (hodd : Odd (Nat.card O))
    (a : MulAut G) (ha : a ^ 2 = 1)
    (hr : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    ¬ TwoRankAtLeastTwo (O.quotientAut a).fixedSubgroup := by
  let q := QuotientGroup.mk' O
  let F := (O.quotientAut a).fixedSubgroup
  have hm := MulAut.map_fixedSubgroup_characteristic_odd O hodd a ha
  let f : a.fixedSubgroup →* F := (q.comp a.fixedSubgroup.subtype).codRestrict F
    (fun x => by
      change q (x : G) ∈ (O.quotientAut a).fixedSubgroup
      rw [← hm]; exact ⟨x, x.property, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : G ⧸ O) ∈ a.fixedSubgroup.map q := hm.symm ▸ y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let k : f.ker →* O :=
    ((a.fixedSubgroup.subtype.comp f.ker.subtype).codRestrict O (fun x => by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property))
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : O => (z : G)) hxy))
  have hko : Odd (Nat.card f.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_injective k hk)
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  intro hfour
  exact not_twoRankAtLeastTwo_quotient_of_odd f.ker hko hr
    (hfour.map_of_injective e.symm.toMonoidHom e.symm.injective)

/-- Every subgroup of a group with a normal Sylow has a normal Sylow. -/
private theorem normalSylow_of_injective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : H →* G) (hf : Function.Injective f)
    (hG : ∃ P : Sylow 2 G, (P : Subgroup G).Normal) :
    ∃ Q : Sylow 2 H, (Q : Subgroup H).Normal := by
  obtain ⟨P, hP⟩ := hG
  let : (P : Subgroup G).Normal := hP
  let : Unique (Sylow 2 G) := Sylow.unique_of_normal P hP
  let Q : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := Q.exists_comap_eq_of_injective hf
  have hRP : R = P := Subsingleton.elim _ _
  refine ⟨Q, ?_⟩
  rw [← hR, hRP]
  exact Subgroup.Normal.comap inferInstance f

/-- Fixed points lying in a Borel force an involutory Bender automorphism to be inner. -/
public theorem bender_inner_of_fixedSubgroup_le_borel
    {B : Type*} [Group B] [Finite B]
    (hB : IsSimpleBenderGroup B) {N : Subgroup B} (hN : IsBorelSubgroup N)
    (a : MulAut B) (ha : a ^ 2 = 1) (hfix : a.fixedSubgroup ≤ N) :
    ∃ b : B, a = MulAut.conj b := by
  obtain ⟨P, hP, _⟩ := simpleBender_borel_normalSylow_regular hN hB
  exact bender_inner_of_fixedSubgroup_normalSylow hB a ha
    (normalSylow_of_injective (Subgroup.inclusion hfix)
      (Subgroup.inclusion_injective hfix) ⟨P, hP⟩)

end BenderSuzuki.ZD

namespace BenderSuzuki.ZD
open PFchapter1section1

/-- The actual conjugation action on the derived odd-core quotient is outer
when its ambient relative centralizer has no elementary four. -/
public theorem bender_quotient_normalizer_outer
    {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (n : Subgroup.normalizer (D : Set G)) (hn : n ^ 2 = 1)
    (hmodel : IsSimpleBenderGroup (D ⧸ pPrimeCore 2 D))
    (hrank : ¬ TwoRankAtLeastTwo ↥(D ⊓ Subgroup.centralizer ({(n : G)} : Set G))) :
    ¬ ∃ b : D ⧸ pPrimeCore 2 D,
      (pPrimeCore 2 D).quotientAut (D.normalizerMonoidHom n) = MulAut.conj b := by
  let a := D.normalizerMonoidHom n
  have ha : a ^ 2 = 1 := by rw [← map_pow, hn, map_one]
  let e := D.normalizerFixedEquivCentralizer n
  have hr : ¬ TwoRankAtLeastTwo a.fixedSubgroup := fun hh =>
    hrank (hh.map_of_injective e.toMonoidHom e.injective)
  have hq := not_twoRank_fixed_odd_quotient (pPrimeCore 2 D)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) a ha hr
  exact (bender_rank_one_fixed_models hmodel _ (by rw [← map_pow, ha, map_one]) hq).2.1

/-- Centralizer containment becomes fixed-point containment in the actual Borel
image, through the odd core; hence the quotient action is inner. -/
public theorem bender_quotient_normalizer_inner
    {G : Type*} [Group G] [Finite G] (D M : Subgroup G)
    (n : Subgroup.normalizer (D : Set G)) (hn : n ^ 2 = 1)
    (hmodel : IsSimpleBenderGroup (D ⧸ pPrimeCore 2 D))
    (hB : IsBorelSubgroup ((M.comap D.subtype).map (QuotientGroup.mk' (pPrimeCore 2 D))))
    (hcent : D ⊓ Subgroup.centralizer ({(n : G)} : Set G) ≤ M) :
    ∃ b : D ⧸ pPrimeCore 2 D,
      (pPrimeCore 2 D).quotientAut (D.normalizerMonoidHom n) = MulAut.conj b := by
  let a := D.normalizerMonoidHom n
  have ha : a ^ 2 = 1 := by rw [← map_pow, hn, map_one]
  have hfix : a.fixedSubgroup ≤ M.comap D.subtype := by
    intro x hx
    exact hcent (D.normalizerFixedEquivCentralizer n ⟨x, hx⟩).property
  apply bender_inner_of_fixedSubgroup_le_borel hmodel hB _
    (by rw [← map_pow, ha, map_one])
  rw [← MulAut.map_fixedSubgroup_characteristic_odd (pPrimeCore 2 D)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) a ha]
  exact Subgroup.map_mono hfix

end BenderSuzuki.ZD
