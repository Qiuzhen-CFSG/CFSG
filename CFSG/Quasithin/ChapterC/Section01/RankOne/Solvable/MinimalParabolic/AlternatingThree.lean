module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The intrinsic alternating-three block in a solvable minimal parabolic

A two-perfect group with elementary four-group two-core and cubic quotient
has the original natural A₃ block structure. The central core image above
U(L) is killed by the coprime central-kernel theorem, so U(L)=O₂(L).
An intermediate normal subgroup of order two would make the quotient core
central, contradicting this equality. This gives irreducibility and the
self-centralizing core, hence all the short-group clauses.

The four-element module is identified with the binary natural module on
three letters. Its proved faithful S₃ action exhausts its six automorphisms;
the original cubic quotient has the alternating image. This constructs the
literal quotient and module isomorphisms with conjugation intertwining,
without a whole-group A₄ identification or a chosen Hall complement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13 and
the solvable minimal-parabolic step of C.1.29, printed pp.123–125, 132–134.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
universe u

private theorem core_eq_blockU {L : Type u} [Group L] [Finite L]
    (hp : IsPPerfect 2 L) (hq : Nat.card (L ⧸ pCore 2 L) = 3) :
    pCore 2 L = blockU L := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hq
  let f := QuotientGroup.lift (blockU L) (QuotientGroup.mk' (pCore 2 L))
    (by simpa only [QuotientGroup.ker_mk'] using (blockU_le_core (L := L)))
  have hk : f.ker = (pCore 2 L).map (QuotientGroup.mk' (blockU L)) := by
    dsimp only [f]
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  have hpQ := hp.of_surjective (QuotientGroup.mk' (blockU L))
    (QuotientGroup.mk'_surjective (blockU L))
  have hpf : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.map _
  have hinj := MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image hpQ f
    (by rw [hk]; exact blockU_core_image_le_center) hpf
    (fun x y => (mul_comm (f x) (f y))) (show Nat.Coprime 2 3 by decide)
    (fun x => by rw [← hq]; exact pow_card_eq_one')
  have hb : (pCore 2 L).map (QuotientGroup.mk' (blockU L)) = ⊥ :=
    hk ▸ (MonoidHom.ker_eq_bot_iff f).mpr hinj
  exact le_antisymm (by simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb)
    blockU_le_core

private theorem normal_core_dichotomy {L : Type u} [Group L] [Finite L]
    (hU : pCore 2 L = blockU L) (hc : Nat.card (pCore 2 L) = 4)
    (N : Subgroup L) [N.Normal] (hN : N ≤ pCore 2 L) :
    N = ⊥ ∨ N = pCore 2 L := by
  have hd : Nat.card N ∣ 2 ^ 2 := by simpa [hc] using card_dvd_of_le hN
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using he))
  · right
    have hNcard : Nat.card N = 2 := by simpa using he
    let q := QuotientGroup.mk' N
    let f := q.subgroupMap (pCore 2 L)
    have hk : f.ker = N.subgroupOf (pCore 2 L) := by
      ext x
      rw [MonoidHom.mem_ker, Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff (N := N) (x : L)
    have himage : Nat.card ((pCore 2 L).map q) = 2 := by
      have hh := f.ker.index_mul_card
      rw [index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
          (q.subgroupMap_surjective (pCore 2 L))).toEquiv,
        hk, Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv, hNcard, hc] at hh
      omega
    have hcentral := central_of_normal_card_two ((pCore 2 L).map q) himage
    have hmap : (blockU L).map q = ⊥ := by
      rw [blockU, map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
        commutator_top_right_eq_bot_iff_le_center]
      exact hcentral
    have hUN : blockU L ≤ N := by
      simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hmap
    exact le_antisymm hN (by rwa [hU])
  · exact Or.inr (eq_of_le_of_card_ge hN (by simpa [hc] using he.ge))

private theorem core_structure {L : Type u} [Group L] [Finite L]
    (hp : IsPPerfect 2 L) (he : IsElementaryAbelian 2 (pCore 2 L))
    (hc : Nat.card (pCore 2 L) = 4) (hq : Nat.card (L ⧸ pCore 2 L) = 3) :
    IsShort L ∧ blockFixed L = ⊥ ∧ Nat.card (blockU L) = 4 := by
  let := he
  have hU := core_eq_blockU hp hq
  have hne : pCore 2 L ≠ ⊥ := by intro hb; rw [hb, card_bot] at hc; omega
  have hncentral : ¬ pCore 2 L ≤ center L := by
    intro hh
    have hb := commutator_top_right_eq_bot_iff_le_center.mpr hh
    change blockU L = ⊥ at hb
    exact hne (hU.trans hb)
  have hQcent : pCore 2 L ≤ centralizer (pCore 2 L : Set L) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : pCore 2 L) ⟨x, hx⟩)
  have hself : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let : IsSimpleGroup (L ⧸ pCore 2 L) := isSimpleGroup_of_prime_card hq
    let C := centralizer (pCore 2 L : Set L)
    let q := QuotientGroup.mk' (pCore 2 L)
    have hn : (C.map q).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with hb | ht
    · simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
    · have hs := congrArg (Subgroup.comap q) ht
      have htop : C = ⊤ := by
        simp only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] at hs
        exact (sup_eq_left.mpr (show pCore 2 L ≤ C from hQcent)).symm.trans hs
      exact (hncentral (centralizer_eq_top_iff_subset.mp htop)).elim
  have hfixed : pCore 2 L ⊓ center L = ⊥ := by
    rcases normal_core_dichotomy hU hc (pCore 2 L ⊓ center L) inf_le_left with hb | ht
    · exact hb
    · exact (hncentral (ht ▸ inf_le_right)).elim
  have hUf : blockU L ⊓ center L = ⊥ := by rw [← hU, hfixed]
  have hshort : IsShort L := {
    finite := inferInstance
    twoPerfect := hp
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2 hself
    elementary := by rwa [← hU]
    central := by rwa [← hU]
    quotient := Or.inr hq
    irreducible := by
      refine ⟨?_, ?_⟩
      · rw [hUf, bot_lt_iff_ne_bot, ← hU]
        exact hne
      · intro N hN _ hNU
        let := hN
        rw [hUf, ← hU]
        apply normal_core_dichotomy hU hc N
        rwa [hU] }
  refine ⟨hshort, ?_, hU ▸ hc⟩
  apply Subgroup.map_injective (blockU L).subtype_injective
  rw [blockFixed_map, hUf, Subgroup.map_bot]

private theorem kleinFour_of_elementary_card_four
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hc : Nat.card A = 4) : IsKleinFour A := by
  let : Nontrivial A := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let := hs
    have h1 := Nat.card_of_subsingleton (1 : A)
    omega
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

private abbrev Natural := Multiplicative (BinaryPermutation.natural (Fin 3))

private instance naturalElementary : IsElementaryAbelian 2 Natural :=
  Representation.BinaryGroupAction.elementary

private theorem naturalCard : Nat.card Natural = 4 := by
  change Nat.card (BinaryPermutation.natural (Fin 3)) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    BinaryPermutation.finrank_natural_odd (Fin 3) (by decide)]
  norm_num

private instance naturalKleinFour : IsKleinFour Natural :=
  kleinFour_of_elementary_card_four naturalCard

private noncomputable def naturalActionEquiv : Equiv.Perm (Fin 3) ≃* MulAut Natural :=
  MulEquiv.ofBijective (BinaryPermutation.naturalMulAction (Fin 3))
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨BinaryPermutation.naturalMulAction_injective_of_odd (Fin 3) (by decide), by
        rw [IsKleinFour.card_mulAut]
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]⟩)

private theorem alternatingThree_of_short_four
    {L : Type u} [Group L] (h : IsShort L)
    (hc : Nat.card (L ⧸ pCore 2 L) = 3)
    (hU : Nat.card (blockU L) = 4) (hfix : blockFixed L = ⊥) :
    IsAlternatingBlock L 3 := by
  classical
  let := h.finite
  let : IsElementaryAbelian 2 (BlockModule L) := h.module_elementary
  have hcard : Nat.card (BlockModule L) = 4 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfix).toEquiv,
      Nat.card_congr (QuotientGroup.quotientBot (G := blockU L)).toEquiv]
    exact hU
  let : IsKleinFour (BlockModule L) := kleinFour_of_elementary_card_four hcard
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := BlockModule L) (G₂ := Natural)
  obtain ⟨rho, hrho⟩ := h.exists_quotient_moduleAction
  have hne : rho ≠ 1 := by
    intro heq
    have hu : blockU L ≤ center L := by
      intro u hu
      apply mem_center_iff.mpr
      intro l
      have hf := hrho l ⟨u, hu⟩
      rw [heq] at hf
      have hinj : Function.Injective (QuotientGroup.mk' (blockFixed L)) := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        simpa only [QuotientGroup.ker_mk'] using hfix
      have heq := congrArg Subtype.val (hinj hf)
      change u = l * u * l⁻¹ at heq
      exact mul_inv_eq_iff_eq_mul.mp heq.symm
    exact (ne_of_lt h.irreducible.1) (inf_eq_left.mpr hu)
  have hrhoinj : Function.Injective rho := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    have hd := rho.ker.card_subgroup_dvd_card
    rw [hc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · have htop : rho.ker = ⊤ := eq_of_le_of_card_ge le_top (by
        simpa only [Nat.card_congr topEquiv.toEquiv, hc] using h3.ge)
      exact (hne (MonoidHom.ext fun x => MonoidHom.mem_ker.mp (htop ▸ mem_top x))).elim
  let phi : (L ⧸ pCore 2 L) →* Equiv.Perm (Fin 3) :=
    naturalActionEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp rho)
  have hphi : Function.Injective phi :=
    naturalActionEquiv.symm.injective.comp ((MulAut.congr e).injective.comp hrhoinj)
  have hphicard : Nat.card phi.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hphi).toEquiv).symm.trans hc
  have hi : phi.range.index = 2 := by
    have hm := phi.range.index_mul_card
    rw [hphicard] at hm
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hm
    omega
  have heq : phi.range = alternatingGroup (Fin 3) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  let eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 3) :=
    (MonoidHom.ofInjective hphi).trans (MulEquiv.subgroupCongr heq)
  let action := (BinaryPermutation.naturalMulAction (Fin 3)).comp
    (alternatingGroup (Fin 3)).subtype
  refine ⟨by decide, h, action, ⟨⟨eQ, e, ?_⟩⟩, ?_⟩
  · intro l u
    have hact (a : L ⧸ pCore 2 L) (v : BlockModule L) :
        e (rho a v) = BinaryPermutation.naturalMulAction (Fin 3) (phi a) (e v) := by
      change e (rho a v) = naturalActionEquiv
        (naturalActionEquiv.symm ((MulAut.congr e) (rho a))) (e v)
      rw [naturalActionEquiv.apply_symm_apply]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]
    rw [← hrho l u]
    exact hact _ _
  · intro a v
    rfl

/-- The actual elementary four-core and cubic quotient give the full
intrinsic A₃ block, including its original conjugation module. -/
public theorem alternatingThree_of_elementary_four_core
    {L : Type u} [Group L] [Finite L]
    (hp : IsPPerfect 2 L) (he : IsElementaryAbelian 2 (pCore 2 L))
    (hc : Nat.card (pCore 2 L) = 4) (hq : Nat.card (L ⧸ pCore 2 L) = 3) :
    IsAlternatingBlock L 3 := by
  obtain ⟨hs, hfixed, hU⟩ := core_structure hp he hc hq
  exact alternatingThree_of_short_four hs hq hU hfixed

/-- Application to the chosen intrinsic minimal-parabolic factor K:
its subnormality and the four numerical/core premises produce the same block. -/
public theorem block_of_subnormal_elementary_four_core
    {H : Type u} [Group H] [Finite H] (K : Subgroup H) (hK : K.IsSubnormal)
    (hp : IsPPerfect 2 K) (he : IsElementaryAbelian 2 (pCore 2 K))
    (hc : Nat.card (pCore 2 K) = 4) (hq : Nat.card (K ⧸ pCore 2 K) = 3) :
    IsBlock K ∧ IsAlternatingBlock K 3 := by
  have ha := alternatingThree_of_elementary_four_core hp he hc hq
  exact ⟨⟨inferInstance, ha.2.1, hK⟩, ha⟩

end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
