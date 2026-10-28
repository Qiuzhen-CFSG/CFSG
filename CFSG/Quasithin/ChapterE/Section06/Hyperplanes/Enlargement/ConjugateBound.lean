module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.CommutingFactorsOddRank

/-!
# At most two actual conjugates in the E.6 enlargements

This proves the `TwoConjugates` contract from the genuine E.6.1 and E.6.15
hypotheses, retaining exactly E.6.13 and E.6.21 as earlier inputs. It uses
the odd-rank restriction directly in place of the citation to 1.2.1(3).
That proposition concerns C-components; an A₃ block is not such a component.

E.6.21 passes through relative subnormality to each factor and makes its
center a two-group. Quasisimplicity, or two-perfection and the nonzero short
module, shows that the factor is not a two-group. Thus it has an element of
odd prime order. Three distinct commuting conjugates give three independent
cyclic subgroups of that order. E.6.17 ensures that the intersection of their
three hyperplane fixed spaces contains an involution. Its actual centralizer
then has odd prime rank at least three, contradicting quasithinness.

The component and block cases retain their separate definitions, including
the actual alternating block modules. No conjugate-count or factorization
hypothesis is added. The fixed-space contradiction remains in `FixedSpaces`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.22–23,
printed pp.254–255 (PDF pp.265–266); compare 1.2.1(3), printed p.504.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open ComponentBalance
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

private theorem factor_center_and_not_two (h21 : OddCoreFree V)
    {U L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hL : CentralizerComponent U L ∨ SmallBlock U L) :
    IsPGroup 2 (center L) ∧ ¬ IsPGroup 2 L := by
  have hLC : L ≤ centralizer (U : Set G) := hL.elim And.left And.left
  let e := subgroupOfEquivOfLe hLC
  have hs : (L.subgroupOf (centralizer (U : Set G))).IsSubnormal := by
    rcases hL with hL | hL
    · exact hL.2.1
    · exact hL.2.1.subnormal
  have ho := hs.pPrimeCore_eq_bot (h21 U hU.1 hU.2.1) _
  have hoL : pPrimeCore 2 L = ⊥ := by
    have he := pPrimeCore_map_iso 2 e
    simpa only [ho, Subgroup.map_bot] using he.symm
  refine ⟨isPGroup_of_nilpotent_normal (center L) inferInstance inferInstance hoL, ?_⟩
  intro hp
  rcases hL with hL | hL
  · let := hL.2.2
    let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
    let : Group.IsNilpotent L := hp.isNilpotent
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · have hshort : ChapterC.IsShort L := hL.2.2.elim (fun h => h.2.1) (fun h => h.2.1)
    have hb : (⊥ : Subgroup L) = ⊤ := hshort.twoPerfect ⊥ inferInstance
      (hp.of_equiv QuotientGroup.quotientBot.symm)
    exact hshort.blockU_ne_bot (le_bot_iff.mp (le_top.trans_eq hb.symm))

private theorem exists_odd_prime_element {L : Type*} [Group L] [Finite L]
    (hL : ¬ IsPGroup 2 L) : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ x : L, orderOf x = p := by
  have hn : ¬ (Nat.card L).primeFactors ⊆ (2 : ℕ).primeFactors := by
    rwa [← isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)]
  obtain ⟨p, hp, hp2⟩ := Finset.not_subset.mp hn
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpne : p ≠ 2 := by
    intro he
    subst p
    exact hp2 (Nat.mem_primeFactors.mpr ⟨by decide, dvd_rfl, by decide⟩)
  let : Fact p.Prime := ⟨hpprime⟩
  exact ⟨p, hpprime, hpprime.odd_of_ne_two hpne,
    exists_prime_orderOf_dvd_card' p (Nat.dvd_of_mem_primeFactors hp)⟩

omit [Finite G] in
private theorem conjugate_conjugate (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      L.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
private theorem commuting_pair {L : Subgroup G} (hc : CommutingConjugates M V L)
    (a b : localNormalizer M V)
    (hne : L.map (MulAut.conj (a : G)).toMonoidHom ≠
      L.map (MulAut.conj (b : G)).toMonoidHom) :
    L.map (MulAut.conj (a : G)).toMonoidHom ≤
      centralizer (L.map (MulAut.conj (b : G)).toMonoidHom : Set G) := by
  have hh := hc (a⁻¹ * b) (a⁻¹ * b).property
  rcases hh with he | hh
  · have he' := congrArg (Subgroup.map (MulAut.conj (a : G)).toMonoidHom) he
    simp only [conjugate_conjugate, Subgroup.coe_inv,
      mul_inv_cancel_left] at he'
    exact (hne he').elim
  · apply commutator_eq_bot_iff_le_centralizer.mp
    have hh' := congrArg (Subgroup.map (MulAut.conj (a : G)).toMonoidHom) hh
    simpa only [map_commutator, conjugate_conjugate, Subgroup.coe_mul,
      Subgroup.coe_inv, mul_inv_cancel_left, Subgroup.map_bot] using hh'

private theorem triple_fixed_involution [IsElementaryAbelian 2 V]
    {U L : Subgroup G} (hU : IsHyperplane V U)
    (hLU : L ≤ centralizer (U : Set G))
    (hdim : 3 < Module.finrank (ZMod 2) (Additive V))
    (g : Fin 3 → localNormalizer M V) :
    ∃ t : G, orderOf t = 2 ∧ ∀ i,
      L.map (MulAut.conj (g i : G)).toMonoidHom ≤ centralizer ({t} : Set G) := by
  let A : Fin 3 → Subgroup G := fun i => U.map (MulAut.conj (g i : G)).toMonoidHom
  have hc (i : Fin 3) : subgroupCorank V (A i) = 1 :=
    (corank_conjugate V U (g i) (g i).property.2).trans hU.2
  let W := A 0 ⊓ A 1 ⊓ A 2
  have hWc : subgroupCorank V W ≤ 3 := by
    have hh := corank_inf_le (V := V) (A 0 ⊓ A 1) (A 2)
    have hh' := corank_inf_le (V := V) (A 0) (A 1)
    rw [hc, hc] at hh'
    rw [hc] at hh
    dsimp only [W]
    omega
  have hWne : W ≠ ⊥ := by
    intro he
    rw [he, corank_bot] at hWc
    omega
  have hWA (i : Fin 3) : W ≤ A i := by
    fin_cases i
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hAV (i : Fin 3) : A i ≤ V := by
    have hv := mem_normalizer_iff_map_conj_eq.mp (g i).property.2
    exact (map_mono hU.1).trans_eq hv
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have htV : (t : G) ∈ V := hAV 0 (hWA 0 t.property)
  have ht2 : (t : G) ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨t, htV⟩)
  refine ⟨t, orderOf_eq_prime ht2 (fun hh => ht (Subtype.ext hh)), ?_⟩
  intro i
  have hcomm := congrArg (Subgroup.map (MulAut.conj (g i : G)).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr hLU)
  rw [map_commutator, Subgroup.map_bot] at hcomm
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro l hl
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (hcentral hl) t (hWA i t.property)).symm

/-- Three distinct commuting conjugates of a factor with two-group center
force odd rank three in an involution centralizer. -/
private theorem conjugates_ncard_le_two [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U L : Subgroup G} (hU : IsHyperplane V U)
    (hLU : L ≤ centralizer (U : Set G))
    (hdim : 3 < Module.finrank (ZMod 2) (Additive V))
    (hz : IsPGroup 2 (center L)) (hnot : ¬ IsPGroup 2 L)
    (hc : CommutingConjugates M V L) : (conjugates M V L).ncard ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨A, B, C, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff).mp (Nat.lt_of_not_ge hn)
  let g : Fin 3 → localNormalizer M V := ![a, b, c]
  let D : Fin 3 → Subgroup G := fun i => L.map (MulAut.conj (g i : G)).toMonoidHom
  have hD : Function.Injective D := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [D, g]
  obtain ⟨p, hp, ho, x, hx⟩ := exists_odd_prime_element hnot
  let : Fact p.Prime := ⟨hp⟩
  let e (i : Fin 3) : L ≃* D i := (MulAut.conj (g i : G)).subgroupMap L
  obtain ⟨t, ht, hDt⟩ := triple_fixed_involution hU hLU hdim g
  let H := centralizer ({t} : Set G)
  let F : Fin 3 → Subgroup H := fun i => (D i).subgroupOf H
  let eF (i : Fin 3) : F i ≃* D i := subgroupOfEquivOfLe (hDt i)
  have hcomm : Pairwise fun i j => F i ≤ centralizer (F j : Set H) := by
    intro i j hij z hz w hw
    apply Subtype.ext
    exact mem_centralizer_iff.mp (commuting_pair hc (g i) (g j)
      (fun he => hij (hD he)) hz) w hw
  have hzF (i : Fin 3) : IsPGroup 2 (center (F i)) :=
    hz.of_equiv (centerCongr ((e i).trans (eF i).symm))
  let y (i : Fin 3) : F i := (eF i).symm (e i x)
  have hy (i : Fin 3) : orderOf (y i) = p := by
    dsimp only [y]
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hx]
  have hl := Subgroup.card_le_primeRank_of_commuting_factors F ho hcomm hzF y hy
  have hu := h.simpleQTKE.toIsQTKE.involution_centralizer_stronglyQuasithin ht p hp ho
  change primeRank p H ≤ 2 at hu
  have : Fintype.card (Fin 3) = 3 := Fintype.card_fin _
  omega

/-- The actual M_V-conjugacy family has at most two members. E.6.13 and
E.6.21 are the only earlier conclusions retained as inputs. The proof applies
separately to ordinary components and the actual small alternating blocks. -/
public theorem twoConjugates [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h21 : OddCoreFree V) : TwoConjugates M V := by
  intro U hU hUh L hL he hc
  have hLU : L ≤ centralizer (U : Set G) := hL.elim And.left And.left
  have hr := (lemma_E_6_16_1 h h15 hUh (fun hh => he (hLU.trans hh))).1
  have hd := (lemma_E_6_17 h h15 h13 hr).2
  obtain ⟨hz, hnot⟩ := factor_center_and_not_two h21 hU hL
  exact conjugates_ncard_le_two h hUh hLU (by omega) hz hnot hc

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
