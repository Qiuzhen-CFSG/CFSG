module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness.Source

/-!
# The actual outside-core witness for 15.4.2(4)

B.6.8(5) identifies the normal Sylow two-subgroup of the core of H ∩ M with
O₂(H). Thus the given V outside O₂(H) is outside that core. The source local
geometry verifies E.2.8, and universal solvable E.2.9 supplies a subgroup I
with the original conjugator, generation, Sylow intersection, two-closed
normal core, and an actual odd-prime-power dihedral quotient.

We prove the E.2.11(1) restriction to I, derive the order-two image from this
model and generation, and establish properness. E.2.9(2) supplies the required
generalized-Fitting equality. The final application uses the proved actor
inside O₂(I) ≤ T ≤ M₀ on the original intrinsic V and its literal centralizer
quotient. Neither H nor I is assumed to normalize V.

This completes the conditional outside-core application. The universal source
implications defined in `OutsideWitness.Source` retain their earlier producers;
final assembly of `Earlier1542Four` remains with qt-15-04-ratio-source.

Source: Aschbacher–Smith, B.6.8(5), E.2.8–13, and 15.4.2(4), printed
pp.113–114, 221–225, and 1156 of the combined manuscript (1 March 2004).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
universe u
variable {X : Type u} [Group X] [Finite X]
variable {T : Sylow 2 X} {H N V I : Subgroup X}

/-- B.6.8(5) places every two-subgroup of the normal core in O₂(H). -/
private theorem le_core_of_le_normalCore (h685 : EarlierB685.{u})
    (hmin : ChapterB.IsMinimalParabolicOver T H)
    (hTN : (T : Subgroup X) ≤ N) (hNH : N ⋖ H)
    (hV : IsPGroup 2 V)
    (hle : V ≤ (N.subgroupOf H).normalCore.map H.subtype) :
    V ≤ H.pCoreIn 2 := by
  let J := (N.subgroupOf H).normalCore
  obtain ⟨S, hSn, hSeq⟩ := h685 X T H N hmin hTN hNH
  let := Sylow.unique_of_normal S hSn
  have hVH : V ≤ H := hle.trans (map_subtype_le J)
  have hVJ : V.subgroupOf H ≤ J := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hle hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hp : IsPGroup 2 ((V.subgroupOf H).subgroupOf J) :=
    hV.comap_subtype.comap_subtype
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  have hS : (V.subgroupOf H).subgroupOf J ≤ (S : Subgroup J) := by
    simpa only [Subsingleton.elim R S] using hR
  have hm := map_mono (f := J.subtype) hS
  rw [map_subgroupOf_eq_of_le hVJ, hSeq] at hm
  have hh := map_mono (f := H.subtype) hm
  rwa [map_subgroupOf_eq_of_le hVH] at hh

omit [Finite X] in
/-- The restriction argument of E.2.11(1), with the literal Sylow intersection. -/
private theorem geometry (c : Configuration T H N V)
    (w : SolvableMember T H N V I)
    (hn : H ⊓ normalizer (V : Set X) ≤ N) :
    ChapterE.TwoConjugate.Hypotheses w.sylow (V.subgroupOf I)
      (N.subgroupOf I) w.conjugator := by
  let := c.elementary
  have hVS : V.subgroupOf I ≤ (w.sylow : Subgroup I) := by
    apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le w.le_I, w.sylow_eq]
    exact le_inf c.le_sylow w.le_I
  have hST : (w.sylow : Subgroup I).map I.subtype ≤ (T : Subgroup X) :=
    w.sylow_eq.le.trans inf_le_left
  have hTV := (normal_subgroupOf_iff_le_normalizer c.le_sylow).mp c.normal_in_sylow
  have hSN : (w.sylow : Subgroup I) ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq w.le_I]
    exact (map_le_iff_le_comap).mp (hST.trans hTV)
  have hlocal : V.subgroupOf I ≤ (N.subgroupOf I).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le w.le_I,
      map_pCoreIn_of_injective 2 _ _ I.subtype_injective, subgroupOf_map_subtype]
    exact (le_inf (le_inf (c.le_core.trans (pCoreIn_le 2 N)) w.le_I) c.le_core).trans
      (inf_pCoreIn_le_of_le 2 inf_le_left)
  refine ⟨IsElementaryAbelian.subgroupOf w.le_I,
    hVS, (normal_subgroupOf_iff_le_normalizer hVS).mpr hSN, ?_, hlocal,
    w.core_two_closed, w.generate⟩
  · rw [← subgroupOf_normalizer_eq w.le_I]
    intro x hx
    exact hn ⟨w.le_H x.property, hx⟩

/-- Generation makes the image nontrivial; the odd dihedral model makes its
two-power order divide two. No image-cardinality certificate is assumed. -/
private theorem quotient_card (w : SolvableMember T H N V I)
    (hV : IsPGroup 2 V) :
    Nat.card ((V.subgroupOf I).map
      (QuotientGroup.mk' (N.subgroupOf I).normalCore)) = 2 := by
  let J := (N.subgroupOf I).normalCore
  let q := QuotientGroup.mk' J
  let U := (V.subgroupOf I).map q
  obtain ⟨p, a, hp, hp2, ha, ⟨e⟩⟩ := w.dihedral
  have hc : Nat.card (I ⧸ J) = 2 * p ^ a :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hne : U ≠ ⊥ := by
    intro he
    have hVJ : V.subgroupOf I ≤ J := by
      simpa only [q, QuotientGroup.ker_mk'] using ((Subgroup.map_eq_bot_iff _).mp he)
    have hWJ : (V.subgroupOf I).map (MulAut.conj w.conjugator).toMonoidHom ≤ J := by
      have hJmap : J.map (MulAut.conj w.conjugator).toMonoidHom = J :=
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
      exact (map_mono hVJ).trans_eq hJmap
    have ht : J = ⊤ := top_unique (w.generate ▸ sup_le hVJ hWJ)
    have hc1 : Nat.card (I ⧸ J) = 1 := by rw [ht]; simp
    have : 0 < p ^ a := pow_pos hp.pos a
    omega
  have hU : IsPGroup 2 U := hV.comap_subtype.map q
  obtain ⟨b, hb⟩ := hU.exists_card_eq
  have hd : Nat.card U ∣ 2 * p ^ a := hc ▸ U.card_subgroup_dvd_card
  have hcop : (Nat.card U).Coprime (p ^ a) := by
    rw [hb]
    exact (Nat.coprime_primes Nat.prime_two hp |>.mpr hp2.symm).pow b a
  have hdiv : Nat.card U ∣ 2 := hcop.dvd_of_dvd_mul_right hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with he | he
  · exact False.elim (hne (U.eq_bot_of_card_eq he))
  · exact he

/-- V cannot equal I, since its normalizer would then make the core quotient trivial. -/
private theorem proper (c : Configuration T H N V)
    (w : SolvableMember T H N V I)
    (hg : ChapterE.TwoConjugate.Hypotheses w.sylow (V.subgroupOf I)
      (N.subgroupOf I) w.conjugator) : V.subgroupOf I ≠ ⊤ := by
  intro he
  have hN : N.subgroupOf I = ⊤ := by
    apply top_unique
    simpa only [he, normalizer_eq_top] using hg.normalizer_le
  let := c.elementary
  have hc := quotient_card w (IsElementaryAbelian.isPGroup 2 V)
  have hb : (V.subgroupOf I).map
      (QuotientGroup.mk' (N.subgroupOf I).normalCore) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk', hN, normalCore_eq_self]
    exact le_top
  simp [hb] at hc

variable {G : Type u} [Group G] [Finite G]
variable {T₀ : Sylow 2 G} {M₀ M H₀ : Subgroup G} {V₀ : Subgroup M₀}

/-- All E.2.8 hypotheses for the actual H and H ∩ M follow from the local data. -/
private theorem configuration
    (h685 : EarlierB685.{u})
    (h : MaximalPrimeSource.SourceHypotheses T₀)
    (l : LocalHypotheses T₀ M₀ M V₀)
    (hH : H₀ ∈ Chapter3.HStar (T₀ : Subgroup G) M)
    (hout : ¬ V₀.map M₀.subtype ≤ H₀.pCoreIn 2) :
    Configuration T₀ H₀ (H₀ ⊓ M) (V₀.map M₀.subtype) := by
  let := l.reduced.elementary
  let : IsElementaryAbelian 2 (V₀.map M₀.subtype) :=
    IsElementaryAbelian.map M₀.subtype
  have hmin := l.minimalParabolic hH hout
  obtain ⟨hTN, hNH, _⟩ := Chapter3.HStar.unique_maximal T₀
    (l.mem_H.2.trans l.le_maximal) hH
  refine ⟨hmin, hTN, hNH, Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1,
    inferInstance, l.module_le_sylow,
    (normal_subgroupOf_iff_le_normalizer l.module_le_sylow).mpr
      (l.mem_H.2.trans l.normalizes), l.module_le_intersection_core hH, ?_⟩
  intro hJ
  exact hout (le_core_of_le_normalCore h685 hmin hTN hNH
    (IsElementaryAbelian.isPGroup 2 _) hJ)

/-- Construct every field of the actual two-conjugate witness in the outside-core
branch of 15.4.2(4), from universal earlier source implications. -/
theorem exists_witness
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h685 : EarlierB685.{u}) (h29 : EarlierE29Solvable.{u})
    (h : MaximalPrimeSource.SourceHypotheses T₀)
    (l : LocalHypotheses T₀ M₀ M V₀)
    (hH : H₀ ∈ Chapter3.HStar (T₀ : Subgroup G) M)
    (hout : ¬ V₀.map M₀.subtype ≤ H₀.pCoreIn 2) :
    ∃ I : Subgroup G, Nonempty (TwoConjugateRatio.Witness T₀ M
      (V₀.map M₀.subtype) H₀ I) := by
  have c := configuration h685 h l hH hout
  have hs := solvable_of_mem_HOver hA hC T₀ h hH.1.1
  obtain ⟨hex, hf⟩ := h29 G T₀ H₀ (H₀ ⊓ M) (V₀.map M₀.subtype) c hs
  obtain ⟨I, ⟨w⟩⟩ := hex
  have hg := geometry c w (l.normalizer_le_intersection hH hout)
  have hpr := proper c w hg
  have hfit := hf I w (fitting_eq_core_of_HStar h hH)
  let := c.elementary
  have hcard := quotient_card w (IsElementaryAbelian.isPGroup 2 _)
  have hswap : (H₀ ⊓ M).subgroupOf I = (M ⊓ H₀).subgroupOf I := by
    rw [inf_comm]
  refine ⟨I, ⟨{
    mem_HStar := hH
    le_H := w.le_H
    le_I := w.le_I
    sylow := w.sylow
    sylow_le := w.sylow_eq.le.trans inf_le_left
    conjugator := w.conjugator
    geometry := ?_
    proper := hpr
    fitting := hfit
    quotient_card := ?_ }⟩⟩
  · rwa [hswap] at hg
  · rw [hswap] at hcard
    exact hcard

/-- The outside-core bound for the exact original M₀/C_M₀(V) representation
on intrinsic V. The earlier universal A/C, B.6.8(5), and solvable E.2.9
implications remain explicit; no selected witness or cardinality premise remains. -/
theorem cubicRatio_le_two
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h685 : EarlierB685.{u}) (h29 : EarlierE29Solvable.{u})
    (h : MaximalPrimeSource.SourceHypotheses T₀)
    (l : LocalHypotheses T₀ M₀ M V₀)
    (hH : H₀ ∈ Chapter3.HStar (T₀ : Subgroup G) M)
    (hout : ¬ V₀.map M₀.subtype ≤ H₀.pCoreIn 2) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    Representation.BinaryOffender.cubicRatio
      (Representation.NormalElementaryQuotient.representation V₀
        (QuotientGroup.mk' (centralizer (V₀ : Set M₀)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  obtain ⟨I, ⟨w⟩⟩ := exists_witness hA hC h685 h29 h l hH hout
  exact l.cubicRatio_le_two_of_witness w

end CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
