module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.EarlierSources
public import Theory.Alternating.PrimeRank

/-!
# The normal component envelope in the paired cubic branch

For an involution r centralizing the source A₆ component K, the same K is
an ordinary component of C_{C_G(r)}(z₂). Its three-rank is two and its odd
core is trivial. The completed rank-two theorem I.3.1(3), with both earlier
known-simple structure inputs discharged, therefore places this literal K
inside an ordinary normal component of C_G(r).

This supplies the envelope used in the second claim of 2.4.36. Identifying
the envelope with K is the subsequent source argument; the conclusion here
retains the original embeddings into G.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 2.4.36,
printed p.549, and I.3.1(3), printed pp.414–415.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual A₆ component has an ordinary normal envelope in the
centralizer of every involution centralizing it. -/
theorem normal_component_envelope
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (z : G) (hz : z ^ 2 = 1) (K : Subgroup (involutionCentralizer z))
    [K.Normal] (eK : K ≃* A6)
    (r : involutionCentralizer z)
    (hr : r ∈ centralizer (K : Set (involutionCentralizer z)))
    (hr2 : orderOf r = 2) :
    ∃ J : Subgroup (involutionCentralizer (r : G)),
      IsComponent (involutionCentralizer (r : G)) J ∧ J.Normal ∧
        K.map (involutionCentralizer z).subtype ≤
          J.map (involutionCentralizer (r : G)).subtype := by
  let H := involutionCentralizer (r : G)
  have hrG : orderOf (r : G) = 2 :=
    (orderOf_injective (involutionCentralizer z).subtype
      (involutionCentralizer z).subtype_injective r).trans hr2
  have hH := hG.involution_centralizer_sqtk hrG
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp r.property).symm⟩
  let P := zpowers zH
  have hP : IsPGroup 2 P :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2)
      (show zH ^ 2 = 1 from Subtype.ext hz)).isPGroup 2 _
  let L := K.map (involutionCentralizer z).subtype
  have hLH : L ≤ H := by
    intro k hk
    change k ∈ K.map (involutionCentralizer z).subtype at hk
    obtain ⟨a, ha, he⟩ := mem_map.mp hk
    rw [← he]
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hr a ha))
  have hLN : involutionCentralizer z ≤ normalizer (L : Set G) := by
    have hh := K.le_normalizer_map (involutionCentralizer z).subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
  let A := L.subgroupOf H
  let C := centralizer (P : Set H)
  have hAC : A ≤ C := by
    intro a ha
    change a ∈ centralizer (zpowers zH : Set H)
    rw [zpowers_eq_closure, centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (map_subtype_le K ha)
  have hCA : C ≤ normalizer (A : Set H) := by
    intro a ha
    have haz : (a : G) ∈ involutionCentralizer z := by
      change a ∈ centralizer (zpowers zH : Set H) at ha
      rw [zpowers_eq_closure, centralizer_closure] at ha
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (hLN haz) l
  let B := A.subgroupOf C
  let eL : L ≃* A6 :=
    (K.equivMapOfInjective (involutionCentralizer z).subtype
      (involutionCentralizer z).subtype_injective).symm.trans eK
  let e : B ≃* A6 :=
    (subgroupOfEquivOfLe hAC).trans ((subgroupOfEquivOfLe hLH).trans eL)
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple A6 := { simple := ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : B.Normal := normal_subgroupOf_of_le_normalizer hCA
  have hcomp : IsComponent C B := ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩
  have ho6 : pPrimeCore 2 A6 = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 A6).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hc := pPrimeCore_coprime_card (p := 2) (G := A6)
      rw [ht, Nat.card_congr topEquiv.toEquiv, card_A6] at hc
      norm_num at hc
  have hoB : pPrimeCore 2 B = ⊥ := by
    apply ((pPrimeCore 2 B).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [pPrimeCore_map_iso, ho6]
  have htwo : IsTwoComponent B := by
    refine ⟨hcomp.isCComponent, ?_⟩
    exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hoB).trans
        (QuotientGroup.quotientBot (G := B))).symm
  have hrank : primeRank 3 B = 2 := by
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]
  obtain ⟨_, J, hJ, hn, hBJ⟩ :=
    ChapterI.RankTwoSource.lemma_I_3_1_three_of_earlier_structure
      ChapterI.RankTwoSource.earlierA36_knownSimple
      ChapterI.RankTwoSource.earlierA38_knownSimple hH P hP B htwo hrank
  have hAJ : A ≤ J := by
    change (A.subgroupOf C).map C.subtype ≤ J at hBJ
    rwa [map_subgroupOf_eq_of_le hAC] at hBJ
  refine ⟨J, hJ, hn, ?_⟩
  simpa only [A, map_subgroupOf_eq_of_le hLH] using map_mono (f := H.subtype) hAJ

/-- The correlated source geometry supplies the same envelope on its original
component and original embeddings. -/
theorem SourceComponentGeometry.normal_component_envelope
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {d : MinimalBlockSetup M} (b : SourceComponentGeometry d)
    (r : involutionCentralizer b.z)
    (hr : r ∈ centralizer (b.K : Set (involutionCentralizer b.z)))
    (hr2 : orderOf r = 2) :
    ∃ J : Subgroup (involutionCentralizer (r : G)),
      IsComponent (involutionCentralizer (r : G)) J ∧ J.Normal ∧
        b.K.map (involutionCentralizer b.z).subtype ≤
          J.map (involutionCentralizer (r : G)).subtype :=
  DoubleA3.normal_component_envelope hG b.z b.involution b.K b.componentEquiv r hr hr2

end CFSG.Quasithin.Chapter2.DoubleA3
