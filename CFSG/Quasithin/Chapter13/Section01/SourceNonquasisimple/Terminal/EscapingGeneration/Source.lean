module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.EscapingGeneration
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.EscapingGeneration.Models
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta.Outside
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension

/-!
# Constructing the escaping E₂-overgroup from source 13.1.6

Choose a maximal two-local distinct from N_G(L) and use the proved theta
or component construction to obtain the actual escaping Y. Relative
normality puts YT inside that local. The odd-prime alternative is solvable,
so E₁-containment excludes it. The five-model sieve excludes every remaining
quotient except A₅. The literal quotient of YT by its two-core is then A₅
or S₅, which proves both the ambient two-rank bound and E₂-generation.

The constructed join feeds Terminal.false_of_escaping_two_generated and
the actual Hypothesis1331 maximal-counterexample consumer. The canonical
stars belong to qt-d-1314-canonical-radical-star; earlier 13.1.2 classification
and rigidity, TI and normalizer uniqueness retain their final discharge
with qt-d-1317-source. There is no assumed escaping witness, model label,
rank bound or E-generation premise in the resulting contradiction.

Source: Aschbacher--Smith 13.1.6, p.868, and the terminal proof of 13.1.7,
p.876; E.1.13--14, p.214. All quotient maps are the intrinsic core maps.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterE Supplements.Escape
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem oddShape_solvable {Y : Subgroup G} (hy : OddShape Y) : Group.IsSolvable Y := by
  obtain ⟨_,d,hp,_,hd,_⟩ := hy
  let : Fact d.Prime := ⟨hp⟩
  let : Group.IsNilpotent (XiQuotient Y) := hd.isNilpotent
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr ⟨inferInstance,inferInstance⟩

/-- The actual 13.1.6 witness produces A₅ at the subgroup YT. -/
theorem a5EscapeSource_of_witness (h : Hypothesis1311 T)
    (hclass : QuasisimpleClassification T)
    {L H Y : Subgroup G} (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (w : Witness T L H Y)
    (hcontain : ∀ J : Subgroup G, (T : Subgroup G) ≤ J →
      IsEGenerated 1 J → J ≤ normalizer (L : Set G)) :
    A5EscapeSource T (normalizer (L : Set G)) (Y ⊔ (T : Subgroup G)) Y := by
  let J := Y ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le w.le_overgroup hTH
  have hHY := (normal_subgroupOf_iff_le_normalizer w.le_overgroup).mp w.normal
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hTH.trans hHY
  have hnJ : (Y.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le Y.le_normalizer hTY)
  have hout : ¬ J ≤ normalizer (L : Set G) := fun hj => w.outside (le_sup_left.trans hj)
  rcases w.alternatives with ho | ⟨hc,hq,hf⟩
  · let : Group.IsSolvable Y := oddShape_solvable ho
    let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
    let : Group.IsSolvable J := Group.isSolvable_sup_of_normalizes _ _ hTY
    exact (hout (hcontain J le_sup_right isEGenerated_one_of_solvable)).elim
  · let B := Y.subgroupOf J
    let e : B ≃* Y := subgroupOfEquivOfLe le_sup_left
    let eQ : (B ⧸ pCore 2 B) ≃* XiQuotient Y :=
      QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    let : B.Normal := hnJ
    let : IsQuasisimple (XiQuotient Y) := hq
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
    let S : Sylow 2 J := T.subtype le_sup_right
    have hBS : B ⊔ (S : Subgroup J) = ⊤ := by
      rw [Sylow.coe_subtype,← subgroupOf_sup (show Y ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right),subgroupOf_self]
    have hsq := (h.simpleQTKE.twoLocal_sqtk hH.1).subgroup (J.subgroupOf H)
    have hsqJ := (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp hsq
    have hm : FiveQuotients (B ⧸ pCore 2 B) := fiveQuotients_of_equiv eQ (hclass Y hf hq)
    rcases a5_or_generation_of_fiveQuotients hsqJ B hm S hBS with ha | hg
    · obtain ⟨a⟩ := ha
      have ey : XiQuotient Y ≃* alternatingGroup (Fin 5) := eQ.symm.trans a
      have hr : primeRank 2 (J ⧸ pCore 2 J) ≤ 2 := by
        rcases Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
            Y (T : Subgroup G) hTY T.isPGroup' ey with hb | hb
        · obtain ⟨b⟩ := hb
          rw [primeRank_equiv 2 b]
          exact (Theory.GroupTheory.primeRank_le_of_injective 2 (alternatingGroup (Fin 5)).subtype
            (alternatingGroup (Fin 5)).subtype_injective).trans
            Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
        · obtain ⟨b⟩ := hb
          rw [primeRank_equiv 2 b]
          exact Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
      exact ⟨⟨le_sup_left,hc.2.subgroupOf_of_le le_sup_left hJH⟩,hnJ,w.outside,⟨a⟩,hr⟩
    · exact (hout (hcontain J le_sup_right hg)).elim

/-- Construct the A₅ source premise from original 13.1.6 and 13.1.2. -/
theorem exists_a5EscapeSource (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hcontain : ∀ J : Subgroup G, (T : Subgroup G) ≤ J →
      IsEGenerated 1 J → J ≤ normalizer (L : Set G)) :
    ∃ Y : Subgroup G, A5EscapeSource T (normalizer (L : Set G))
      (Y ⊔ (T : Subgroup G)) Y := by
  have hex : ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ (T : Subgroup G) ≤ H ∧
      H ≠ normalizer (L : Set G) := by
    obtain ⟨A,hA,B,hB,hAB⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases he : A = normalizer (L : Set G)
    · exact ⟨B,hB.1,hB.2,fun hb => hAB (he.trans hb.symm)⟩
    · exact ⟨A,hA.1,hA.2,he⟩
  obtain ⟨H,hH,hTH,hne⟩ := hex
  obtain ⟨Y,w⟩ := Theta.witness_exists_of_stars h hmany hs hrig hL hn hH hTH hne
  exact ⟨Y,a5EscapeSource_of_witness h hclass hH hTH w hcontain⟩

/-- The escaping E₂-generated overgroup is the original join YT. -/
theorem exists_escaping_two_generated_of_source (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hcontain : ∀ J : Subgroup G, (T : Subgroup G) ≤ J →
      IsEGenerated 1 J → J ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, (T : Subgroup G) ≤ J ∧
      ¬ J ≤ normalizer (L : Set G) ∧ IsEGenerated 2 J := by
  obtain ⟨Y,s⟩ := exists_a5EscapeSource h hmany hs hrig hclass hL hn hcontain
  exact ⟨Y ⊔ (T : Subgroup G),le_sup_right,
    fun hj => s.outside (le_sup_left.trans hj),s.isEGenerated_of_sup rfl⟩

/-- Apply the constructed escape to the proved corank-two terminal containment.
The final 13.1.7 owner discharges the earlier stars, Chapter12 clauses, TI
and normalizer uniqueness; no escape or generation premise remains. -/
theorem false_of_source_escaping (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L))
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)}) : False := by
  apply false_of_escaping_two_generated h hmany hL hn hTI hunique
  apply exists_escaping_two_generated_of_source h hmany hs hrig hclass hL hn
  intro J hTJ hgen
  exact le_normalizer_of_isEGenerated_two h hmany hL hn hTI hunique hTJ
    (hgen.mono (by decide))

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal 13.3.1 consumer, with the escaping-generation premise discharged. -/
theorem Hypothesis1331.false_of_nonquasisimple_source_escape
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T)
    (hTI : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → IsTISubgroup (normalizerMoved K))
    (hcontrol : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → maximalTwoLocalOvergroups (normalizer
        (((T : Subgroup G) ⊓ centralizer (normalizerMoved K : Set G) : Subgroup G) : Set G)) =
          {normalizer (K : Set G)}) : False := by
  obtain ⟨K,_,hLK,hf,hkn,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact false_of_source_escaping h.hypothesis1311 hmany hs hrig hclass hf hkn.2
    (hTI K hLK hf hkn.2) (hcontrol K hLK hf hkn.2)

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
