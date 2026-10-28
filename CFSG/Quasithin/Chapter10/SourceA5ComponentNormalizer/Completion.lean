module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Constrained
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Nonconstrained
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoRankBender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
/-!
# Source 10.2.6: the original component normalizer lies in M

A contrary normalizer supplies a strict normal containing C-component with
three-rank at most one. The completed constrained branch forces this component
to be quasisimple after the original module kills the odd normalizer core.
Its literal two-core quotient is simple and has the full Theorem C catalogue.
The original A₅ moved subgroup forces two-rank at least four there, and the
original A₅ section supplies a factor of five. The complete model inspection
leaves a Bender group. Proper full-Sylow overgroups in that group are solvable;
lifting through the two-core contradicts the actual strict local component.

This discharges the normalizer containment of 10.2.6 from the original
Fundamental Setup, its A₅ quotient and nonnormal Sylow orbit. No Baumann escape,
point-centralizer control, module marking or embedding-list premise is used.
Source: Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- The genuine nonconstrained strict opposite-component branch is impossible. -/
theorem source_a5_strict_component_not_nonconstrained
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hBK : L.map (MulAut.conj t).toMonoidHom < K)
    (h3 : primeRank 3 K ≤ 1) (hF : generalizedFitting K ≠ pCore 2 K) : False := by
  let : IsQuasisimple K := source_a5_nonconstrained_component_quasisimple D e hn hK hF
  have h2 : 4 ≤ primeRank 2 (K ⧸ pCore 2 K) :=
    source_a5_quasisimple_overgroup_quotient_twoRank D e hn hBK.le
  have ho : pPrimeCore 2 K = ⊥ := by
    have hh := hK.2.subnormal.pPrimeCore_eq_bot
      (source_a5_component_normalizer_oddCore_eq_bot D e hn) (K.subgroupOf (normalizer (L : Set G)))
    have heq := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hK.1)
    rw [hh] at heq
    simpa only [Subgroup.map_bot] using heq.symm
  have hz : center K = pCore 2 K := IsQuasisimple.center_eq_pCore ho
  let qk : K ⧸ pCore 2 K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hz.symm
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    have hs := source_component_normalizer_sqtk D
    have hKsq : IsSQTK KnownSimple.IsKnownSimple K := ⟨
      hs.stronglyQuasithin.of_injective (inclusion hK.1) (inclusion_injective hK.1),
      hs.isKGroup.of_injective (inclusion hK.1) (inclusion_injective hK.1)⟩
    refine ⟨?_,hKsq.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans (hKsq.stronglyQuasithin p hp hop)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := (MulEquiv.isSimpleGroup_congr qk).mpr IsQuasisimple.simple
  have hmodel : Chapter1.Section02.LocalModels.TheoremCModel (K ⧸ pCore 2 K) :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
      (ChapterA.Section02.theoremC_knownSimple (G := K ⧸ pCore 2 K) inferInstance
        (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
        hsqtk.stronglyQuasithin hsqtk.isKGroup)
  have hb := SourceEmbeddings.bender_of_large_twoRank_low_threeRank_five hmodel h2
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans h3)
    (source_a5_conjugate_overgroup_five e hBK.le)
  let B := L.map (MulAut.conj t).toMonoidHom
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (source_a5_component_normalizer_sylow D e hn) hK.1 hK.2.subnormal
  have hSe : (S : Subgroup K) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hBL : B ∈ localCComponents (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr D.maximal.1
    have heT : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [heT] at hh
    exact hh.1
  have hlocal : B.subgroupOf K ∈ localCComponents S := by
    rw [hSe]
    exact SourceEmbeddings.local_restrict (localCComponents_antitone inf_le_left hBL) hBK.le
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have hproper : ∀ (S' : Sylow 2 K) (P : Subgroup K),
      (S' : Subgroup K) ≤ P → P ≠ ⊤ → Group.IsSolvable P := by
    intro S' P hSP hneP
    exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (G := K) (fun Q' P' hQ' hneQ' => SourceEmbeddings.bender_solvable_proper_sylow_overgroup hb Q' P' hQ' hneQ')
      S' P hSP hneP
  have heB := SourceEmbeddings.eq_of_solvable_sylow_overgroups S hlocal htop le_top
    (isSolvable_proper_sylow_overgroup_of_equiv topEquiv hproper)
  have heBK : B = K := le_antisymm hBK.le (subgroupOf_eq_top.mp heB)
  exact hBK.ne heBK
/-- Source 10.2.6(2), with every earlier model and module premise discharged. -/
theorem source_a5_component_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (L : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨t,ht,_,_,K,hK,_,hBK,_,h3,_,hF⟩ :=
    source_a5_nonconstrained_normalizer_enlargement D e hn hout
  exact source_a5_strict_component_not_nonconstrained D e hn ht hK hBK h3 hF

end CFSG.Quasithin.Chapter10
