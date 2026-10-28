module
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OddCore
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientTwoRank
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.RankOneExclusion
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoRankBender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
/-!
# Excluding ordinary strict enlargements of the original moved factor

Retain an SQTK overgroup of L₀ and the exact O₂(L₀T), with the original
half-Sylow. Its nonconstrained C-component over L is quasisimple by the
source odd-core argument. The original moved A₅ group survives its central
two-core and supplies two-rank at least four in the simple quotient.
Together with cubic rank at most one and a surviving factor five, the
complete source catalogue forces a Bender quotient. The full original
Sylow then excludes a strict enlargement of the local C-component L.

Source: Aschbacher--Smith, Lemma 10.2.6, printed pp.748--749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- The nonconstrained branch is impossible in any overgroup retaining the original geometry. -/
theorem source_a5_orbit_overgroup_strict_component_not_nonconstrained
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H)
    (hsyl : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    {K : Subgroup G} (hK : K ∈ cComponentsIn H) (hLK : L < K)
    (h3 : primeRank 3 K ≤ 1) (hF : generalizedFitting K ≠ pCore 2 K) : False := by
  let : IsQuasisimple K := source_a5_orbit_overgroup_component_quasisimple D e hsq hXH hRH hK hF
  have hLK' : L.map (MulAut.conj 1).toMonoidHom ≤ K := by
    have hf : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      change 1 * x * (1 : G)⁻¹ = x
      simp
    simpa only [hf,map_id] using hLK.le
  have h2 : 4 ≤ primeRank 2 (K ⧸ pCore 2 K) :=
    source_a5_quasisimple_overgroup_quotient_twoRank D e hn hLK'
  have ho : pPrimeCore 2 K = ⊥ := by
    have hh := hK.2.subnormal.pPrimeCore_eq_bot
      (source_a5_orbit_overgroup_oddCore_eq_bot D e hsq hXH hRH) (K.subgroupOf H)
    have heq := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hK.1)
    rw [hh] at heq
    simpa only [Subgroup.map_bot] using heq.symm
  have hz : center K = pCore 2 K := IsQuasisimple.center_eq_pCore ho
  let qk : K ⧸ pCore 2 K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hz.symm
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    have hKsq : IsSQTK KnownSimple.IsKnownSimple K := ⟨
      hsq.stronglyQuasithin.of_injective (inclusion hK.1) (inclusion_injective hK.1),
      hsq.isKGroup.of_injective (inclusion hK.1) (inclusion_injective hK.1)⟩
    refine ⟨?_,hKsq.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp hop)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := (MulEquiv.isSimpleGroup_congr qk).mpr IsQuasisimple.simple
  have hmodel : Chapter1.Section02.LocalModels.TheoremCModel (K ⧸ pCore 2 K) :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
      (ChapterA.Section02.theoremC_knownSimple (G := K ⧸ pCore 2 K) inferInstance
        (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
        hsqtk.stronglyQuasithin hsqtk.isKGroup)
  have hb := SourceEmbeddings.bender_of_large_twoRank_low_threeRank_five hmodel h2
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans h3)
    (source_a5_conjugate_overgroup_five e hLK')
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsyl hK.1 hK.2.subnormal
  have hSe : (S : Subgroup K) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hlocal : L.subgroupOf K ∈ localCComponents S := by
    rw [hSe]
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLK.le
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have hproper : ∀ (S' : Sylow 2 K) (P : Subgroup K),
      (S' : Subgroup K) ≤ P → P ≠ ⊤ → Group.IsSolvable P := by
    intro S' P hSP hneP
    exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (G := K) (fun Q' P' hQ' hneQ' => SourceEmbeddings.bender_solvable_proper_sylow_overgroup hb Q' P' hQ' hneQ')
      S' P hSP hneP
  have heL := SourceEmbeddings.eq_of_solvable_sylow_overgroups S hlocal htop le_top
    (isSolvable_proper_sylow_overgroup_of_equiv topEquiv hproper)
  exact hLK.ne (le_antisymm hLK.le (subgroupOf_eq_top.mp heL))
end CFSG.Quasithin.Chapter10
