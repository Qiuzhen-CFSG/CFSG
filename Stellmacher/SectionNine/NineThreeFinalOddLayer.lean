module

public import Stellmacher.SectionNine.NineThreeFinalCentralizerSetup
public import Theory.GroupTheory.Fitting.Centralizer
public import FeitThompson.BGsection1.PLengthLemmas

/-!
# Nontrivial odd-layer action in the final centralizer of (9.3)

In a finite solvable group with trivial two-core, a nontrivial two-subgroup
cannot centralize the odd core: the Fitting subgroup lies in the odd core
and is self-centralizing. Apply this to the quotient by the two-core, then
lift the commutator to the actual odd-core preimage.

For the normalized mixed centralizer, the existing initial-center
noncontainment and conditional Sylow setup supply exactly these inputs.
This proves the odd-layer commutator assertion on printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`. It does not assert the subsequent
core-intersection bound or the transvection conclusion.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem fitting_le_odd_core_of_two_core_eq_bot
    {K : Type*} [Group K] [Finite K] (hcore : pCore 2 K = ⊥) :
    fittingSubgroup K ≤ pPrimeCore 2 K := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun prime => ?_
  by_cases heq : prime.val.val = 2
  · rw [heq, hcore]
    exact bot_le
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨exponent, hcard⟩ :=
      (pCore_isPGroup (p := prime.val.val) (G := K)).exists_card_eq
    rw [hcard]
    exact ((Nat.coprime_primes Nat.prime_two
      (Nat.prime_of_mem_primeFactors prime.val.property)).mpr (Ne.symm heq)).pow_right _

public theorem two_subgroup_odd_core_commutator_ne_bot
    {K : Type*} [Group K] [Finite K]
    (hsolvable : Group.IsSolvable K) (hcore : pCore 2 K = ⊥)
    (vectors : Subgroup K) (hp : IsPGroup 2 vectors) (hne : vectors ≠ ⊥) :
    ⁅pPrimeCore 2 K, vectors⁆ ≠ ⊥ := by
  intro hcomm
  have hcentral : vectors ≤ Subgroup.centralizer (pPrimeCore 2 K : Set K) :=
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hodd : vectors ≤ pPrimeCore 2 K :=
    hcentral.trans ((Subgroup.centralizer_le
      (fitting_le_odd_core_of_two_core_eq_bot hcore)).trans
        ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvable).trans
          (fitting_le_odd_core_of_two_core_eq_bot hcore)))
  have hcoprime : Nat.Coprime (Nat.card vectors) (Nat.card (pPrimeCore 2 K)) := by
    obtain ⟨exponent, hcard⟩ := hp.exists_card_eq
    rw [hcard]
    exact (pPrimeCore_coprime_card (p := 2) (G := K)).pow_left _
  exact hne (le_bot_iff.mp ((le_inf le_rfl hodd).trans
    (Subgroup.disjoint_of_coprime_natCard hcoprime).le_bot))

public theorem two_subgroup_odd_layer_commutator_not_le_core
    {K : Type*} [Group K] [Finite K]
    (hsolvable : Group.IsSolvable K)
    (vectors : Subgroup K) (hp : IsPGroup 2 vectors)
    (hnot : ¬ vectors ≤ pCore 2 K) :
    ¬ ⁅(pPrimeCore 2 (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)),
      vectors⁆ ≤ pCore 2 K := by
  let quotient := QuotientGroup.mk' (pCore 2 K)
  have hquotientCore : pCore 2 (K ⧸ pCore 2 K) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) (pCore 2 K)
      (pCore_isPGroup (p := 2) (G := K)), QuotientGroup.map_mk'_self]
  have hne : vectors.map quotient ≠ ⊥ := by
    intro hbot
    exact hnot (by simpa [quotient] using
      ((Subgroup.map_eq_bot_iff (f := quotient) (H := vectors)).mp hbot))
  let _ := hsolvable
  have hcomm := two_subgroup_odd_core_commutator_ne_bot
    (inferInstance : Group.IsSolvable (K ⧸ pCore 2 K)) hquotientCore
    (vectors.map quotient) (hp.map quotient) hne
  intro hle
  apply hcomm
  have hmap := Subgroup.map_mono (f := quotient) hle
  rw [Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] at hmap
  exact le_bot_iff.mp hmap

public theorem nine_three_final_odd_layer_commutator_not_le_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hgeometry :
      let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
      Nat.card mixed = 2 ∧ ∃ conjugator : G,
        conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
        T.map (MulAut.conj conjugator).toMonoidHom ≤
          Subgroup.centralizer (mixed : Set G)) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    ¬ ⁅(pPrimeCore 2 (centralizer ⧸ pCore 2 centralizer)).comap
        (QuotientGroup.mk' (pCore 2 centralizer)),
      ((ZAt ctx.Γ ctx.criticalPath.a).map embedding).subgroupOf centralizer⁆ ≤
        pCore 2 centralizer := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  have hcentral : vectors ≤ centralizer :=
    (nine_three_final_centralizer_center_core ctx hb hlarge first second config).1
  have hneighbor : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hp : IsPGroup 2 vectors :=
    (IsElementaryAbelian.isPGroup 2 (z ctx.Γ ctx.criticalPath.a)).map embedding
  apply two_subgroup_odd_layer_commutator_not_le_core
    (nine_three_final_centralizer_setup_of_mixed_sylow ctx first second config hgeometry).1
    (vectors.subgroupOf centralizer)
    (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hcentral).symm)
  intro hle
  apply nine_three_initial_center_not_le_final_centralizer_core
    ctx hb hlarge first second config
  have hmap := Subgroup.map_mono (f := centralizer.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hcentral] at hmap

end Stellmacher.SectionNine
