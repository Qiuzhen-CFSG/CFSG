module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.MixedNontrivial
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.CubicResidualQuotient
public import Stellmacher.FullBaumannLocalNormalizer

/-!
# The actual nontrivial mixed subgroup and its local normalizer

In the large-center cubic branch, the mixed commutator is nontrivial and
lies in the initial elementary center. The large-center Baumann bound
makes the whole mixed subgroup centralize B(T), so the intersection used
in the source centralizer step is exactly this subgroup. Both extracted
groups centralize it. The literal residual--Baumann commutator is full
and has three-group quotient over its two-core.

Its nontrivial two-group normalizer is thus a genuine two-local overgroup.
The two-cores of that normalizer and of the centralizer normalize the full
commutator, by the direct ambient-Sylow Baumann argument. Subnormality in
the whole centralizer remains a separate source step: normalization by its
two-core does not establish it.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, the
nontrivial mixed-subgroup application of (5.2).
-/
namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

@[expose] public def mixedSubgroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) : Subgroup G :=
  let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  ⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
    ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆

@[expose] public noncomputable def extractedFullCommutator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) : Subgroup G :=
  ⁅twoResidualIn (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom),baumannIn T⁆

public theorem normalized_pair_centralizes_mixed
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) :
    mixedSubgroup ctx first second config ≤ ZAt ctx.Γ ctx.criticalPath.a ∧
      first.E.map (MulAut.conj config.g⁻¹).toMonoidHom ⊔
        second.E.map (MulAut.conj config.g⁻¹).toMonoidHom ≤
          Subgroup.centralizer (mixedSubgroup ctx first second config : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hbLocal : 1 < cp.length := hb
  let c := MulAut.conj config.g⁻¹
  let m0 := Γ.act first.extraction.x⁻¹ first.l
  let n0 := Γ.act second.extraction.x⁻¹ second.l
  let m := Γ.act config.g m0
  let d := Γ.act config.g cp.a'
  let r := Γ.act config.g second.l
  let V := VAt Γ cp.firstStep
  let E1 := first.E.map c.toMonoidHom
  let E2 := second.E.map c.toMonoidHom
  let R0 := (⁅ZAt Γ cp.a ⊓ GAt Γ m,ZAt Γ m ⊓ GAt Γ cp.a⁆ : Subgroup G)
  let Rold := (⁅ZAt Γ n0 ⊓ GAt Γ m0,ZAt Γ m0 ⊓ GAt Γ n0⁆ : Subgroup G)
  have hZnmap : (ZAt Γ n0).map c.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ n0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act,config.maps_new_vertex]
  have hGnmap : (GAt Γ n0).map c.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ n0) config.g⁻¹ = _
    rw [← stabilizer_act,config.maps_new_vertex]
  have hZmmap : (ZAt Γ m0).map c.toMonoidHom = ZAt Γ m := by
    change (z Γ m0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hGmmap : (GAt Γ m0).map c.toMonoidHom = GAt Γ m := by
    change conjugateBy (stabilizer Γ m0) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hRmap : Rold.map c.toMonoidHom = R0 := by
    rw [show Rold = ⁅ZAt Γ n0 ⊓ GAt Γ m0,ZAt Γ m0 ⊓ GAt Γ n0⁆ from rfl,
      Subgroup.map_commutator,Subgroup.map_inf _ _ _ c.injective,
      Subgroup.map_inf _ _ _ c.injective,hZnmap,hGnmap,hZmmap,hGmmap]
  have hpair := pair_center_commutator ctx e hb hlarge first second
  have hRoldZn : Rold ≤ ZAt Γ n0 :=
    hpair.1.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hR0Za : R0 ≤ ZAt Γ cp.a := by
    rw [← hRmap,← hZnmap]
    exact Subgroup.map_mono hRoldZn
  have hEpair : E1 ⊔ E2 ≤ Subgroup.centralizer (R0 : Set G) := by
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hpair.2
    have hm := congrArg (Subgroup.map c.toMonoidHom) hc
    rw [Subgroup.map_commutator,Subgroup.map_sup,Subgroup.map_bot,hRmap] at hm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hm
  exact ⟨hR0Za,hEpair⟩

/-- All established inputs to the remaining nontrivial centralizer step. -/
public structure MixedCentralizerData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) : Prop where
  nontrivial : mixedSubgroup ctx first second config ≠ ⊥
  two_group : IsPGroup 2 (mixedSubgroup ctx first second config)
  fixed_intersection : mixedSubgroup ctx first second config ⊓
    Subgroup.centralizer (baumannIn T : Set G) = mixedSubgroup ctx first second config
  pair_centralizes : first.E.map (MulAut.conj config.g⁻¹).toMonoidHom ⊔
    second.E.map (MulAut.conj config.g⁻¹).toMonoidHom ≤
      Subgroup.centralizer (mixedSubgroup ctx first second config : Set G)
  full : extractedFullCommutator ctx first second config =
    ⁅extractedFullCommutator ctx first second config,baumannIn T⁆
  three_quotient : IsPGroup 3 ((extractedFullCommutator ctx first second config) ⧸
    pCore 2 (extractedFullCommutator ctx first second config))
  centralizer_contains : baumannIn T ⊔ extractedFullCommutator ctx first second config ≤
    Subgroup.centralizer (mixedSubgroup ctx first second config : Set G)
  genuine_two_local : IsTwoLocal (Subgroup.normalizer
    (mixedSubgroup ctx first second config : Set G))
  normalizer_core_normalizes : twoCoreIn (Subgroup.normalizer
    (mixedSubgroup ctx first second config : Set G)) ≤
      Subgroup.normalizer (extractedFullCommutator ctx first second config : Set G)
  centralizer_core_normalizes : twoCoreIn (Subgroup.centralizer
    (mixedSubgroup ctx first second config : Set G)) ≤
      Subgroup.normalizer (extractedFullCommutator ctx first second config : Set G)

public theorem mixed_centralizer_data
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (enext : ((stabilizer ctx.Γ ctx.criticalPath.firstStep) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.firstStep)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (hBaumann : baumannIn T ≤ QAt ctx.Γ ctx.criticalPath.a)
    (S : Sylow 2 G) (hS : T = (S : Subgroup G))
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) : MixedCentralizerData ctx first second config := by
  let R := mixedSubgroup ctx first second config
  let D := twoResidualIn (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom)
  let F := extractedFullCommutator ctx first second config
  let C := Subgroup.centralizer (R : Set G)
  let N := Subgroup.normalizer (R : Set G)
  have hpair := normalized_pair_centralizes_mixed ctx e hb hlarge first second config
  have hne : R ≠ ⊥ := mixed_commutator_ne_bot ctx e hb hlarge first second config
  have hZtwo : IsPGroup 2 (ZAt ctx.Γ ctx.criticalPath.a) := by
    let := z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
    exact IsElementaryAbelian.isPGroup 2 _
  have htwo : IsPGroup 2 R := hZtwo.to_le hpair.1
  have hRB : R ≤ Subgroup.centralizer (baumannIn T : Set G) := by
    apply hpair.1.trans
    apply Subgroup.le_centralizer_iff.mpr
    have hc := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer
    exact hBaumann.trans (hc.symm.le.trans inf_le_right)
  have hBC : baumannIn T ≤ C := Subgroup.le_centralizer_iff.mp hRB
  have hDC : D ≤ C := (Subgroup.map_subtype_le _).trans (le_sup_right.trans hpair.2)
  have hFC : F ≤ C := (Subgroup.commutator_le_sup D (baumannIn T)).trans (sup_le hDC hBC)
  have hDF : D ≤ F := config.residual_baumann
  have hfull : F = ⁅F,baumannIn T⁆ :=
    le_antisymm (Subgroup.commutator_mono hDF le_rfl)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.normalizer_commutator_ge_right D (baumannIn T)))
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hnorm (M : Subgroup G) (hFM : F ≤ M) (hBM : baumannIn T ≤ M) :
      twoCoreIn M ≤ Subgroup.normalizer (F : Set G) := by
    rw [hS] at hBM hfull
    exact twoCore_normalizes_full_baumann S F M hFM hBM hfull
  exact ⟨hne,htwo,inf_eq_left.mpr hRB,hpair.2,hfull,
    residual_baumann_quotient_three ctx enext first second config,
    sup_le hBC hFC,⟨R,hne,htwo,rfl⟩,
    hnorm N (hFC.trans hCN) (hBC.trans hCN),hnorm C hFC hBC⟩

end Stellmacher.SectionNine.LocalLonger

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix Stellmacher.SectionNine
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The actual Goldschmidt triple supplies every retained input to the
nontrivial mixed-centralizer step, including the original ambient Sylow. -/
public theorem IsGoldschmidtTriple.exists_nontrivial_mixed_centralizer_data
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
      ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
    ∃ first : LocalLonger.FirstConfigurationData ctx,
      ∃ second : LocalLonger.SecondConfigurationData ctx first,
        ∃ config : LocalLonger.NormalizedGeometry ctx first second,
          LocalLonger.MixedCentralizerData ctx first second config := by
  classical
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  obtain ⟨first,second,⟨config⟩⟩ := h.exists_normalized_extractions_of_large_center
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  have he : Nonempty (((stabilizer Γ cp.a) ⧸ pCore 2 (stabilizer Γ cp.a)) ≃*
      Equiv.Perm (Fin 3)) ∧
      Nonempty (((stabilizer Γ cp.firstStep) ⧸ pCore 2 (stabilizer Γ cp.firstStep)) ≃*
      Equiv.Perm (Fin 3)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [show stabilizer Γ cp.a = G₁ from he.1,
        show stabilizer Γ cp.firstStep = G₂ from he.2]
      exact ⟨h.quotient_left,h.quotient_right⟩
    · rw [show stabilizer Γ cp.a = G₂ from he.1,
        show stabilizer Γ cp.firstStep = G₁ from he.2]
      exact ⟨h.quotient_right,h.quotient_left⟩
  have hb := h.critical_length_gt_one_of_commuting hcore hgood₁ hgood₂ Γ cp hcomm
  have hB := h.critical_baumann_le_initial_core_of_large_center
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  obtain ⟨S,hS⟩ := h.intersection_sylow
  exact ⟨first,second,config,LocalLonger.mixed_centralizer_data ctx he.1.some he.2.some
    hb hlarge hB S hS first second config⟩

end CFSG.Quasithin.ChapterF
