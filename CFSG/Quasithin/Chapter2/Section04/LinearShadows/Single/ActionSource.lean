module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NaturalConfiguration
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.InternalSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport

/-!
# The actual Thompson decomposition and Borel torus action

The original C.5 configuration and its internal action are constructed
from the full simple-QTKE hypotheses. The checked core formula then gives
J(S)=(S∩L)C_S(L), with C_S(L) central in J(S). The original Borel torus D
normalizes each factor, and S normalizes J(S)D because it normalizes both
J(S) and M∩L=(S∩L)D.

All subgroups are the literal selected source subgroups; no parabolic
model or independent marking is assumed. The later joint Hall torus and
fixed-centralizer argument remain separate.

Source: Aschbacher–Smith 2.4.8(5), printed p.530, first two paragraphs.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem source_thompson_decomposition_of_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (M₀ : Subgroup G)
    (c : ChapterC.Section05.BlockAnalysis.OriginalHypotheses d.H M₀
      (d.block.map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype)
      ((d.S : Subgroup d.H).map d.H.subtype))
    {F : Type*} [Field F]
    (h : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype) (d.block.map d.H.subtype) F)
    (hi : h.coordinates.IsInternal)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    R = (S ⊓ L) ⊔ (S ⊓ centralizer (L : Set G)) ∧ R ⊓ L = S ⊓ L ∧
      S ⊓ centralizer (L : Set G) ≤ centralizer (R : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := S ⊓ centralizer (L : Set G)
  have hfam := ChapterC.Section06.rankOne_family_from_original c h hindex x hx hnc
  have hcl := d.single_block_closures (c.R_le_H.trans c.normalizes_residual)
  have hq := d.core_source hG T hST
  have hQ : twoCore d.H = RankOne.U L ⊔ C := by
    simpa only [hsingle,hcl.2,sourceModule,RankOne.U,S,L,C] using hq.2.1
  have hker : RankOne.S S ⊓ centralizer (RankOne.U L : Set G) = RankOne.U L ⊔ C :=
    h.core.symm.trans (hfam.1.trans hQ)
  have hR : R = (S ⊓ L) ⊔ C := by
    have he := h.internal_decomposition hi hker
    rw [h.source_sylow_intersection c.R_twoGroup] at he
    exact hfam.2.1.symm.trans he
  have hRL : R ⊓ L = S ⊓ L := by
    exact (congrArg (fun A : Subgroup G => A ⊓ L) hfam.2.1.symm).trans
      (h.source_sylow_intersection c.R_twoGroup)
  have hCQ : C ≤ twoCore d.H := le_sup_right.trans_eq hQ.symm
  let : IsElementaryAbelian 2 (twoCore d.H) := hq.2.2.2.1
  have hCC : C ≤ centralizer (C : Set G) := hCQ.trans
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hCQ))
  refine ⟨hR,hRL,le_centralizer_iff.mp ?_⟩
  change R ≤ centralizer (C : Set G)
  rw [hR]
  exact sup_le (inf_le_right.trans (le_centralizer_iff.mp inf_le_right)) hCC


theorem source_thompson_decomposition
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    R = (S ⊓ L) ⊔ (S ⊓ centralizer (L : Set G)) ∧ R ⊓ L = S ⊓ L ∧
      S ⊓ centralizer (L : Set G) ≤ centralizer (R : Set G) := by
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨M₀,hSM,hMT,hindex⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,hi,x,hx,hnc⟩ := d.single_natural_configuration hG T hST.le
    hsingle hK M₀ hSM hMT hindex
  exact source_thompson_decomposition_of_configuration d hG T hST hsingle M₀ c h hi
    hindex x hx hnc

end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem borel_normalizations_of_decomposition
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (P : Sylow 2 d.block) (D : Subgroup d.block)
    (hP : (P : Subgroup d.block).map d.block.subtype = (d.S : Subgroup d.H) ⊓ d.block)
    (hDN : D ≤ normalizer (P : Set d.block))
    (hgen : (P : Subgroup d.block) ⊔ D = (M.subgroupOf d.H).subgroupOf d.block)
    (hdec : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) =
      ((d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype) ⊔
      ((d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.block.map d.H.subtype : Set G))) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let D₀ := D.map (d.H.subtype.comp d.block.subtype)
    D₀ ≤ normalizer (R : Set G) ∧ S ≤ normalizer ((R ⊔ D₀ : Subgroup G) : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := S ⊓ centralizer (L : Set G)
  let f := d.H.subtype.comp d.block.subtype
  let D₀ := D.map f
  let B := (M.subgroupOf d.H).subgroupOf d.block
  have hrange : f.range = L := by
    dsimp only [f]
    rw [MonoidHom.range_comp,range_subtype]
  have hP' : (P : Subgroup d.block).map f = S ⊓ L := by
    dsimp only [f]
    rw [←map_map,hP,map_inf _ _ _ d.H.subtype_injective]
  have hD₀L : D₀ ≤ L := (map_le_range f D).trans_eq hrange
  have hDP : D₀ ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [←hP']
    exact (map_mono (show D ≤ normalizer ((P : Subgroup d.block) : Set d.block) from hDN)).trans
      ((P : Subgroup d.block).le_normalizer_map f)
  have hDC : D₀ ≤ centralizer (C : Set G) :=
    hD₀L.trans (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right))
  have hDR : D₀ ≤ normalizer (R : Set G) := by
    change D₀ ≤ normalizer (Stellmacher.elementaryAbelianMaxJ S : Set G)
    change R = (S ⊓ L) ⊔ C at hdec
    rw [show Stellmacher.elementaryAbelianMaxJ S = (S ⊓ L) ⊔ C from hdec]
    exact (le_inf hDP (hDC.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hB : B.map f = M ⊓ L := by
    change (M.comap f).map f = M ⊓ L
    rw [map_comap_eq,hrange,inf_comm]
  have hPD : (S ⊓ L) ⊔ D₀ = M ⊓ L := by
    have he := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup,hP',hB] at he
    exact he
  have hSL : S ≤ normalizer (L : Set G) := by
    let := d.L0_normal
    have hn : (d.S : Subgroup d.H) ≤ normalizer (d.L0 : Set d.H) := le_normalizer_of_normal
    have hn' := (map_mono (f := d.H.subtype) hn).trans (d.L0.le_normalizer_map d.H.subtype)
    simpa only [hsingle] using hn'
  have hSM : S ≤ M := d.full_pair.1.1.2.1
  have hSB : S ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    (le_inf (hSM.trans M.le_normalizer) hSL).trans inf_normalizer_le_normalizer_inf
  have hSR : S ≤ normalizer (R : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ S).map (MulAut.conj s).toMonoidHom = _
    rw [←Stellmacher.elementaryAbelianMaxJ_map_equiv,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)]
  have hPR : S ⊓ L ≤ R := le_sup_left.trans_eq hdec.symm
  have hRD : R ⊔ D₀ = R ⊔ (M ⊓ L) := by
    rw [←hPD,←sup_assoc,sup_eq_left.mpr hPR]
  refine ⟨hDR,?_⟩
  change S ≤ normalizer ((R ⊔ D₀ : Subgroup G) : Set G)
  rw [hRD]
  exact (le_inf hSR hSB).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The original cyclic complement normalizes the actual Thompson group,
and the original Sylow subgroup normalizes their product. -/
theorem source_torus_normalizations
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (P : Sylow 2 d.block) (D : Subgroup d.block)
    (hP : (P : Subgroup d.block).map d.block.subtype = (d.S : Subgroup d.H) ⊓ d.block)
    (hDN : D ≤ normalizer (P : Set d.block))
    (hgen : (P : Subgroup d.block) ⊔ D = (M.subgroupOf d.H).subgroupOf d.block) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let D₀ := D.map (d.H.subtype.comp d.block.subtype)
    D₀ ≤ normalizer (R : Set G) ∧ S ≤ normalizer ((R ⊔ D₀ : Subgroup G) : Set G) :=
  borel_normalizations_of_decomposition d hsingle P D hP hDN hgen
    (source_thompson_decomposition d hG T hST hsingle hL).1

/-- Source 2.4.8(5), through the construction and normalization of RD,
with the selected Hall complement and all preceding action data constructed. -/
theorem source_borel_torus_action
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n) :
    ∃ (P : Sylow 2 d.block) (D : Subgroup d.block),
      (P : Subgroup d.block).map d.block.subtype = (d.S : Subgroup d.H) ⊓ d.block ∧
      normalizer (P : Set d.block) = (M.subgroupOf d.H).subgroupOf d.block ∧
      D ≤ (M.subgroupOf d.H).subgroupOf d.block ∧ Odd (Nat.card D) ∧
      Disjoint (P : Subgroup d.block) D ∧
      (P : Subgroup d.block) ⊔ D = (M.subgroupOf d.H).subgroupOf d.block ∧
      IsHallSubgroup OddHall.oddPrimes (D.subgroupOf ((M.subgroupOf d.H).subgroupOf d.block)) ∧
      IsCyclic D ∧ Nat.card D = 2^n - 1 ∧ D ≠ ⊥ ∧
      let S := (d.S : Subgroup d.H).map d.H.subtype
      let R := Stellmacher.elementaryAbelianMaxJ S
      let D₀ := D.map (d.H.subtype.comp d.block.subtype)
      D₀ ≤ normalizer (R : Set G) ∧ S ≤ normalizer ((R ⊔ D₀ : Subgroup G) : Set G) := by
  obtain ⟨P,D,hP,hB,hDB,hodd,hd,hgen,hHall,hcyc,hcard,hne⟩ := source_borel_torus d hsingle hL
  have hDN : D ≤ normalizer (P : Set d.block) := hB.symm ▸ hDB
  exact ⟨P,D,hP,hB,hDB,hodd,hd,hgen,hHall,hcyc,hcard,hne,
    source_torus_normalizations d hG T hST hsingle hL P D hP hDN hgen⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
