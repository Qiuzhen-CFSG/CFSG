module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedSource
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.Commutator.CentralizingComplement
/-!
# The derived center and torus commutators of the actual block Sylow

The original C.5 configuration identifies the fixed module subgroup with
its commutator under an escaping conjugate. Since O₂(L)=U and
R=(S∩L)C_S(L), this puts Z(S∩L) in (S∩L)′, including the full central
covering layer. The natural-block odd fixed-point and Sylow-transfer
calculation then gives [S∩L,D]=S∩L and [R,D]=S∩L for the actual torus.

Source: Aschbacher–Smith C.5.6(2),(3) and 2.4.8(5), printed pp.156,530.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_sylow_center_le_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n) :
    let P := (d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype
    P ⊓ centralizer (P : Set G) ≤ ⁅P,P⁆ := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let P := S ⊓ L
  let C := S ⊓ centralizer (L : Set G)
  let U := RankOne.U L
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,hint,x,hx,hnc⟩ := d.single_natural_configuration hG T hST.le
    hsingle hK M₀ hSM hMT hi
  have hf := ChapterC.Section06.rankOne_family_from_original c h hi x hx hnc
  have hSR : RankOne.S S = R := hf.2.1
  have hxS : x ∈ normalizer (S : Set G) := by
    have hnormal : (S.subgroupOf M₀).Normal := normal_of_index_eq_two hi
    exact (normal_subgroupOf_iff_le_normalizer hSM).mp hnormal hx
  have hUP : U ≤ P := le_inf (h.module_le.trans inf_le_left) (map_subtype_le _)
  have hUR : U ≤ R := h.module_le.trans_eq hSR
  have hd := source_thompson_decomposition d hG T hST hsingle hL
  change R = P ⊔ C ∧ R ⊓ L = P ∧ C ≤ centralizer (R : Set G) at hd
  have hcore : L.pCoreIn 2 = U := congrArg (Subgroup.map L.subtype)
    (source_block_core_eq_module d hG T hST hsingle)
  have hCU : C ≤ centralizer (U : Set G) := hd.2.2.trans (centralizer_le hUR)
  have hPU : P ≤ normalizer (U : Set G) :=
    inf_le_right.trans (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image
      L (ChapterC.blockU L)))
  have hcomm : ⁅U,R⁆ ≤ ⁅P,P⁆ := by
    rw [←commutator_eq_of_centralizing_sup ((sup_comm C P).trans hd.1.symm) hCU hPU]
    exact commutator_mono hUP le_rfl
  change P ⊓ centralizer (P : Set G) ≤ ⁅P,P⁆
  rintro z ⟨hzP,hzC⟩
  have hzR : z ∈ R := hd.1.symm ▸ mem_sup_left hzP
  have hzCR : z ∈ centralizer (R : Set G) := by
    rw [hd.1,sup_eq_closure,centralizer_closure]
    intro y hy
    rcases hy with hy | hy
    · exact mem_centralizer_iff.mp hzC y hy
    · exact ((mem_centralizer_iff.mp (hd.2.2 hy)) z hzR).symm
  have hzQ : z ∈ twoCore d.H := by
    have hz : z ∈ RankOne.Q S L := h.core.symm ▸
      (show z ∈ RankOne.S S ⊓ centralizer (U : Set G) from
        ⟨hSR.symm ▸ hzR,centralizer_le hUR hzCR⟩)
    change z ∈ d.H.pCoreIn 2
    exact hf.1 ▸ hz
  have hzU : z ∈ U := hcore ▸ inf_pCoreIn_le_of_le 2 (map_subtype_le d.block) ⟨hzP.2,hzQ⟩
  have hvR : (U.map (MulAut.conj x⁻¹).toMonoidHom) ≤ R :=
    (h.conjugate_le hxS).trans_eq hSR
  have hzfix : z ∈ U ⊓ centralizer (U.map (MulAut.conj x⁻¹).toMonoidHom : Set G) :=
    ⟨hzU,centralizer_le hvR hzCR⟩
  have hzcomm : z ∈ ⁅U,U.map (MulAut.conj x⁻¹).toMonoidHom⁆ :=
    (h.commutator_eq_fixed hxS hnc).1.symm ▸ hzfix
  exact hcomm ((commutator_mono le_rfl hvR) hzcomm)


theorem source_sylow_odd_commutator
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥)
    (hDR : D ≤ normalizer
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) :
    let P := (d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype
    ⁅P,D⁆ = P := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let P := S ⊓ L
  let R := Stellmacher.elementaryAbelianMaxJ S
  let e := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  have hK := hL.of_mulEquiv e
  obtain ⟨P₀,hP₀,_⟩ := source_intersection_borel d hsingle hL
  let P' : Sylow 2 L := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P' : Subgroup L).map L.subtype = P := by
    change ((P₀ : Subgroup d.block).map e.toMonoidHom).map L.subtype = _
    rw [Subgroup.map_map]
    have hf : L.subtype.comp e.toMonoidHom = d.H.subtype.comp d.block.subtype := rfl
    rw [hf,←Subgroup.map_map,hP₀,map_inf _ _ _ d.H.subtype_injective]
  have hd := source_thompson_decomposition d hG T hST hsingle hL
  have hDP : D ≤ normalizer (P : Set G) := by
    have hp : R ⊓ L = P := hd.2.1
    rw [←hp]
    exact (le_inf hDR (hDL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hNP : normalizer (P' : Set L) = (normalizer (P : Set G)).subgroupOf L := by
    rw [←hP',subgroupOf_normalizer_eq (map_subtype_le (P' : Subgroup L))]
    simp only [subgroupOf,comap_map_eq_self_of_injective L.subtype_injective,P'.coe_coe]
  have hn : D.subgroupOf L ≤ normalizer (P' : Set L) := by
    rw [hNP]
    exact subgroupOf_mono L hDP
  have ho : Odd (Nat.card (D.subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have hne : D.subgroupOf L ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [map_subgroupOf_eq_of_le hDL,Subgroup.map_bot] at hh
    exact hD hh
  have hc := hK.sylow_odd_commutator_eq (source_block_core_eq_module d hG T hST hsingle)
    P' (D.subgroupOf L) ho hne hn
  have hm := congrArg (Subgroup.map L.subtype) hc
  rwa [map_commutator,hP',map_subgroupOf_eq_of_le hDL] at hm


theorem source_thompson_odd_commutator
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥)
    (hDR : D ≤ normalizer
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    ⁅Stellmacher.elementaryAbelianMaxJ S,D⁆ = S ⊓ d.block.map d.H.subtype := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let P := S ⊓ L
  let C := S ⊓ centralizer (L : Set G)
  have hd := source_thompson_decomposition d hG T hST hsingle hL
  change R = P ⊔ C ∧ R ⊓ L = P ∧ C ≤ centralizer (R : Set G) at hd
  have hPR : P ≤ R := le_sup_left.trans_eq hd.1.symm
  have hCR : C ≤ R := le_sup_right.trans_eq hd.1.symm
  have hDP : D ≤ normalizer (P : Set G) := by
    rw [←hd.2.1]
    exact (le_inf hDR (hDL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hRP : R ≤ normalizer (P : Set G) := by
    rw [hd.1]
    exact sup_le P.le_normalizer ((hd.2.2.trans (centralizer_le hPR)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hCD : ⁅C,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le hDL))
  have hupper : ⁅R,D⁆ ≤ P := by
    have hpre : R ≤ commutatorPreimage R D P := hd.1.le.trans (sup_le
      (le_commutatorPreimage hPR (le_normalizer_iff_commutator_le_left.mp hDP))
      (le_commutatorPreimage hCR (by rw [hCD];exact bot_le)))
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le R D P hRP)
  have hPD : ⁅P,D⁆ = P := source_sylow_odd_commutator d hG T hST hsingle hL D hDL hodd hD hDR
  exact le_antisymm hupper (hPD.ge.trans (commutator_mono hPR le_rfl))

end CFSG.Quasithin.Chapter2.LinearShadows.Single

