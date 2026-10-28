module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOpposedKernelNormalizer

/-!
# The original component cannot normalize the opposed kernel image

If the actual B=q(L) normalized A=q(N^g), its full preimage N join N^g
would be L-normal. The original exchanger also normalizes this nontrivial
two-group, and the original Y/T uniqueness forces L inside M. Thus this
specific Sylow-normal kernel image is not B-normal. The proof retains
both point kernels rather than replacing them by finite model radicals.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The actual smaller component fails to normalize the actual opposite kernel image. -/
theorem binary_three_source_binary_opposed_kernel_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let A := ((N.conjBy g).subgroupOf C).map q
    ¬ B ≤ normalizer A := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Ng := N.conjBy g
  let q := QuotientGroup.mk' (pCore 2 C)
  let A := (Ng.subgroupOf C).map q
  let J := N ⊔ Ng
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hSN : d.S ≤ normalizer N := (le_sup_right.trans hLS).trans hCN
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer d.S :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSg : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hNgS : Ng ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNS
    rwa [hSg] at hh
  have hSNg : d.S ≤ normalizer Ng := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSN
    rwa [hSg,map_equiv_normalizer_eq] at hh
  have hSJ : d.S ≤ normalizer J :=
    (le_inf hSN hSNg).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNgC : Ng ≤ C := hNgS.trans (le_sup_right.trans hLS)
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hJC : J ≤ C := sup_le hNC hNgC
  have hNsub : N.subgroupOf C = pCore 2 C :=
    comap_map_eq_self_of_injective C.subtype_injective (pCore 2 C)
  have hpre : A.comap q = J.subgroupOf C := by
    rw [comap_map_eq,QuotientGroup.ker_mk',←hNsub,←subgroupOf_sup hNgC hNC,sup_comm]
  change ¬ (c.L.subgroupOf C).map q ≤ normalizer A
  intro hBA
  have hLc : c.L.subgroupOf C ≤ normalizer (J.subgroupOf C) := by
    have hh := map_le_iff_le_comap.mp hBA
    rw [comap_normalizer_eq_of_surjective A (QuotientGroup.mk'_surjective _),hpre] at hh
    exact hh
  have hLJ : c.L ≤ normalizer J := by
    rw [←subgroupOf_normalizer_eq hJC] at hLc
    intro l hl
    exact hLc (show (⟨l,(le_sup_left.trans hLS) hl⟩ : C) ∈ c.L.subgroupOf C from hl)
  have hXne := (binary_three_source_binary_kernel_exchange
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm g hgT hgS).2.1
  have hNne : N ≠ ⊥ := by
    intro hz
    apply hXne
    change N ⊓ Ng = ⊥
    exact le_bot_iff.mp (inf_le_left.trans hz.le)
  have hY := Y_le_component_sylow d c.L hg.generation g hgT (hg.exchange g hgT hgS)
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact outside_conjugatePair_contradiction d c.outside hNne hNS g hgT hgS hi hSN
    (sup_le hLJ hSJ) hY hunique

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
