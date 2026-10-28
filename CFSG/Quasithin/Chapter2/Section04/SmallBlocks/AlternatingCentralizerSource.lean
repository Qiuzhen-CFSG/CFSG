module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingBorelSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
public import CFSG.Quasithin.ChapterC.Section06.SmallBlockCenter
/-!
# The centralizer factor in the original single A₅ branch

An offender supplies an odd transposition in the image of J(S). Together
with the residual A₅ image and the source core contained in J(S), this
gives H = L J(S). The original normalizer barrier puts C_T(L) inside S.
The C.6 fixed-plane calculation then makes this factor central in H and
bounds its order by four.

These are the literal centralizer and generation facts used before the
extraspecial calculation strengthens the bound in 2.4.29.
Source: Aschbacher–Smith, C.5.4(3), 2.4.27 and 2.4.29, pp.155,544–545.
-/

public section
open Subgroup Stellmacher BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
open ChapterC.Section05.BlockAnalysis.AlternatingSetup ChapterB.Offenders
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_thompson_generation
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    d.H = d.block.map d.H.subtype ⊔
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  let U := (blockU d.block).map d.block.subtype
  let J := elementaryAbelianMaxJ (d.S : Subgroup d.H)
  let N := d.block ⊔ J
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : U.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  let : IsElementaryAbelian 2 U := by
    let := hAi.2.1.elementary
    exact IsElementaryAbelian.map d.block.subtype
  have hU : U.map d.H.subtype = sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hUS : U ≤ d.S := (le_centralizer U).trans
    ((hC.symm.trans hker).le.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hJ : ¬ J ≤ centralizer (U : Set d.H) := by
    intro hh
    have hm := map_mono (f := d.H.subtype) hh
    rw [←elementaryAbelianMaxJ_map_injective d.H.subtype d.H.subtype_injective] at hm
    exact thompson_moves_of_commutator (d.block.map d.H.subtype) _ hA.2.1 d.moved
      (hm.trans (by rw [←hU]; exact map_centralizer_le_centralizer_image _ _))
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.S : Subgroup d.H), A.map q ≠ ⊥ := by
    by_contra! hall
    apply hJ
    rw [←hC]
    exact sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hmax,hne⟩ := hex
  obtain ⟨m,hm,_,a,ha⟩ := max_image_caseA U q hC e he d.S A hUS hmax hne
  let t := (MulAut.conj a) (pairSwap 5 0)
  have ht : t.IsSwap :=
    ⟨a 0,a 1,a.injective.ne (by decide),Equiv.symm_trans_swap_trans (0 : Fin 5) 1 a⟩
  have htN : t ∈ N.map q := by
    apply map_mono ((le_sSup hmax).trans le_sup_right)
    rw [ha]
    exact mem_map_of_mem _ (pairSwap_mem 0 hm)
  have hAN : alternatingGroup (Fin 5) ≤ N.map q := by
    rw [←(d.single_alternating_residual_action hsingle q hq hker).1]
    exact map_mono le_sup_left
  have himage : N.map q = ⊤ := by
    have hdvd := index_dvd_of_le hAN
    rw [alternatingGroup.index_eq_two] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hi | hi
    · exact index_eq_one.mp hi
    · rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi,
        Equiv.Perm.mem_alternatingGroup,ht.sign_eq] at htN
      exact (by decide : (-1 : ℤˣ) ≠ 1) htN |>.elim
  have hkerJ : q.ker ≤ J := by
    apply (map_le_map_iff_of_injective d.H.subtype_injective).mp
    rw [hker]
    change twoCore d.H ≤ J.map d.H.subtype
    rw [←elementaryAbelianMaxJ_map_injective d.H.subtype d.H.subtype_injective]
    exact le_sSup (d.core_source hG T hST).2.2
  have hN : N = ⊤ := by
    have hh := comap_map_eq_self (hkerJ.trans (show J ≤ N from le_sup_right))
    rw [himage,comap_top] at hh
    exact hh.symm
  have hh := congrArg (map d.H.subtype) hN
  rw [Subgroup.map_sup,←elementaryAbelianMaxJ_map_injective d.H.subtype
    d.H.subtype_injective,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh.symm

theorem MinimalBlockSetup.single_block_sylow_centralizer
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block) :
    (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) =
      (d.S : Subgroup d.H).map d.H.subtype ⊓
        centralizer (d.block.map d.H.subtype : Set G) := by
  let U := d.U0.map d.H.subtype
  have hU : U ≠ ⊥ := fun h => d.U0_ne_bot
    ((map_eq_bot_iff_of_injective _ d.H.subtype_injective).mp h)
  have hUS : U ≤ (d.S : Subgroup d.H).map d.H.subtype :=
    map_mono (d.U0_le_core.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hUL : U ≤ d.block.map d.H.subtype :=
    map_mono (hsingle ▸ d.U0_le_L0)
  have hUn : (U.subgroupOf d.H).Normal := by
    have he : U.subgroupOf d.H = d.U0 :=
      comap_map_eq_self_of_injective d.H.subtype_injective _
    rw [he]
    exact d.U0_normal
  have hb := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST U hU hUS hUn
  apply le_antisymm
  · exact le_inf ((inf_le_inf le_rfl ((centralizer_le hUL).trans
        (Subgroup.centralizer_le_normalizer _))).trans hb.le) inf_le_right
  · exact inf_le_inf hST le_rfl

theorem MinimalBlockSetup.single_alternating_centralizer_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    D ≤ centralizer (d.H : Set G) ∧ Nat.card D ≤ 4 := by
  have hi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle hA
    (T : Subgroup G) hST.le le_rfl hi
  obtain ⟨hD,_,hcard⟩ := ChapterC.Section06.alternating_block_center_index_from_original c h hi x hx hnc
  rw [d.single_block_sylow_centralizer T hST.le hsingle]
  refine ⟨?_,hcard⟩
  have hDC : (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.block.map d.H.subtype : Set G) ≤
      centralizer (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) := by
    intro a ha
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hD ha)).2.2
  conv_rhs => rw [d.single_alternating_thompson_generation hG T hST hsingle hA]
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp hDC)

end CFSG.Quasithin.Chapter2
