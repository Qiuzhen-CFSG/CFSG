module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingKernel
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Ambient kernel control for quotient order eighteen

Write C=C_G(U), D=C_G(L), and M=N_G(L). The original block is
O²(M), so a conjugate of L contained in M equals L. If T centralizes C,
ambient uniqueness therefore makes D disjoint from every conjugate by an
escaping element of H. Both subgroups lie in C=Z(U)D, giving |D|≤2.
The residual action on C, then of order at most four and fixing the original
central involution, is trivial. Since T normalizes D and H=O²(H)T,
uniqueness forces D=1.

When |H/O₂(H)|=18, the exact kernel cardinality and Sylow counting give
T=(T∩L)D, which centralizes C. This excludes the selected swapping action
in the entire order-eighteen branch, and supplies its genuine recognition
configuration. The unconditional source consumer now leaves only quotient
order36, with elementary D of rank at least two and nontrivial T-action on C.
This remaining swapping case is NOT excluded by the present family.

The remaining ambient argument and final source assembly belong to
qt-d-14414-g2-source. Universal I.4.5 remains qt-i45-g2-recognition;
EarlierSetupResults retains its original producers, and the final 14.4.14
assembly belongs to qt-d-14414-source.

Source: Aschbacher–Smith, proof of 14.4.4–5, printed pp.1007–1008.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)

include d earlier hq chosen previous hne hZ hcard

/-- The original block is the actual two-residual of its ambient normalizer. -/
theorem source_normalizer_residual :
    (pResidual 2 (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype = L := by
  let H := higherRankHypothesis d earlier hq chosen
  let M := normalizer (L : Set G)
  have hLM : L ≤ M := L.le_normalizer
  have hTM : (T : Subgroup G) ≤ M := H.sylow_normalizes previous.structural
  let : (L.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hLM).mpr le_rfl
  have hp : IsPPerfect 2 (L.subgroupOf M) :=
    ((pResidual_eq_top_iff 2 L).mp H.residual).of_surjective
      (subgroupOfEquivOfLe hLM).symm.toMonoidHom (subgroupOfEquivOfLe hLM).symm.surjective
  have hsup : L.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup hLM hTM, ← source_normalizer_eq_join d earlier hq chosen previous
      F hne hZ hcard]
    exact subgroupOf_self _
  have he := pResidual_eq_of_isPPerfect_sup (L.subgroupOf M)
    ((T : Subgroup G).subgroupOf M) hp T.isPGroup'.comap_subtype hsup
  change (pResidual 2 M).map M.subtype = L
  rw [he,map_subgroupOf_eq_of_le hLM]

/-- A conjugate of L contained in its original normalizer equals L. -/
theorem source_mem_normalizer_of_conjugate_le (x : G)
    (hx : L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set G)) :
    x ∈ normalizer (L : Set G) := by
  let H := higherRankHypothesis d earlier hq chosen
  let M := normalizer (L : Set G)
  let f : L →* M := ((MulAut.conj x).toMonoidHom.comp L.subtype).codRestrict M
    (fun l => hx (mem_map_of_mem _ l.property))
  have hf := map_pResidual_le 2 f
  rw [H.residual] at hf
  have hle : L.map (MulAut.conj x).toMonoidHom ≤ L := by
    rintro _ ⟨l,hl,rfl⟩
    rw [← source_normalizer_residual d earlier hq chosen previous F hne hZ hcard]
    exact mem_map_of_mem M.subtype (hf (mem_map_of_mem f (mem_top (⟨l,hl⟩ : L))))
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])

/-- If T centralizes C_G(U), distinct escaping conjugates of C_G(L) are disjoint. -/
theorem source_block_centralizer_disjoint_conjugate
    (hTC : (T : Subgroup G) ≤ centralizer (centralizer (F.U : Set G) : Set G))
    (x : G) (hxM : x ∉ normalizer (L : Set G)) :
    Disjoint (centralizer (L : Set G))
      ((centralizer (L : Set G)).map (MulAut.conj x).toMonoidHom) := by
  let H := higherRankHypothesis d earlier hq chosen
  let D := centralizer (L : Set G)
  let C := centralizer (F.U : Set G)
  let D' := D.map (MulAut.conj x).toMonoidHom
  let E := D ⊓ D'
  have hUL := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).2
  have hDC : D ≤ C := centralizer_le hUL
  have hCT : C ≤ (T : Subgroup G) := (centralizer_le (le_conjugateSpanBy V F.H)).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hLN : L ≤ normalizer (E : Set G) :=
    (le_centralizer_iff.mp (show E ≤ centralizer (L : Set G) from inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (hTC.trans (centralizer_le (inf_le_left.trans hDC))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hL'N : L.map (MulAut.conj x).toMonoidHom ≤ normalizer (E : Set G) := by
    apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact (show E ≤ D' from inf_le_right).trans
      (map_centralizer_le_centralizer_image _ _)
  apply disjoint_iff.mpr
  change E = ⊥
  by_contra hE
  have hNM : normalizer (E : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
      (T.isPGroup'.to_le ((inf_le_left.trans hDC).trans hCT)) hE (sup_le hLN hTN)
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique previous.structural previous.uniqueness).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact hxM (source_mem_normalizer_of_conjugate_le d earlier hq chosen previous
    F hne hZ hcard x (hL'N.trans hNM))

/-- If the Sylow subgroup centralizes the core centralizer, the block centralizer
has order at most two. Ambient uniqueness is used at an escaping conjugate. -/
theorem source_block_centralizer_card_le_two_of_sylow_centralizes
    (hTC : (T : Subgroup G) ≤ centralizer (centralizer (F.U : Set G) : Set G)) :
    Nat.card (centralizer (L : Set G)) ≤ 2 := by
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨x,hxH,hxM⟩ := Set.not_subset.mp (H.flag_escape F previous.alternatives)
  let D := centralizer (L : Set G)
  let C := centralizer (F.U : Set G)
  let D' := D.map (MulAut.conj x).toMonoidHom
  let := source_core_centralizer_elementary d earlier hq chosen previous F hne hZ hcard
  have hDC : D ≤ C := centralizer_le (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).2
  have hCN : F.H ≤ normalizer (C : Set G) := (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_centralizer F.U)
  have hD'C : D' ≤ C := by
    apply (map_mono hDC).trans
    exact (mem_normalizer_iff_map_conj_eq.mp (hCN hxH)).le
  have hnorm : D' ≤ normalizer (D : Set G) :=
    ((hD'C.trans (le_centralizer C)).trans (centralizer_le hDC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis := source_block_centralizer_disjoint_conjugate d earlier hq chosen previous
    F hne hZ hcard hTC x hxM
  have hc := card_le_of_le (sup_le hDC hD'C)
  rw [card_sup_of_disjoint_of_normalizes D D' hdis hnorm,
    card_map_of_injective (MulAut.conj x).injective,
    (source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard).1] at hc
  have hp : 0 < Nat.card D := Nat.card_pos
  change Nat.card D ≤ 2
  nlinarith

/-- A block centralizer of order at most two is trivial. The residual action
on C_G(U), of order at most four, fixes the marked central involution. -/
theorem source_block_centralizer_eq_bot_of_card_le_two
    (hD : Nat.card (centralizer (L : Set G)) ≤ 2) : centralizer (L : Set G) = ⊥ := by
  classical
  by_contra hnD
  let := chosen.elementary
  let C := centralizer (F.U : Set G)
  let D := centralizer (L : Set G)
  have hDc : Nat.card D = 2 := by
    change Nat.card D ≤ 2 at hD
    have hp : 0 < Nat.card D := Nat.card_pos
    have hn : Nat.card D ≠ 1 := fun he => hnD (card_eq_one.mp he)
    omega
  have hCc : Nat.card C = 4 := by
    rw [(source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard).1,hDc]
  have hZC : F.ZU ≤ C := by
    change F.ZU ≤ centralizer (F.U : Set G)
    rw [source_core_centralizer_eq_center_join d earlier hq chosen previous F hne hZ hcard]
    exact le_sup_left
  have hZc : Nat.card F.ZU = 2 := by rw [hZ]; exact F.card 1 (by decide)
  let : Nontrivial F.ZU := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hh
    have hc : Nat.card F.ZU = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hh,inferInstance⟩
    omega
  obtain ⟨z,hz⟩ := exists_ne (1 : F.ZU)
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := by
    intro he
    exact hz (Subtype.ext (congrArg (fun c : C => (c : G)) he))
  have hHN : F.H ≤ normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer F.U)
  let f : F.H →* MulAut C := C.normalizerMonoidHom.comp (inclusion hHN)
  have hfix : ∀ a ∈ f.range, a zC = zC := by
    rintro _ ⟨a,rfl⟩
    apply Subtype.ext
    change (a : G)*(z : G)*(a : G)⁻¹ = z
    have ha := (point_centralizer F hZ).le a.property z z.property
    rw [←ha,mul_inv_cancel_right]
  have hr := card_mulAut_subgroup_le_two_of_fixed_point hCc zC hzC f.range hfix
  have hpR : IsPGroup 2 f.range := by
    have hp : 0 < Nat.card f.range := Nat.card_pos
    have hc : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (n := 0) (by simpa using hc)
    · exact IsPGroup.of_card (n := 1) (by simpa using hc)
  have hKC : (pResidual 2 F.H).map F.H.subtype ≤ centralizer (C : Set G) := by
    rintro _ ⟨k,hk,rfl⟩ c hc
    have he := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hpR hk
    have he' : f k = 1 := congrArg Subtype.val he
    have hh := congrArg Subtype.val (DFunLike.congr_fun he' (⟨c,hc⟩ : C))
    change (k : G)*c*(k : G)⁻¹=c at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hDC : D ≤ C := centralizer_le
    (source_block_core d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard).2
  have hHD : F.H ≤ normalizer (D : Set G) := by
    rw [(source_normalizer_factors d earlier hq chosen previous F hne hZ hcard).2]
    refine sup_le ((hKC.trans (centralizer_le hDC)).trans
      (Subgroup.centralizer_le_normalizer _)) ?_
    exact ((higherRankHypothesis d earlier hq chosen).sylow_normalizes previous.structural).trans
      (normalizer_le_normalizer_centralizer L)
  exact hnD (source_no_common_normal_block_centralizer d earlier hq chosen previous
    F hne hZ hcard D le_rfl hHD)

/-- Ambient uniqueness eliminates a block centralizer centralized by the full Sylow. -/
theorem source_block_centralizer_eq_bot_of_sylow_centralizes
    (hTC : (T : Subgroup G) ≤ centralizer (centralizer (F.U : Set G) : Set G)) :
    centralizer (L : Set G) = ⊥ :=
  source_block_centralizer_eq_bot_of_card_le_two d earlier hq chosen previous F hne hZ hcard
    (source_block_centralizer_card_le_two_of_sylow_centralizes
      d earlier hq chosen previous F hne hZ hcard hTC)

/-- Quotient order eighteen gives the literal Sylow product (T∩L)C_G(L). -/
theorem source_sylow_eq_product_of_quotient_eighteen
    (h18 : Nat.card (HStar F.H) = 18) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔ centralizer (L : Set G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let S := (T : Subgroup G) ⊓ L
  let D := centralizer (L : Set G)
  let P := S ⊔ D
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hPT : P ≤ (T : Subgroup G) := sup_le inf_le_left hDT
  have hPH : P ≤ F.H := hPT.trans (F.invariant 1)
  have hdis : Disjoint S D := by
    apply disjoint_def.mpr
    intro x hx hxD
    have hxV : x ∈ V :=
      (source_block_core d earlier hq chosen previous.structural previous.alternatives
        F hne hZ hcard).1.ge (H.centralizer_L.le
          ⟨hx.2,centralizer_le chosen.le_component hxD⟩)
    exact disjoint_def.mp (source_block_centralizer_disjoint_closure d earlier hq chosen
      previous F hne hZ hcard) (le_conjugateSpanBy V F.H hxV) hxD
  have hPc : Nat.card P = 64 * Nat.card D := by
    rw [card_sup_of_disjoint_of_normalizes S D hdis
      ((centralizer_le (show S ≤ L from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)),
      (source_sylow_index d earlier hq chosen previous.structural previous.alternatives
        F hne hZ hcard).1]
  have hHc : Nat.card F.H = 576 * Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H),h18,
      ← card_map_of_injective F.H.subtype_injective]
    change 18 * Nat.card (F.H.pCoreIn 2) = _
    rw [(source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard).2]
    ring
  have hPi : (P.subgroupOf F.H).index = 9 := by
    have hh := (P.subgroupOf F.H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv,hPc,hHc] at hh
    have hp : 0 < Nat.card D := Nat.card_pos
    nlinarith
  let S' : Sylow 2 F.H := ((T.isPGroup'.to_le hPT).comap_subtype).toSylow
    (by change ¬ 2 ∣ (P.subgroupOf F.H).index; rw [hPi]; decide)
  let T' : Sylow 2 F.H := T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)
  have he : (S' : Subgroup F.H) = (T' : Subgroup F.H) :=
    (S'.is_maximal' T'.isPGroup' (fun _ hx => hPT hx)).symm
  have hh := congrArg (Subgroup.map F.H.subtype) he
  change (P.subgroupOf F.H).map F.H.subtype =
    ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
  rw [map_subgroupOf_eq_of_le hPH,
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hh
  exact hh.symm

/-- Order eighteen makes the entire Sylow subgroup centralize C_G(U). -/
theorem source_sylow_centralizes_core_centralizer_of_quotient_eighteen
    (h18 : Nat.card (HStar F.H) = 18) :
    (T : Subgroup G) ≤ centralizer (centralizer (F.U : Set G) : Set G) := by
  let := source_core_centralizer_elementary d earlier hq chosen previous F hne hZ hcard
  rw [source_sylow_eq_product_of_quotient_eighteen d earlier hq chosen previous F hne hZ hcard h18]
  apply sup_le
  · apply le_centralizer_iff.mp
    exact (source_core_centralizer_eq_sylow_centralizer d earlier hq chosen previous
      F hne hZ hcard).le
  · exact (centralizer_le (source_block_core d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).2).trans (le_centralizer _)

/-- The ambient source hypotheses force C_G(L)=1 whenever H/O₂(H) has order eighteen. -/
theorem source_block_centralizer_eq_bot_of_quotient_eighteen
    (h18 : Nat.card (HStar F.H) = 18) : centralizer (L : Set G) = ⊥ :=
  source_block_centralizer_eq_bot_of_sylow_centralizes d earlier hq chosen previous F hne hZ hcard
    (source_sylow_centralizes_core_centralizer_of_quotient_eighteen
      d earlier hq chosen previous F hne hZ hcard h18)

/-- In the original swapping branch the quotient order is necessarily thirty-six. -/
theorem source_quotient_card_thirty_six_of_swapping
    (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype) : Nat.card (HStar F.H) = 36 := by
  apply (source_quotient_card_cases d earlier hq chosen previous F hne hZ hcard).resolve_left
  intro h18
  exact source_block_centralizer_ne_bot_of_swapping d earlier hq chosen previous
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    (source_block_centralizer_eq_bot_of_quotient_eighteen
      d earlier hq chosen previous F hne hZ hcard h18)

/-- The entire order-eighteen source branch gives the genuine recognition configuration. -/
theorem configuration_of_source_quotient_eighteen
    (h18 : Nat.card (HStar F.H) = 18) : Nonempty (DimensionFour.G2ThreeConfiguration G) := by
  rcases source_configuration_or_swapping d earlier hq chosen previous F hne hZ hcard with
    hc | ⟨q,g,s,hgL,hgP,hgH,hsX,hs,hout,_hTL,hswap,_hD,_hA,_hAc⟩
  · exact hc
  · have h36 := source_quotient_card_thirty_six_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    omega

/-- Source assembly is reduced to quotient order thirty-six and a block centralizer
of rank at least two. This is still an unresolved swapping branch. -/
theorem source_configuration_or_large_kernel_thirty_six :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      (let D := centralizer (L : Set G)
       Nat.card (HStar F.H) = 36 ∧ 4 ≤ Nat.card D ∧ IsElementaryAbelian 2 D ∧
       normalizer (D : Set G) = normalizer (L : Set G) ∧
       ¬ F.H ≤ normalizer (D : Set G) ∧
       ¬ (T : Subgroup G) ≤ centralizer (centralizer (F.U : Set G) : Set G) ∧
       centralizer (F.U : Set G) = F.ZU ⊔ D ∧
       F.H.pCoreIn 2 = F.U ⊔ D ∧ Disjoint F.U D) := by
  rcases source_configuration_or_swapping d earlier hq chosen previous F hne hZ hcard with
    hc | ⟨q,g,s,hgL,hgP,hgH,hsX,hs,hout,_hTL,hswap,_hD,_hA,_hAc⟩
  · exact Or.inl hc
  · let D := centralizer (L : Set G)
    have hnD := source_block_centralizer_ne_bot_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    have hncard : ¬ Nat.card D ≤ 2 := fun hc => hnD
      (source_block_centralizer_eq_bot_of_card_le_two d earlier hq chosen previous F hne hZ hcard hc)
    have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
      (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le hDT).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      have hnsmall : n = 0 ∨ n = 1 := by omega
      rcases hnsmall with rfl | rfl <;> simp_all
    have hcardD : 4 ≤ Nat.card D := by
      rw [hn]
      exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hn2
    have hN := source_block_centralizer_normalizer_of_ne_bot d earlier hq chosen previous F hne hZ hcard hnD
    refine Or.inr ⟨source_quotient_card_thirty_six_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap,hcardD,
      source_block_centralizer_elementary d earlier hq chosen previous F hne hZ hcard,hN,?_,?_,
      source_core_centralizer_eq_center_join d earlier hq chosen previous F hne hZ hcard,
      source_twoCore_eq_closure_join_block_centralizer d earlier hq chosen previous F hne hZ hcard,
      source_block_centralizer_disjoint_closure d earlier hq chosen previous F hne hZ hcard⟩
    · rw [hN]
      exact (higherRankHypothesis d earlier hq chosen).flag_escape F previous.alternatives
    · exact fun hTC => hnD (source_block_centralizer_eq_bot_of_sylow_centralizes
        d earlier hq chosen previous F hne hZ hcard hTC)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
