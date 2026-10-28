module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.CentralSylowKernel
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# The fixed line in the remaining block kernel

Put D=C_G(L), C=C_G(U), and E=C_D(T). The full ambient uniqueness
hypothesis makes E disjoint from every escaping conjugate D^h: a nontrivial
intersection would have its normalizer contain both LT and L^h, forcing
h into N_G(L). For h in H, both groups lie in C=Z(U)D, so |E|≤2.
A nontrivial D meets the center of T, hence |E|=2.

When |H/O₂(H)|=36, the literal subgroup (T∩L)D has index two in T and
centralizes D. The involution fixed-point bound gives |D|≤|E|²=4; the
previous exclusion of |D|≤2 gives |D|=4. The original Sylow center is
Z(U)E, of order four. Moreover every nonidentity e in E has full ambient
centralizer C_G(e)=N_G(L). Consequently |C|=8, |O₂(H)|=128, |H|=4608,
and |T|=512.

The last two theorems apply this family to the original source hypotheses,
returning SourceLocalData and its genuine I.4.5 configuration unless this
precise four-kernel case remains. These orders do not exclude that case:
the earlier weaker local diagnostic also has order 4608. Its ambient
exclusion, the unconditional local constructor, and final recognition
assembly remain with qt-d-14414-g2-source. Universal I.4.5 remains with
qt-i45-g2-recognition; EarlierSetupResults retains its earlier producers,
and the final 14.4.14 assembly belongs to qt-d-14414-source.

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

/-- Sylow-fixed elements of the block centralizer cannot lie in an escaping
conjugate of that centralizer. The full ambient uniqueness hypothesis is essential. -/
theorem source_fixed_block_kernel_disjoint_conjugate
    (x : G) (hxM : x ∉ normalizer (L : Set G)) :
    Disjoint (centralizer (L : Set G) ⊓ centralizer (T : Set G))
      ((centralizer (L : Set G)).map (MulAut.conj x).toMonoidHom) := by
  let H := higherRankHypothesis d earlier hq chosen
  let D := centralizer (L : Set G)
  let E := (D ⊓ centralizer (T : Set G)) ⊓ D.map (MulAut.conj x).toMonoidHom
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hLN : L ≤ normalizer (E : Set G) :=
    (le_centralizer_iff.mp (show E ≤ centralizer (L : Set G) from
      inf_le_left.trans inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_centralizer_iff.mp (show E ≤ centralizer (T : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hL'N : L.map (MulAut.conj x).toMonoidHom ≤ normalizer (E : Set G) := by
    apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact (show E ≤ D.map (MulAut.conj x).toMonoidHom from inf_le_right).trans
      (map_centralizer_le_centralizer_image _ _)
  apply disjoint_iff.mpr
  change E = ⊥
  by_contra hE
  have hNM : normalizer (E : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
      (T.isPGroup'.to_le ((inf_le_left.trans inf_le_left).trans hDT)) hE (sup_le hLN hTN)
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique previous.structural previous.uniqueness).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact hxM (source_mem_normalizer_of_conjugate_le d earlier hq chosen previous
    F hne hZ hcard x (hL'N.trans hNM))

/-- The fixed subgroup C_D(T) has order at most two, even when T acts
nontrivially on C_G(U). -/
theorem source_fixed_block_kernel_card_le_two :
    Nat.card (centralizer (L : Set G) ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨x,hxH,hxM⟩ := Set.not_subset.mp (H.flag_escape F previous.alternatives)
  let D := centralizer (L : Set G)
  let C := centralizer (F.U : Set G)
  let E := D ⊓ centralizer (T : Set G)
  let D' := D.map (MulAut.conj x).toMonoidHom
  let := source_core_centralizer_elementary d earlier hq chosen previous F hne hZ hcard
  have hDC : D ≤ C := centralizer_le (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).2
  have hEC : E ≤ C := inf_le_left.trans hDC
  have hCN : F.H ≤ normalizer (C : Set G) := (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_centralizer F.U)
  have hD'C : D' ≤ C := (map_mono hDC).trans
    (mem_normalizer_iff_map_conj_eq.mp (hCN hxH)).le
  have hnorm : D' ≤ normalizer (E : Set G) :=
    ((hD'C.trans (le_centralizer C)).trans (centralizer_le hEC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis := source_fixed_block_kernel_disjoint_conjugate d earlier hq chosen previous
    F hne hZ hcard x hxM
  have hc := card_le_of_le (sup_le hEC hD'C)
  rw [card_sup_of_disjoint_of_normalizes E D' hdis hnorm,
    card_map_of_injective (MulAut.conj x).injective,
    (source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard).1] at hc
  have hp : 0 < Nat.card D := Nat.card_pos
  change Nat.card E ≤ 2
  nlinarith

/-- A nontrivial block centralizer has a unique nonidentity T-fixed element. -/
theorem source_fixed_block_kernel_card_two
    (hnD : centralizer (L : Set G) ≠ ⊥) :
    Nat.card (centralizer (L : Set G) ⊓ centralizer (T : Set G) : Subgroup G) = 2 := by
  let D := centralizer (L : Set G)
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((higherRankHypothesis d earlier hq chosen).sylow_normalizes previous.structural).trans
      (normalizer_le_normalizer_centralizer L)
  have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup D (T : Subgroup G)
    hDT T.isPGroup' hTN hnD
  have hEne : D ⊓ centralizer (T : Set G) ≠ ⊥ := by
    intro he
    apply hn
    apply bot_unique
    apply (show D ⊓ omegaCenterIn (T : Subgroup G) ≤ D ⊓ centralizer (T : Set G) from ?_).trans_eq he
    exact fun _ hx => ⟨hx.1,((mem_omegaCenterIn_iff _ _).mp hx.2).2.1⟩
  have hb := source_fixed_block_kernel_card_le_two d earlier hq chosen previous F hne hZ hcard
  have hp : 0 < Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) := Nat.card_pos
  have hnone : Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) ≠ 1 :=
    fun he => hEne (card_eq_one.mp he)
  change Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 at hb
  change Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) = 2
  exact Nat.le_antisymm hb (by omega)

/-- Every nonidentity T-fixed element of D has the original maximal two-local
as its full ambient centralizer. -/
theorem source_fixed_block_element_centralizer
    (e : G) (heD : e ∈ centralizer (L : Set G))
    (heT : e ∈ centralizer (T : Set G)) (he : e ≠ 1) :
    centralizer ({e} : Set G) = normalizer (L : Set G) := by
  let H := higherRankHypothesis d earlier hq chosen
  have heT' : e ∈ (T : Subgroup G) := ((centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)) heD
  have hJC : L ⊔ (T : Subgroup G) ≤ centralizer ({e} : Set G) := by
    apply sup_le
    · exact fun x hx => mem_centralizer_singleton_iff.mpr (heD x hx)
    · exact fun x hx => mem_centralizer_singleton_iff.mpr (heT x hx)
  have hCE : centralizer ({e} : Set G) = centralizer (zpowers e : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hCN : centralizer ({e} : Set G) ≤ normalizer (zpowers e : Set G) :=
    hCE.le.trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · apply hCN.trans
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
        (T.isPGroup'.to_le (zpowers_le.mpr heT'))
        (by intro hb; exact he (mem_bot.mp (hb ▸ mem_zpowers e)))
        (hJC.trans (hCE.le.trans
          (Subgroup.centralizer_le_normalizer _)))
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique previous.structural previous.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
  · rw [source_normalizer_eq_join d earlier hq chosen previous F hne hZ hcard]
    exact hJC

/-- In quotient order thirty-six, (T∩L)D has index two in the full ambient
Sylow subgroup. In particular its trivial action on D leaves at most one
involution acting. -/
theorem source_sylow_kernel_product_index_two
    (h36 : Nat.card (HStar F.H) = 36) :
    (((T : Subgroup G) ⊓ L) ⊔ centralizer (L : Set G)).relIndex (T : Subgroup G) = 2 := by
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
  have hHc : Nat.card F.H = 1152 * Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H),h36,
      ← card_map_of_injective F.H.subtype_injective]
    change 36 * Nat.card (F.H.pCoreIn 2) = _
    rw [(source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard).2]
    ring
  have hPi : P.relIndex F.H = 18 := by
    have hh := (P.subgroupOf F.H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv] at hh
    have hp : 0 < Nat.card D := Nat.card_pos
    change Nat.card P * P.relIndex F.H = Nat.card F.H at hh
    rw [hPc,hHc] at hh
    nlinarith
  have hprod := relIndex_mul_relIndex P (T : Subgroup G) F.H hPT (F.invariant 1)
  rw [hPi] at hprod
  have hd : P.relIndex (T : Subgroup G) ∣ 18 := ⟨_,hprod.symm⟩
  have hn3 : ¬ 3 ∣ P.relIndex (T : Subgroup G) := by
    intro hd3
    have hh := hd3.trans (relIndex_dvd_card P (T : Subgroup G))
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn] at hh
    have hh' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hh
    norm_num at hh'
  have hn1 : P.relIndex (T : Subgroup G) ≠ 1 := by
    intro he
    have hi : (T : Subgroup G).relIndex F.H = 18 := by simpa only [he,one_mul] using hprod
    have hn : ¬ 2 ∣ (T : Subgroup G).relIndex F.H := (T.subtype (F.invariant 1)).not_dvd_index
    rw [hi] at hn
    exact hn (by decide)
  have hc := Nat.mem_divisors.mpr ⟨hd,(by decide : (18 : ℕ) ≠ 0)⟩
  rw [show (18 : ℕ).divisors = {1,2,3,6,9,18} by decide] at hc
  simp only [Finset.mem_insert,Finset.mem_singleton] at hc
  change P.relIndex (T : Subgroup G) = 2
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact (hn1 hc).elim
  · exact hc
  all_goals
    exfalso
    apply hn3
    norm_num [hc]

/-- The nontrivial kernel in quotient order thirty-six is exactly a four-group.
The ambient fixed-line bound and the index-two action supply both inequalities. -/
theorem source_block_centralizer_card_four
    (h36 : Nat.card (HStar F.H) = 36) (hnD : centralizer (L : Set G) ≠ ⊥) :
    Nat.card (centralizer (L : Set G)) = 4 := by
  let D := centralizer (L : Set G)
  let P := ((T : Subgroup G) ⊓ L) ⊔ D
  let := source_block_centralizer_elementary d earlier hq chosen previous F hne hZ hcard
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((higherRankHypothesis d earlier hq chosen).sylow_normalizes previous.structural).trans
      (normalizer_le_normalizer_centralizer L)
  have hDP : D ≤ centralizer (P : Set G) := by
    apply le_centralizer_iff.mp
    exact sup_le (inf_le_right.trans (le_centralizer_iff.mp le_rfl)) (le_centralizer D)
  have hb := card_le_centralizer_card_sq_of_relIndex_two D P (T : Subgroup G) hTN hDP
    (source_sylow_kernel_product_index_two d earlier hq chosen previous F hne hZ hcard h36)
  have he : Nat.card ((centralizer (T : Set G)).subgroupOf D) = 2 := by
    rw [← inf_subgroupOf_left (centralizer (T : Set G)) D, Nat.card_congr (subgroupOfEquivOfLe
      (show D ⊓ centralizer (T : Set G) ≤ D from inf_le_left)).toEquiv]
    exact source_fixed_block_kernel_card_two d earlier hq chosen previous F hne hZ hcard hnD
  change Nat.card D ≤ Nat.card ((centralizer (T : Set G)).subgroupOf D) ^ 2 at hb
  rw [he] at hb
  have hnsmall : ¬ Nat.card D ≤ 2 := fun hh => hnD
    (source_block_centralizer_eq_bot_of_card_le_two d earlier hq chosen previous F hne hZ hcard hh)
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hn3 : Nat.card D ≠ 3 := by
    intro hh
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le hDT).exists_card_eq
    have hd : 3 ∣ 2^n := by rw [←hn,hh]
    have hp := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at hp
  change Nat.card D = 4
  norm_num at hb
  omega

/-- The full Sylow center is the direct product of the original flag point
and C_D(T). This identifies its actual position, not just its rank. -/
theorem source_sylow_center_eq_point_join_fixed_kernel :
    (center (T : Subgroup G)).map (T : Subgroup G).subtype =
      F.ZU ⊔ (centralizer (L : Set G) ⊓ centralizer (T : Set G)) := by
  let := chosen.elementary
  let D := centralizer (L : Set G)
  let E := D ⊓ centralizer (T : Set G)
  let Z := (center (T : Subgroup G)).map (T : Subgroup G).subtype
  have hZT : F.ZU ≤ (T : Subgroup G) :=
    (map_subtype_le _).trans (source_closure_le_sylow d earlier hq chosen previous.structural
      previous.alternatives F)
  have hZfix : F.ZU ≤ centralizer (T : Set G) := le_centralizer_iff.mp
    ((F.invariant 1).trans (point_centralizer F hZ).le)
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le chosen.le_component).trans
    (source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard)
  have hZle : F.ZU ≤ Z := by
    intro z hz
    exact ⟨⟨z,hZT hz⟩,mem_center_iff.mpr (fun t => Subtype.ext
      (hZfix hz t t.property)),rfl⟩
  have hEle : E ≤ Z := by
    intro e he
    exact ⟨⟨e,hDT he.1⟩,mem_center_iff.mpr (fun t => Subtype.ext
      (he.2 t t.property)),rfl⟩
  apply le_antisymm _ (sup_le hZle hEle)
  rintro _ ⟨z,hz,rfl⟩
  have hzfix : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t,ht⟩)
  have hzC : (z : G) ∈ centralizer (F.U : Set G) := centralizer_le
    (source_closure_le_sylow d earlier hq chosen previous.structural previous.alternatives F) hzfix
  rw [source_core_centralizer_eq_center_join d earlier hq chosen previous F hne hZ hcard] at hzC
  have hZD : F.ZU ≤ normalizer (D : Set G) :=
    ((map_subtype_le _).trans (source_block_core d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).2).trans
        (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L))
  change (z : G) ∈ ((F.ZU ⊔ D : Subgroup G) : Set G) at hzC
  rw [coe_mul_of_left_le_normalizer_right F.ZU D hZD] at hzC
  obtain ⟨a,ha,b,hb,he⟩ := hzC
  have hbfix : b ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem
      ((centralizer (T : Set G)).inv_mem (hZfix ha)) hzfix
    rw [←he,inv_mul_cancel_left] at hh
    exact hh
  change (z : G) ∈ F.ZU ⊔ E
  rw [←he]
  exact (F.ZU ⊔ E).mul_mem (mem_sup_left ha) (mem_sup_right ⟨hb,hbfix⟩)

/-- A nontrivial block kernel forces the original full Sylow center to be a four-group. -/
theorem source_sylow_center_card_four
    (hnD : centralizer (L : Set G) ≠ ⊥) : Nat.card (center (T : Subgroup G)) = 4 := by
  let D := centralizer (L : Set G)
  let E := D ⊓ centralizer (T : Set G)
  rw [← card_map_of_injective (T : Subgroup G).subtype_injective,
    source_sylow_center_eq_point_join_fixed_kernel d earlier hq chosen previous F hne hZ hcard]
  have hdis : Disjoint F.ZU E :=
    (source_block_centralizer_disjoint_center d earlier hq chosen previous F hne hZ hcard).mono_right
      inf_le_left
  have hnorm : E ≤ normalizer (F.ZU : Set G) :=
    ((inf_le_left.trans (centralizer_le (source_block_core d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).2)).trans
      (centralizer_le (map_subtype_le _))).trans (Subgroup.centralizer_le_normalizer _)
  rw [card_sup_of_disjoint_of_normalizes F.ZU E hdis hnorm,
    source_fixed_block_kernel_card_two d earlier hq chosen previous F hne hZ hcard hnD,hZ,
    F.card 1 (by decide)]
  rfl

/-- The remaining local orders are forced by the original source hypotheses.
They describe an unresolved ambient case; they do not assert its existence. -/
theorem source_kernel_four_local_orders
    (h36 : Nat.card (HStar F.H) = 36) (hnD : centralizer (L : Set G) ≠ ⊥) :
    Nat.card (centralizer (F.U : Set G)) = 8 ∧
    Nat.card (F.H.pCoreIn 2) = 128 ∧ Nat.card F.H = 4608 ∧ Nat.card T = 512 := by
  have hD := source_block_centralizer_card_four d earlier hq chosen previous F hne hZ hcard h36 hnD
  have hc := source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard
  rw [hD] at hc
  have hQ : Nat.card (pCore 2 F.H) = 128 := by
    rw [← card_map_of_injective F.H.subtype_injective]
    exact hc.2
  have hH : Nat.card F.H = 4608 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H),h36,hQ]
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  have hS : Nat.card S = 512 := by
    rw [S.card_eq_multiplicity,hH]
    decide +kernel
  have hT : Nat.card T = 512 := by
    change Nat.card ((T : Subgroup G).subgroupOf F.H) = 512 at hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ F.H from
      F.invariant 1)).toEquiv] at hS
  exact ⟨hc.1,hc.2,hH,hT⟩

/-- The literal original source setup either constructs all local recognition
data, or has the precise four-kernel geometry below. The latter remains an
ambient exclusion obligation of the same source owner. -/
theorem source_localData_or_kernel_four :
    Nonempty (SourceLocalData L F) ∨
      (let D := centralizer (L : Set G)
       let E := D ⊓ centralizer (T : Set G)
       Nat.card (HStar F.H) = 36 ∧ Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
       Nat.card E = 2 ∧ Nat.card (center (T : Subgroup G)) = 4 ∧
       (center (T : Subgroup G)).map (T : Subgroup G).subtype = F.ZU ⊔ E ∧
       Nat.card (centralizer (F.U : Set G)) = 8 ∧ Nat.card (F.H.pCoreIn 2) = 128 ∧
       Nat.card F.H = 4608 ∧ Nat.card T = 512 ∧
       ∃ e ∈ E, e ≠ 1 ∧ centralizer ({e} : Set G) = normalizer (L : Set G)) := by
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨g,s,hgL,hgP,hgH,hsX,hs,hout,_hTL⟩ := source_involution_sylow_exists
    d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard
  rcases source_involution_action_dichotomy d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout with hc2 | hswap
  · exact Or.inl (source_localData_of_c2 d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2)
  · have hnD := source_block_centralizer_ne_bot_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    have h36 := source_quotient_card_thirty_six_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    have hE := source_fixed_block_kernel_card_two d earlier hq chosen previous F hne hZ hcard hnD
    have hEn : centralizer (L : Set G) ⊓ centralizer (T : Set G) ≠ ⊥ := by
      intro hh
      rw [hh,card_bot] at hE
      omega
    obtain ⟨e,he,hen⟩ := (centralizer (L : Set G) ⊓ centralizer (T : Set G)).bot_or_exists_ne_one.resolve_left hEn
    obtain ⟨hC,hQ,hH,hT⟩ := source_kernel_four_local_orders d earlier hq chosen previous F hne hZ hcard h36 hnD
    exact Or.inr ⟨h36,source_block_centralizer_card_four d earlier hq chosen previous
      F hne hZ hcard h36 hnD,
      source_block_centralizer_elementary d earlier hq chosen previous F hne hZ hcard,hE,
      source_sylow_center_card_four d earlier hq chosen previous F hne hZ hcard hnD,
      source_sylow_center_eq_point_join_fixed_kernel d earlier hq chosen previous F hne hZ hcard,
      hC,hQ,hH,hT,e,he,hen,
      source_fixed_block_element_centralizer d earlier hq chosen previous F hne hZ hcard e he.1 he.2 hen⟩

/-- Apply the local-data branch to the actual I.4.5 configuration while
retaining the exact remaining four-kernel branch for final ambient exclusion. -/
theorem source_configuration_or_kernel_four :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      (let D := centralizer (L : Set G)
       let E := D ⊓ centralizer (T : Set G)
       Nat.card (HStar F.H) = 36 ∧ Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
       Nat.card E = 2 ∧ Nat.card (center (T : Subgroup G)) = 4 ∧
       (center (T : Subgroup G)).map (T : Subgroup G).subtype = F.ZU ⊔ E ∧
       Nat.card (centralizer (F.U : Set G)) = 8 ∧ Nat.card (F.H.pCoreIn 2) = 128 ∧
       Nat.card F.H = 4608 ∧ Nat.card T = 512 ∧
       ∃ e ∈ E, e ≠ 1 ∧ centralizer ({e} : Set G) = normalizer (L : Set G)) := by
  rcases source_localData_or_kernel_four d earlier hq chosen previous F hne hZ hcard with
    hc | hcase
  · obtain ⟨localData⟩ := hc
    exact Or.inl (configuration_of_source_local d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard localData)
  · exact Or.inr hcase

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
