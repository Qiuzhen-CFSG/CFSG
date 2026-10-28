module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.FixedKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.CentralSylowKernel

/-!
# The fixed line in the remaining block kernel at the original G,T

Put D=C_G(L), C=C_G(U), and E=C_D(T). The full ambient uniqueness
hypothesis makes E disjoint from every escaping conjugate D^h: a nontrivial
intersection would have its normalizer contain both LT and L^h, forcing
h into N_G(L). For h in H, both groups lie in C=Z(U)D, so |E|≤2.
A nontrivial D meets the center of T, hence |E|=2.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)

include d setup structural alternatives hne hZ hcard

/-- Sylow-fixed elements of the block centralizer cannot lie in an escaping
conjugate of that centralizer. The full ambient uniqueness hypothesis is essential. -/
theorem source_fixed_block_kernel_disjoint_conjugate
    (x : G) (hxM : x ∉ normalizer (L : Set G)) :
    Disjoint (centralizer (L : Set G) ⊓ centralizer (T : Set G))
      ((centralizer (L : Set G)).map (MulAut.conj x).toMonoidHom) := by
  let H := setup
  let D := centralizer (L : Set G)
  let E := (D ⊓ centralizer (T : Set G)) ⊓ D.map (MulAut.conj x).toMonoidHom
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le setup.chosen.le_component).trans
    (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
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
    exact Set.mem_singleton_iff.mp ((H.maximal_unique_at structural).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact hxM (source_mem_normalizer_of_conjugate_le d setup structural alternatives
    F hne hZ hcard x (hL'N.trans hNM))

/-- The fixed subgroup C_D(T) has order at most two, even when T acts
nontrivially on C_G(U). -/
theorem source_fixed_block_kernel_card_le_two :
    Nat.card (centralizer (L : Set G) ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
  let H := setup
  obtain ⟨x,hxH,hxM⟩ := Set.not_subset.mp (H.flag_escape_at F alternatives)
  let D := centralizer (L : Set G)
  let C := centralizer (F.U : Set G)
  let E := D ⊓ centralizer (T : Set G)
  let D' := D.map (MulAut.conj x).toMonoidHom
  let := source_core_centralizer_elementary d setup structural alternatives F hne hZ hcard
  have hDC : D ≤ C := centralizer_le (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  have hEC : E ≤ C := inf_le_left.trans hDC
  have hCN : F.H ≤ normalizer (C : Set G) := (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_centralizer F.U)
  have hD'C : D' ≤ C := (map_mono hDC).trans
    (mem_normalizer_iff_map_conj_eq.mp (hCN hxH)).le
  have hnorm : D' ≤ normalizer (E : Set G) :=
    ((hD'C.trans (le_centralizer C)).trans (centralizer_le hEC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis := source_fixed_block_kernel_disjoint_conjugate d setup structural alternatives
    F hne hZ hcard x hxM
  have hc := card_le_of_le (sup_le hEC hD'C)
  rw [card_sup_of_disjoint_of_normalizes E D' hdis hnorm,
    card_map_of_injective (MulAut.conj x).injective,
    (source_extra_kernel_card d setup structural alternatives F hne hZ hcard).1] at hc
  have hp : 0 < Nat.card D := Nat.card_pos
  change Nat.card E ≤ 2
  nlinarith

/-- A nontrivial block centralizer has a unique nonidentity T-fixed element. -/
theorem source_fixed_block_kernel_card_two
    (hnD : centralizer (L : Set G) ≠ ⊥) :
    Nat.card (centralizer (L : Set G) ⊓ centralizer (T : Set G) : Subgroup G) = 2 := by
  let D := centralizer (L : Set G)
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le setup.chosen.le_component).trans
    (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((setup).sylow_normalizes_at structural).trans
      (normalizer_le_normalizer_centralizer L)
  have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup D (T : Subgroup G)
    hDT T.isPGroup' hTN hnD
  have hEne : D ⊓ centralizer (T : Set G) ≠ ⊥ := by
    intro he
    apply hn
    apply bot_unique
    apply (show D ⊓ omegaCenterIn (T : Subgroup G) ≤ D ⊓ centralizer (T : Set G) from ?_).trans_eq he
    exact fun _ hx => ⟨hx.1,((mem_omegaCenterIn_iff _ _).mp hx.2).2.1⟩
  have hb := source_fixed_block_kernel_card_le_two d setup structural alternatives F hne hZ hcard
  have hp : 0 < Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) := Nat.card_pos
  have hnone : Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) ≠ 1 :=
    fun he => hEne (card_eq_one.mp he)
  change Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 at hb
  change Nat.card (D ⊓ centralizer (T : Set G) : Subgroup G) = 2
  exact Nat.le_antisymm hb (by omega)

/-- In quotient order thirty-six, (T∩L)D has index two in the full ambient
Sylow subgroup. In particular its trivial action on D leaves at most one
involution acting. -/
theorem source_sylow_kernel_product_index_two
    (h36 : Nat.card (HStar F.H) = 36) :
    (((T : Subgroup G) ⊓ L) ⊔ centralizer (L : Set G)).relIndex (T : Subgroup G) = 2 := by
  let := setup.chosen.elementary
  let H := setup
  let S := (T : Subgroup G) ⊓ L
  let D := centralizer (L : Set G)
  let P := S ⊔ D
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le setup.chosen.le_component).trans
    (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  have hPT : P ≤ (T : Subgroup G) := sup_le inf_le_left hDT
  have hPH : P ≤ F.H := hPT.trans (F.invariant 1)
  have hdis : Disjoint S D := by
    apply disjoint_def.mpr
    intro x hx hxD
    have hxV : x ∈ V :=
      (source_block_core d setup structural alternatives
        F hne hZ hcard).1.ge (H.centralizer_L.le
          ⟨hx.2,centralizer_le setup.chosen.le_component hxD⟩)
    exact disjoint_def.mp (source_block_centralizer_disjoint_closure d setup
      structural alternatives F hne hZ hcard) (le_conjugateSpanBy V F.H hxV) hxD
  have hPc : Nat.card P = 64 * Nat.card D := by
    rw [card_sup_of_disjoint_of_normalizes S D hdis
      ((centralizer_le (show S ≤ L from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)),
      (source_sylow_index d setup structural alternatives
        F hne hZ hcard).1]
  have hHc : Nat.card F.H = 1152 * Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H),h36,
      ← card_map_of_injective F.H.subtype_injective]
    change 36 * Nat.card (F.H.pCoreIn 2) = _
    rw [(source_extra_kernel_card d setup structural alternatives F hne hZ hcard).2]
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
  let := source_block_centralizer_elementary d setup structural alternatives F hne hZ hcard
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((setup).sylow_normalizes_at structural).trans
      (normalizer_le_normalizer_centralizer L)
  have hDP : D ≤ centralizer (P : Set G) := by
    apply le_centralizer_iff.mp
    exact sup_le (inf_le_right.trans (le_centralizer_iff.mp le_rfl)) (le_centralizer D)
  have hb := card_le_centralizer_card_sq_of_relIndex_two D P (T : Subgroup G) hTN hDP
    (source_sylow_kernel_product_index_two d setup structural alternatives F hne hZ hcard h36)
  have he : Nat.card ((centralizer (T : Set G)).subgroupOf D) = 2 := by
    rw [← inf_subgroupOf_left (centralizer (T : Set G)) D, Nat.card_congr (subgroupOfEquivOfLe
      (show D ⊓ centralizer (T : Set G) ≤ D from inf_le_left)).toEquiv]
    exact source_fixed_block_kernel_card_two d setup structural alternatives F hne hZ hcard hnD
  change Nat.card D ≤ Nat.card ((centralizer (T : Set G)).subgroupOf D) ^ 2 at hb
  rw [he] at hb
  have hnsmall : ¬ Nat.card D ≤ 2 := fun hh => hnD
    (source_block_centralizer_eq_bot_of_card_le_two d setup structural alternatives F hne hZ hcard hh)
  have hDT : D ≤ (T : Subgroup G) := (centralizer_le setup.chosen.le_component).trans
    (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  have hn3 : Nat.card D ≠ 3 := by
    intro hh
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le hDT).exists_card_eq
    have hd : 3 ∣ 2^n := by rw [←hn,hh]
    have hp := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at hp
  change Nat.card D = 4
  norm_num at hb
  omega

/-- The remaining local orders are forced by the original source hypotheses.
They describe an unresolved ambient case; they do not assert its existence. -/
theorem source_kernel_four_local_orders
    (h36 : Nat.card (HStar F.H) = 36) (hnD : centralizer (L : Set G) ≠ ⊥) :
    Nat.card (centralizer (F.U : Set G)) = 8 ∧
    Nat.card (F.H.pCoreIn 2) = 128 ∧ Nat.card F.H = 4608 ∧ Nat.card T = 512 := by
  have hD := source_block_centralizer_card_four d setup structural alternatives F hne hZ hcard h36 hnD
  have hc := source_extra_kernel_card d setup structural alternatives F hne hZ hcard
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

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
