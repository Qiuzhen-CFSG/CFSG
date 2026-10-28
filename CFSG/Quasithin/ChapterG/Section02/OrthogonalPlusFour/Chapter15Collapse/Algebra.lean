module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The central middle-layer argument of 15.3.54

Cross-normalization and the two disjoint point bounds make the marked
intersection central. For the resulting abelian middle layer, coprime
splitting uses the actual conjugation image of Y; Y itself may have even
order. The absence of Y-fixed vectors in the upper section identifies the
middle layer as a fixed-subgroup preimage. This proves T-normality of its
fixed factor, which the omega-center hypothesis eliminates.

The literal Chapter 15 consumer is in `Chapter15Collapse`. The hypotheses
about the natural and upper modules remain separate source obligations.
The central order-two argument also appears in the later 15.3.59 proof,
`Nonabelian/Fusion/Core/Reduction.lean`.

Source: Aschbacher–Smith, 15.3.54, printed p.1146, PDF p.1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G]

/-- The two marked factors centralize the intersection: each commutator
lies in the other group and in a disjoint derived-subgroup bound. -/
theorem intersection_centralizes_marks {A B W X Z Z' : Subgroup G}
    (hWA : W ≤ A) (hXB : X ≤ B)
    (hWB : W ≤ normalizer (B : Set G)) (hXA : X ≤ normalizer (A : Set G))
    (hAZ : ⁅A,A⁆ ≤ Z) (hBZ : ⁅B,B⁆ ≤ Z')
    (hAZ' : A ⊓ Z' = ⊥) (hBZ' : B ⊓ Z = ⊥) :
    A ⊓ B ≤ centralizer (W : Set G) ∧ A ⊓ B ≤ centralizer (X : Set G) := by
  constructor
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hBZ']
    exact le_inf
      ((commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hWB))
      ((commutator_mono inf_le_left hWA).trans hAZ)
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hAZ']
    exact le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hXA))
      ((commutator_mono inf_le_right hXB).trans hBZ)

/-- The source omega-center, with both inclusions kept explicit. -/
def omegaCenter (T : Subgroup G) : Subgroup G :=
  ((omega₁ (center T) (p := 2)).map (center T).subtype).map T.subtype

/-- A T-normal factor disjoint from the omega-center is trivial.
The same central order-two argument is used later in 15.3.59. -/
theorem normal_disjoint_omega_eq_bot [Finite G] (T C V : Subgroup G)
    (hT : IsPGroup 2 T) (hCT : C ≤ T)
    (hTC : T ≤ normalizer (C : Set G))
    (hΩ : omegaCenter T ≤ V) (hd : Disjoint C V) : C = ⊥ := by
  let D := C.subgroupOf T
  let : D.Normal := normal_subgroupOf_of_le_normalizer hTC
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  by_contra hn
  have hD : D ≠ ⊥ := by
    intro he
    have hm := congrArg (map T.subtype) he
    rw [map_subgroupOf_eq_of_le hCT, Subgroup.map_bot] at hm
    exact hn hm
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  obtain ⟨A, _, hAD, hA, hAc⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) D inferInstance
  have hAbot : A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have haC : (a : G) ∈ C := hAD ha
    have haΩ : (a : G) ∈ omegaCenter T := by
      apply mem_map_of_mem
      apply mem_map_of_mem (center T).subtype (x := ⟨a, hAc ha⟩)
      apply Subgroup.subset_closure
      change (⟨a, hAc ha⟩ : center T) ^ (2 ^ 1) = 1
      apply Subtype.ext
      have hp := congrArg (fun x : A => (x : T)) (pow_card_eq_one' (x := ⟨a, ha⟩))
      change a ^ Nat.card A = 1 at hp
      change a ^ (2 ^ 1) = 1
      simpa only [hA, pow_one] using hp
    have habot : (a : G) ∈ (⊥ : Subgroup G) := (disjoint_iff.mp hd).le ⟨haC, hΩ haΩ⟩
    exact Subtype.ext (mem_bot.mp habot)
  have hc : Nat.card A = 1 := by simp [hAbot]
  omega

/-- The actual action image is coprime when its kernel contains a
subgroup of odd index. The original actor may have even order. -/
theorem coprime_conjugation_image [Finite G] (B Y K : Subgroup G)
    (hYB : Y ≤ normalizer (B : Set G))
    (hB : IsPGroup 2 B) (hBK : B ≤ centralizer (K : Set G))
    (hodd : Odd (K.subgroupOf Y).index) :
    Nat.Coprime (Nat.card (B.normalizerMonoidHom.comp (inclusion hYB)).range)
      (Nat.card B) := by
  let f := B.normalizerMonoidHom.comp (inclusion hYB)
  have hker : K.subgroupOf Y ≤ f.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    ext b
    change (k : G) * (b : G) * (k : G)⁻¹ = (b : G)
    rw [mem_centralizer_iff.mp (hBK b.property) k hk, mul_inv_cancel_right]
  have hdiv : Nat.card f.range ∣ (K.subgroupOf Y).index := by
    rw [← index_ker]
    exact index_dvd_of_le hker
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  rw [hn]
  exact (hodd.of_dvd_nat hdiv).coprime_two_right.pow_right n

/-- If P/B has no Y-fixed vectors and [B,Y]≤V, then B is precisely
the preimage of the fixed subgroup of P/V. -/
theorem fixed_preimage {P B V Y : Subgroup G}
    (hVB : V ≤ B) (hBP : B ≤ P) (hPV : P ≤ normalizer (V : Set G))
    (hBY : ⁅B,Y⁆ ≤ V)
    (hno : commutatorPreimage P Y B ≤ B) :
    commutatorPreimage P Y V = B := by
  apply le_antisymm
  · apply le_trans _ hno
    exact le_commutatorPreimage (commutatorPreimage_le P Y V)
      ((commutator_commutatorPreimage_le P Y V hPV).trans hVB)
  · exact le_commutatorPreimage hBP hBY

/-- The central middle layer splits under the actual Y-action. Its fixed
factor is T-normal, hence vanishes by the omega-center condition. -/
theorem central_layer_collapse [Finite G] (T P B V Y K : Subgroup G)
    (hT : IsPGroup 2 T) (hPT : P ≤ T) (hVB : V ≤ B) (hBP : B ≤ P)
    (hcentral : B ≤ centralizer (P : Set G))
    (hYB : Y ≤ normalizer (B : Set G))
    (hTP : T ≤ normalizer (P : Set G))
    (hTV : T ≤ normalizer (V : Set G))
    (hTY : T ≤ normalizer (Y : Set G))
    (hBY : ⁅B,Y⁆ ≤ V) (hVY : ⁅V,Y⁆ = V)
    (hno : commutatorPreimage P Y B ≤ B)
    (hKP : K ≤ P) (hodd : Odd (K.subgroupOf Y).index)
    (hΩ : omegaCenter T ≤ V) :
    commutatorPreimage P Y V = B ∧
    B = V ⊔ (B ⊓ centralizer (Y : Set G)) ∧
    Disjoint V (B ⊓ centralizer (Y : Set G)) ∧
    T ≤ normalizer (B ⊓ centralizer (Y : Set G) : Set G) ∧
    B ⊓ centralizer (Y : Set G) = ⊥ ∧ B = V := by
  have hBT := hBP.trans hPT
  have hPV : P ≤ normalizer (V : Set G) := hPT.trans hTV
  have hpre := fixed_preimage hVB hBP hPV hBY hno
  have hTB : T ≤ normalizer (B : Set G) := by
    rw [← hpre]
    exact commutatorPreimage_normalized P Y V T hPV hTP hTY hTV
  have hB : IsPGroup 2 B := hT.of_injective (inclusion hBT) (inclusion_injective _)
  let : IsMulCommutative B := le_centralizer_iff_isMulCommutative.mp
    (hcentral.trans (centralizer_le hBP))
  have hcop := coprime_conjugation_image B Y K hYB hB
    (hcentral.trans (centralizer_le hKP)) hodd
  have hmove : ⁅B,Y⁆ = V := le_antisymm hBY
    (hVY.symm.le.trans (commutator_mono hVB le_rfl))
  have hsplit := commutator_centralizer_decomposition_of_coprime_image B Y hYB hcop
  rw [hmove] at hsplit
  have hTC : T ≤ normalizer (B ⊓ centralizer (Y : Set G) : Set G) :=
    (le_inf hTB (hTY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  have hd : Disjoint V (B ⊓ centralizer (Y : Set G)) := disjoint_iff.mpr hsplit.2
  have hC := normal_disjoint_omega_eq_bot T (B ⊓ centralizer (Y : Set G)) V hT
    (inf_le_left.trans hBT) hTC hΩ hd.symm
  refine ⟨hpre, hsplit.1.symm, hd, hTC, hC, ?_⟩
  simpa only [hC, sup_bot_eq] using hsplit.1.symm
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
