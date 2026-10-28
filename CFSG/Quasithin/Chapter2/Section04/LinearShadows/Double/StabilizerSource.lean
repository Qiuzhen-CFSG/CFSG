module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.IndexTwo
public import CFSG.Quasithin.Chapter2.Section04.CoreElementarySource

/-!
# The original block stabilizer and mixed-normalizer obstruction

The paired action gives an index-two block stabilizer containing the
Thompson subgroup and the original two-core. Thus it lies in beta and
supplies the literal local pair with the second block. A mixed subgroup
containing the core cannot have a normalizer of the original Sylow order:
source maximality would put that normalizer in Gamma-e-zero and make its
core, hence the mixed subgroup, elementary.

Source: Aschbacher–Smith, Section 2.4.1, printed pp.540–541.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem DoubleLinearSourceSetup.second_outside
    (c : DoubleLinearSourceSetup d M₀ n) : ¬ c.second ≤ M := by
  obtain ⟨s,hs,he⟩ := c.exchange
  have hsM : s ∈ M := d.full_pair.1.1.2.1 hs
  intro h
  apply d.outside
  intro a ha
  have ha' : s*a*s⁻¹ ∈ c.second := he ▸ (show
      s*a*s⁻¹ ∈ (d.block.map d.H.subtype).conjBy s from ⟨a,ha,rfl⟩)
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using
    M.mul_mem (M.mul_mem (M.inv_mem hsM) (h ha')) hsM

omit [Finite G] in
theorem DoubleLinearSourceSetup.block_stabilizer_index
    (c : DoubleLinearSourceSetup d M₀ n) :
    (((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)).relIndex
        ((d.S : Subgroup d.H).map d.H.subtype) = 2 := by
  obtain ⟨s,hs,he⟩ := c.exchange
  simpa only [inf_relIndex_left] using normalizer_relIndex_eq_two_of_pair
    ((d.S : Subgroup d.H).map d.H.subtype) (d.block.map d.H.subtype) c.second
    c.permutes s hs (fun hh => c.second_ne (he.symm.trans hh))

theorem DoubleLinearSourceSetup.block_stabilizer_beta
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let B := ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)
    B ∈ beta M ∧ elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤ B ∧
      twoCore d.H ≤ B := by
  let := c.field₁_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  have hp := c.core_pair T hST hSM hMT hi
  have hJR : elementaryAbelianMaxJ S ≤ B :=
    le_inf (sSup_le (fun _ h => h.1)) (hp.1 ▸ c.marked₁.normalizes)
  have hQB : twoCore d.H ≤ B := (le_sup_left.trans_eq hp.2.1.symm).trans hJR
  refine ⟨?_,hJR,hQB⟩
  apply lemma_2_3_9_8 hG T hM hTM hu d.mem_gammaEvenZero.1 d.full_pair
    d.S le_rfl hJR hQB inf_le_left c.block_stabilizer_index
  intro a ha
  exact hQB (d.mem_gammaEvenZero.2
    ⟨(map_subtype_le _) ha.1, centralizer_le hQB ha.2⟩)

theorem DoubleLinearSourceSetup.block_stabilizer_local_pair
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let B := ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)
    (B, c.second ⊔ B) ∈ localPairs (Chapter1.He G) M := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  let J := c.second ⊔ B
  obtain ⟨hB,_,hQB⟩ := c.block_stabilizer_beta hG T hM hTM hu hST hSM hMT hi
  have hJH : J ≤ d.H := sup_le
    ((le_sup_right.trans_eq c.join).trans (map_subtype_le _))
    (inf_le_left.trans (map_subtype_le _))
  have hQJ : twoCore d.H ≤ J := hQB.trans le_sup_right
  have hQne : twoCore d.H ≠ ⊥ :=
    (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hJne : J ≠ ⊥ := fun he => hQne (bot_unique (he ▸ hQJ))
  have hJe : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_4 hJne hJH
    d.mem_gammaEvenZero.2 (inf_le_left.trans hQJ)
  have hQQ : twoCore d.H ≤ twoCore J := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 d.H) hQJ (hJH.trans (le_normalizer_twoCore d.H))
  exact ⟨hB,hJe,fun he => hQne (bot_unique (he ▸ hQQ)),le_sup_right,
    fun he => c.second_outside (le_sup_left.trans he)⟩

omit [Finite G] in
/-- The original block stabilizer is also the stabilizer of its nontrivial
Thompson factor once the two actual factors are distinct. -/
theorem DoubleLinearSourceSetup.block_stabilizer_eq_factor_stabilizer
    (c : DoubleLinearSourceSetup d M₀ n)
    (hne : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        d.block.map d.H.subtype ≠
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ c.second) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    S ⊓ normalizer (d.block.map d.H.subtype : Set G) =
      S ⊓ normalizer ((elementaryAbelianMaxJ S ⊓ d.block.map d.H.subtype : Subgroup G) : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  have hn : S ≤ normalizer (R : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ S)
  apply le_antisymm
  · rintro a ⟨ha,haL⟩
    exact ⟨ha,inf_normalizer_le_normalizer_inf ⟨hn ha,haL⟩⟩
  · rintro a ⟨ha,haR⟩
    refine ⟨ha,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    rcases c.permutes a ha with hfix | hswap
    · exact hfix
    have hmap := mem_normalizer_iff_map_conj_eq.mp haR
    change (R ⊓ d.block.map d.H.subtype).map (MulAut.conj a).toMonoidHom = _ at hmap
    have hr : R.map (MulAut.conj a).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hn ha)
    change (d.block.map d.H.subtype).map (MulAut.conj a).toMonoidHom = c.second at hswap
    rw [map_inf _ _ _ (MulAut.conj a).injective,hr,hswap] at hmap
    exact (hne hmap.symm).elim

/-- A mixed overgroup of the core becomes elementary if its normalizer
has at least the original Sylow order. The actual beta base can be larger
than the Thompson subgroup. -/
theorem MinimalBlockSetup.normalizer_elementary_of_beta_base
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (B W : Subgroup G) (hB : B ∈ beta M)
    (hBS : B ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hQW : twoCore d.H ≤ W)
    (hWS : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hBN : B ≤ normalizer (W : Set G))
    (hout : ¬ d.H ⊓ normalizer (W : Set G) ≤ M)
    (hcard : Nat.card ((d.S : Subgroup d.H).map d.H.subtype) ≤
      Nat.card ((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G))
    (hBT : B ≤ (T : Subgroup G)) :
    IsElementaryAbelian 2 W := by
  let N := normalizer (W : Set G)
  let J := d.H ⊓ N
  let S₁ := (T : Subgroup G) ⊓ N
  have hWp := (d.S.isPGroup'.map d.H.subtype).to_le hWS
  have hMe := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hQe := beta_twoCore_mem_S2e hG.evenCharacteristic hMe d.full_pair.1.1
    (map_subtype_le _) d.mem_gammaEvenZero.2
  have hWe := Chapter1.lemma_1_1_4_1 hQe hQW hWp
  have hWne : W ≠ ⊥ := hWe.1
  have hJe : J ∈ Chapter1.He G := Chapter1.normalizer_mem_He_of_isPGroup
    d.mem_gammaEvenZero.2 hWp (hWS.trans (map_subtype_le _))
  have hWJ : W ≤ J := le_inf (hWS.trans (map_subtype_le _)) W.le_normalizer
  have hQJ : W ≤ twoCore J := le_pCoreIn_of_normalizes hWp hWJ inf_le_right
  have hp : (B,J) ∈ localPairs (Chapter1.He G) M :=
    ⟨hB,hJe,fun he => hWne (bot_unique (he ▸ hQJ)),
      le_inf (hBS.trans (map_subtype_le _)) hBN,hout⟩
  have hQN : W ≤ twoCore N := le_pCoreIn_of_normalizes hWp W.le_normalizer le_rfl
  have hNg : N ∈ gamma (Chapter1.He G) M :=
    ⟨fun he => hWne (bot_unique (he ▸ hQN)),⟨(B,J),hp,inf_le_right⟩⟩
  have hS₁ : S₁ ∈ beta M := beta_mono hB (le_inf hBT hBN)
    (T.isPGroup'.to_le inf_le_left)
  have hpart : twoPart d.H ≤ twoPart N := by
    rw [←sylow_image_card d.H d.S]
    exact hcard.trans (beta_card_le_twoPart hS₁ inf_le_right)
  have hNzero := (lemma_2_4_3_2 d.mem_gammaEvenZero ⟨hNg,hWe.2.2⟩ hpart).2
  let : IsElementaryAbelian 2 (twoCore N) :=
    gammaEvenZero_twoCore_elementary_source hG T hTM hu hNzero
  exact IsElementaryAbelian.of_le hQN

/-- Literal normalizer-size consumer for a nonelementary mixed subgroup
normalized by the original block stabilizer and the escaping first block. -/
theorem DoubleLinearSourceSetup.mixed_normalizer_card_lt
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (W : Subgroup G) (hQW : twoCore d.H ≤ W)
    (hWS : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hBN : ((d.S : Subgroup d.H).map d.H.subtype ⊓
      normalizer (d.block.map d.H.subtype : Set G)) ≤ normalizer (W : Set G))
    (hLN : d.block.map d.H.subtype ≤ normalizer (W : Set G))
    (hnot : ¬ IsElementaryAbelian 2 W) :
    Nat.card ((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) <
      Nat.card ((d.S : Subgroup d.H).map d.H.subtype) := by
  by_contra! hc
  exact hnot (d.normalizer_elementary_of_beta_base hG T hM hTM hu _ W
    (c.block_stabilizer_beta hG T hM hTM hu hST hSM hMT hi).1
    inf_le_left hQW hWS hBN
    (fun he => d.outside ((le_inf (map_subtype_le _) hLN).trans he))
    hc (inf_le_left.trans hST))

end CFSG.Quasithin.Chapter2
