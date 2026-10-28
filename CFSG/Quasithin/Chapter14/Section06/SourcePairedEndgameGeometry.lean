module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCoreCover
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedQuotientMarking
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCoreGeometry
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.CommutingCoreGeometry
public import Theory.GroupTheory.OmegaCenterProduct
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The paired commutator and centralizer geometry in original 14.6.9

Once the residual centralizer D vanishes, the actual point core is the
product of its two block point cores. Their marked Borel models identify
the vector commutators, residual commutators, and centralizer tests.
Disjointness and commutation let these identities pass to their literal
products. The order-two centers give the omega-center containment.

The resulting packet supplies all five remaining commutator and centralizer
inputs to the paired endgame. It uses the source subgroups and their actual
residuals; no model, action, coordinate, or centralizer premise remains.
The sole additional source premise is D = 1.

Source: Aschbacher--Smith, proof of 14.6.9(i,k--n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem commutator_pair_bound (B A₁ A₂ X₁ X₂ E : Subgroup G)
    (hBE : B ≤ normalizer (E : Set G))
    (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B) (hX₁ : X₁ ≤ B) (hX₂ : X₂ ≤ B)
    (h₁₁ : ⁅A₁,X₁⁆ ≤ E) (h₁₂ : ⁅A₁,X₂⁆ ≤ E)
    (h₂₁ : ⁅A₂,X₁⁆ ≤ E) (h₂₂ : ⁅A₂,X₂⁆ ≤ E) :
    ⁅A₁ ⊔ A₂,X₁ ⊔ X₂⁆ ≤ E := by
  apply commutator_sup_le_of_relative_normal B A₁ A₂ (X₁ ⊔ X₂) E hBE hA₁ hA₂
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal B X₁ X₂ A₁ E hBE hX₁ hX₂
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal B X₁ X₂ A₂ E hBE hX₁ hX₂
      (by rwa [commutator_comm]) (by rwa [commutator_comm])

omit [Finite G] in
private theorem residual_core_normalized (B : Subgroup G) :
    B ≤ normalizer ((((pResidual 2 B).map B.subtype).pCoreIn 2 : Subgroup G) : Set G) :=
  (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

omit [Finite G] in
private theorem center_residual_core_le_omega (B : Subgroup G)
    (hc : Nat.card (center (((pResidual 2 B).map B.subtype).pCoreIn 2)) = 2)
    (hle : (center (((pResidual 2 B).map B.subtype).pCoreIn 2)).map
      (((pResidual 2 B).map B.subtype).pCoreIn 2).subtype ≤ B.pCoreIn 2) :
    (center (((pResidual 2 B).map B.subtype).pCoreIn 2)).map
      (((pResidual 2 B).map B.subtype).pCoreIn 2).subtype ≤ omegaOneCenterAmbient (B.pCoreIn 2) := by
  let N := ((pResidual 2 B).map B.subtype).pCoreIn 2
  let Z := (center N).map N.subtype
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective N.subtype_injective,hc]
  have hBZ : B ≤ centralizer (Z : Set G) :=
    ((residual_core_normalized B).trans
      (normalizer_le_normalizer_characteristic_image N (center N))).trans
      (normalizer_le_centralizer_of_card_two Z hZcard)
  intro z hz
  refine (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hle hz,?_,?_⟩
  · have hp := pow_card_eq_one' (x := (⟨z,hz⟩ : Z))
    rw [hZcard] at hp
    exact congrArg Subtype.val hp
  · intro y hy
    exact (hBZ (pCoreIn_le 2 B hy) z hz).symm

/-- The actual paired point cores supply the complete endgame geometry after D = 1. -/
theorem source_paired_endgame_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hD : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) = ⊥) :
    let B := I ⊓ Mc
    let K := (pResidual 2 I).map I.subtype
    let A := K.pCoreIn 2
    let C := B.pCoreIn 2
    let Kz := (pResidual 2 B).map B.subtype
    let N := Kz.pCoreIn 2
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    Z₀ ≤ omegaOneCenterAmbient C ∧ ⁅A,Kz⁆ ≤ E ∧ ⁅C,Kz⁆ = N ∧
      C ⊓ centralizer (N : Set G) ≤ Z₀ ∧
      (∀ x ∈ C, (∀ n ∈ N, ⁅n,x⁆ ∈ Z₀) → x ∈ N) := by
  let B := I ⊓ Mc
  let K := (pResidual 2 I).map I.subtype
  let A := K.pCoreIn 2
  let C := B.pCoreIn 2
  let Kz := (pResidual 2 B).map B.subtype
  let N := Kz.pCoreIn 2
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let B₁ := K₁ ⊓ Mc
  let B₂ := K₂ ⊓ Mc
  let P₁ := B₁.pCoreIn 2
  let P₂ := B₂.pCoreIn 2
  let X₁ := (pResidual 2 B₁).map B₁.subtype
  let X₂ := (pResidual 2 B₂).map B₂.subtype
  let N₁ := X₁.pCoreIn 2
  let N₂ := X₂.pCoreIn 2
  let U₁ := K₁.pCoreIn 2
  let U₂ := K₂.pCoreIn 2
  let E := (U₁ ⊓ N₁) ⊔ (U₂ ⊓ N₂)
  let Z₁ := (center N₁).map N₁.subtype
  let Z₂ := (center N₂).map N₂.subtype
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨hd,hc,_,_⟩ := source_paired_point_centralizer_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨hU₁,hU₂⟩ := source_paired_cores_eq_modules c b i j hij hs hi
  have hA : A = U₁ ⊔ U₂ := by
    change K.pCoreIn 2 = _
    have hK : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
    rw [←hK]
    exact pCoreIn_sup_of_disjoint_of_commuting 2 K₁ K₂ hd hc
  have hC : C = P₁ ⊔ P₂ := source_paired_point_core_cover
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hpairIndex hD
  have hKz : Kz = X₁ ⊔ X₂ := (source_paired_point_residuals
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi).1
  have hN : N = N₁ ⊔ N₂ := source_paired_residual_core_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hg₁ := source_paired_block_point_core_geometry
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hg₂ := source_paired_block_point_core_geometry
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b j i (Ne.symm hij) hs h'.block
  have hP₁K : P₁ ≤ K₁ := (pCoreIn_le 2 B₁).trans inf_le_left
  have hP₂K : P₂ ≤ K₂ := (pCoreIn_le 2 B₂).trans inf_le_left
  have hX₁K : X₁ ≤ K₁ := (map_subtype_le _).trans inf_le_left
  have hX₂K : X₂ ≤ K₂ := (map_subtype_le _).trans inf_le_left
  have hB₁B : B₁ ≤ B := inf_le_inf (map_subtype_le _) le_rfl
  have hB₂B : B₂ ≤ B := inf_le_inf (map_subtype_le _) le_rfl
  have hP₁B : P₁ ≤ B := (pCoreIn_le 2 B₁).trans hB₁B
  have hP₂B : P₂ ≤ B := (pCoreIn_le 2 B₂).trans hB₂B
  have hX₁B : X₁ ≤ B := (map_subtype_le _).trans hB₁B
  have hX₂B : X₂ ≤ B := (map_subtype_le _).trans hB₂B
  obtain ⟨_,_,_,_,_,_,hRB,_⟩ := source_paired_borel_action_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hU₁B : U₁ ≤ B := ((pCoreIn_le_sylow K₁ h.sylow).trans_eq
    h.sylow_image).trans (inf_le_left.trans hRB)
  have hU₂B : U₂ ≤ B := ((pCoreIn_le_sylow K₂ h'.sylow).trans_eq
    h'.sylow_image).trans (inf_le_left.trans hRB)
  obtain ⟨eb₁,heb₁⟩ := source_paired_block_borel_vectors
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨eb₂,heb₂⟩ := source_paired_block_borel_vectors
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b j i (Ne.symm hij) hs h'.block
  have hsmall₁ : ⁅U₁,X₁⁆ = U₁ ⊓ N₁ :=
    BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry.marked_borel_vector_commutator
      B₁ eb₁ U₁ (hU₁.trans heb₁.symm)
  have hsmall₂ : ⁅U₂,X₂⁆ = U₂ ⊓ N₂ :=
    BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry.marked_borel_vector_commutator
      B₂ eb₂ U₂ (hU₂.trans heb₂.symm)
  have hBE : B ≤ normalizer (E : Set G) := by
    have hh := (source_paired_irreducible_section
      hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi).2.2.1
    rw [←hU₁,←hU₂] at hh
    exact hh
  have hcross {V W : Subgroup G} (hV : V ≤ K₁) (hW : W ≤ K₂) : ⁅V,W⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hV.trans (hc.trans (centralizer_le hW)))
  have hcomm : ⁅C,Kz⁆ = N := by
    rw [hC,hKz,hN]
    apply le_antisymm
    · apply commutator_pair_bound B P₁ P₂ X₁ X₂ (N₁ ⊔ N₂)
        (hN ▸ residual_core_normalized B) hP₁B hP₂B hX₁B hX₂B
      · exact hg₁.2.2.le.trans le_sup_left
      · rw [hcross hP₁K hX₂K]; exact bot_le
      · rw [commutator_comm,hcross hX₁K hP₂K]; exact bot_le
      · exact hg₂.2.2.le.trans le_sup_right
    · exact sup_le (hg₁.2.2.symm.le.trans (commutator_mono le_sup_left le_sup_left))
        (hg₂.2.2.symm.le.trans (commutator_mono le_sup_right le_sup_right))
  have hsmall : ⁅A,Kz⁆ ≤ E := by
    rw [hA,hKz]
    apply commutator_pair_bound B U₁ U₂ X₁ X₂ E hBE hU₁B hU₂B hX₁B hX₂B
    · exact hsmall₁.le.trans le_sup_left
    · rw [hcross (pCoreIn_le 2 K₁) hX₂K]; exact bot_le
    · rw [commutator_comm,hcross hX₁K (pCoreIn_le 2 K₂)]; exact bot_le
    · exact hsmall₂.le.trans le_sup_right
  have hZ₁P : Z₁ ≤ omegaOneCenterAmbient P₁ := center_residual_core_le_omega B₁
    (source_paired_block_borel_core hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi).2.2 (hg₁.1.symm.le.trans inf_le_left)
  have hZ₂P : Z₂ ≤ omegaOneCenterAmbient P₂ := center_residual_core_le_omega B₂
    (source_paired_block_borel_core hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b j i (Ne.symm hij) hs h'.block).2.2 (hg₂.1.symm.le.trans inf_le_left)
  have hN₁P : N₁ ≤ P₁ := hg₁.2.2.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans (B₁.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image B₁ (pCore 2 B₁)))))
  have hN₂P : N₂ ≤ P₂ := hg₂.2.2.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans (B₂.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image B₂ (pCore 2 B₂)))))
  have hpair := commuting_core_geometry K₁ K₂ P₁ P₂ N₁ N₂ Z₁ Z₂ hd hc hP₁K hP₂K
    hN₁P hN₂P (map_subtype_le _) (map_subtype_le _) hg₁.1.le hg₂.1.le hg₁.2.1 hg₂.2.1
  have hcent : C ⊓ centralizer (N : Set G) ≤ Z₁ ⊔ Z₂ := by
    rw [hC,hN]
    exact hpair.1
  have hmod : ∀ x ∈ C, (∀ n ∈ N, ⁅n,x⁆ ∈ Z₁ ⊔ Z₂) → x ∈ N := by
    rw [hC,hN]
    exact hpair.2
  refine ⟨?_,hsmall,hcomm,hcent,hmod⟩
  change Z₁ ⊔ Z₂ ≤ omegaOneCenterAmbient C
  rw [hC,omegaOneCenterAmbient_sup_of_disjoint_of_commuting P₁ P₂
    (hd.mono hP₁K hP₂K) (hP₁K.trans (hc.trans (centralizer_le hP₂K)))]
  exact sup_le_sup hZ₁P hZ₂P
end CFSG.Quasithin.Chapter14.Section06
