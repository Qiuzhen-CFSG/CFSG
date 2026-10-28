module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.FourRows

/-!
# Whole-normalizer enlargement from a fixed tetrad

For an elementary subgroup containing the native second involution, its full
centralizer lies in the Mathieu local. If the quotient image fixes exactly one
of the two displayed tetrads, the centralizer preserves that tetrad and hence
its kernel involution, mask 818. The central omega fixes every pair in the
tetrad, so it fixes each point; the intrinsic pair character then puts mask 818
in the form radical. This gives a nontrivial zero-form subgroup invariant under
the whole normalizer.

The eight literal Figure 2(a) images below discharge the fixed-tetrad premise.
This is a subcase of the box branch, not the whole box classification.
Source: Kleidman--Wilson (1988), Figure 2(a) and Proposition 2.3.2, p.492.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxTetrads
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open ElementaryEightGeometry M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def tetrad : Fin 2 → Fin 4 → Fin 24 := ![![7,15,16,17],![4,5,8,14]]

private theorem tetrad_injective : ∀ k, Function.Injective (tetrad k) := by decide +kernel
private theorem tetrad_label : ∀ (k : Fin 2) (f : Fin 4 → Fin 4),
    Function.Injective f →
      Nat.xor (pairLabel (tetrad k (f 0)) (tetrad k (f 1)))
        (pairLabel (tetrad k (f 2)) (tetrad k (f 3))) = 818 := by decide +kernel
private theorem pair_detect : ∀ (k : Fin 2) (i : Fin 4) (a : Fin 24),
    (∀ j : Fin 4, ∃ b : Fin 24, pairLabel a b = pairLabel (tetrad k i) (tetrad k j)) →
      a = tetrad k i := by decide +kernel

private theorem tetrad_product (k : Fin 2) : kernelValue 818 =
    kernelValue (pairLabel (tetrad k 0) (tetrad k 1)) *
      kernelValue (pairLabel (tetrad k 2) (tetrad k 3)) := by
  have h := tetrad_label k id Function.injective_id
  dsimp only [id_eq] at h
  rw [← kernelValue_xor,h]

private theorem pair_centralizes (X : Subgroup Model) (hXM : X ≤ M)
    (i j : Fin 24)
    (hi : ∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i)
    (hj : ∀ p ∈ (X.subgroupOf M).map starHom, p.val j = j) :
    (kernelValue (pairLabel i j) : Model) ∈ centralizer (X : Set Model) := by
  intro x hx
  let x0 : M := ⟨x,hXM hx⟩
  have hm : starHom x0 ∈ (X.subgroupOf M).map starHom := mem_map_of_mem _ hx
  have he := congrArg Subtype.val (starHom_pair x0 i j)
  change x0 * kernelValue (pairLabel i j) * x0⁻¹ =
    kernelValue (pairLabel ((starHom x0).val i) ((starHom x0).val j)) at he
  rw [hi _ hm,hj _ hm] at he
  exact congrArg (fun y : M => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)

private theorem centralizer_tetrad_action (X : Subgroup Model) (k : Fin 2)
    (hfixed : ∀ i : Fin 24,
      (∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i) ↔ ∃ j, tetrad k j = i)
    (c : M) (hc : (c : Model) ∈ centralizer (X : Set Model)) :
    ∃ f : Fin 4 → Fin 4, Function.Injective f ∧
      ∀ i, (starHom c).val (tetrad k i) = tetrad k (f i) := by
  have hcomm (p : StarGroup) (hp : p ∈ (X.subgroupOf M).map starHom) (j : Fin 24) :
      (starHom c).val (p.val j) = p.val ((starHom c).val j) := by
    obtain ⟨x,hx,rfl⟩ := hp
    have hh : Commute c x := Subtype.ext (hc x hx).symm
    exact congrArg (fun y : StarGroup => y.val j) (hh.map starHom).eq
  have he (i : Fin 4) : ∃ j, (starHom c).val (tetrad k i) = tetrad k j := by
    obtain ⟨j,hj⟩ := (hfixed _).mp (fun p hp => by
      rw [← hcomm p hp, (hfixed _).mpr ⟨i,rfl⟩ p hp])
    exact ⟨j,hj.symm⟩
  choose f hf using he
  refine ⟨f,?_,hf⟩
  intro i j hij
  apply tetrad_injective k
  apply (starHom c).val.injective
  rw [hf,hf,hij]

theorem centralInvolution_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (k : Fin 2)
    (hfixed : ∀ i : Fin 24,
      (∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i) ↔ ∃ j, tetrad k j = i)
    (hCM : centralizer (X : Set Model) ≤ M) :
    NonsingularC.centralInvolution ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) :
      c * NonsingularC.centralInvolution = NonsingularC.centralInvolution * c := by
    let c0 : M := ⟨c,hCM hc⟩
    obtain ⟨f,hf,hact⟩ := centralizer_tetrad_action X k hfixed c0 hc
    have he : c0 * kernelValue 818 * c0⁻¹ = kernelValue 818 := by
      rw [tetrad_product k]
      change (MulAut.conj c0).toMonoidHom (_ * _) = _
      rw [map_mul]
      change (c0 * _ * c0⁻¹) * (c0 * _ * c0⁻¹) = _
      rw [show c0 * kernelValue (pairLabel (tetrad k 0) (tetrad k 1)) * c0⁻¹ =
        kernelValue (pairLabel ((starHom c0).val (tetrad k 0)) ((starHom c0).val (tetrad k 1))) from
        congrArg Subtype.val (starHom_pair c0 (tetrad k 0) (tetrad k 1))]
      rw [show c0 * kernelValue (pairLabel (tetrad k 2) (tetrad k 3)) * c0⁻¹ =
        kernelValue (pairLabel ((starHom c0).val (tetrad k 2)) ((starHom c0).val (tetrad k 3))) from
        congrArg Subtype.val (starHom_pair c0 (tetrad k 2) (tetrad k 3))]
      rw [hact,hact,hact,hact,← kernelValue_xor,tetrad_label k f hf,← tetrad_product k]
    exact congrArg (fun y : M => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨fun x hx => hcomm x (X.le_centralizer hx),hcomm,by
      rw [← NonsingularC.centralInvolution_order]; exact pow_orderOf_eq_one _⟩

private theorem omega_fixes_tetrad (X : Subgroup Model) (hXM : X ≤ M)
    (k : Fin 2)
    (hfixed : ∀ i : Fin 24,
      (∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i) ↔ ∃ j, tetrad k j = i)
    (w : M) (hw : (w : Model) ∈ omegaCenterIn (centralizer (X : Set Model))) :
    ∀ i, (starHom w).val (tetrad k i) = tetrad k i := by
  intro i
  apply pair_detect k i
  intro j
  refine ⟨(starHom w).val (tetrad k j),?_⟩
  have hpair := pair_centralizes X hXM (tetrad k i) (tetrad k j)
    ((hfixed _).mpr ⟨i,rfl⟩) ((hfixed _).mpr ⟨j,rfl⟩)
  have hc : Commute w (kernelValue (pairLabel (tetrad k i) (tetrad k j))) :=
    Subtype.ext (((mem_omegaCenterIn_iff _ _).mp hw).2.1 _ hpair).symm
  have he := congrArg Subtype.val (starHom_pair w (tetrad k i) (tetrad k j))
  change w * kernelValue (pairLabel (tetrad k i) (tetrad k j)) * w⁻¹ =
    kernelValue (pairLabel ((starHom w).val (tetrad k i)) ((starHom w).val (tetrad k j))) at he
  rw [hc.eq,mul_inv_cancel_right] at he
  exact kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) he.symm

theorem centralInvolution_mem_radical (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (k : Fin 2)
    (hfixed : ∀ i : Fin 24,
      (∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i) ↔ ∃ j, tetrad k j = i)
    (hCM : centralizer (X : Set Model) ≤ M) :
    NonsingularC.centralInvolution ∈ NonsingularC.zeroWitness X := by
  have ht := centralInvolution_mem_omega X k hfixed hCM
  refine ⟨ht,?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1,outerValue_one_right]
  let w0 : M := ⟨w,hCM (map_subtype_le _ hw)⟩
  have hact := omega_fixes_tetrad X hXM k hfixed w0 hw
  have hw2 : orderOf w = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw) hw1
  have hp (i j : Fin 4) : Commute (kernelValue (pairLabel (tetrad k i) (tetrad k j)) : Model) w :=
    ((mem_omegaCenterIn_iff _ _).mp hw).2.1 _
      (pair_centralizes X hXM _ _ ((hfixed _).mpr ⟨i,rfl⟩) ((hfixed _).mpr ⟨j,rfl⟩))
  have hv (i j : Fin 4) (hij : i ≠ j) :
      outerValue w (kernelValue (pairLabel (tetrad k i) (tetrad k j)) : Model) = 0 := by
    have hd := (tetrad_injective k).ne hij
    exact (outerValue_eq_zero_iff _ _ hw1).mpr
      ((innerRelated_symm _ _ (pair_order _ _ hd) hw2 (hp i j)).mp
        (inner_of_star_fixed w0 _ _ hd (hact i) (hact j)))
  have hprod : NonsingularC.centralInvolution =
      (kernelValue (pairLabel (tetrad k 0) (tetrad k 1)) : Model) *
      (kernelValue (pairLabel (tetrad k 2) (tetrad k 3)) : Model) :=
    congrArg (fun y : M => (y : Model)) (tetrad_product k)
  have hz : outerValue w NonsingularC.centralInvolution = 0 := by
    rw [hprod,outerValue_mul_right w hw2 _ _ (hp 0 1).symm (hp 2 3).symm,
      hv 0 1 (by decide),hv 2 3 (by decide),add_zero]
  exact (outerValue_eq_zero_iff _ _ NonsingularC.centralInvolution_ne_one).mpr
    ((innerRelated_symm _ _ hw2 NonsingularC.centralInvolution_order
      (setLike_mul_comm hw ht)).mp ((outerValue_eq_zero_iff _ _ hw1).mp hz))

theorem fixed_tetrad_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (k : Fin 2)
    (hfixed : ∀ i : Fin 24,
      (∀ p ∈ (X.subgroupOf M).map starHom, p.val i = i) ↔ ∃ j, tetrad k j = i) :
    NonsingularC.zeroWitness X ≠ ⊥ ∧
      intrinsicElementaryForm (NonsingularC.zeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (NonsingularC.zeroWitness X : Set Model) := by
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  have ht := centralInvolution_mem_radical X (X.le_centralizer.trans hCM) k hfixed hCM
  exact ⟨fun he => NonsingularC.centralInvolution_ne_one (mem_bot.mp (he ▸ ht)),
    NonsingularC.zeroWitness_form X,NonsingularC.zeroWitness_normalizer X⟩

def rowMask : Fin 8 → Fin 3 → Fin 32 :=
  ![![16,6,0],![16,7,0],![16,9,0],![16,11,0],
    ![16,13,0],![16,14,0],![16,6,11],![16,7,9]]
def rowTetrad : Fin 8 → Fin 2 := ![0,1,1,0,0,1,0,1]
def rowGenerator (r : Fin 8) (j : Fin 3) : StarGroup :=
  binaryProduct NonsingularImages.FigureA.wholeGenerator
    (fun i => (rowMask r j).val.testBit i.val)
def rowImage (r : Fin 8) : Subgroup StarGroup := closure (Set.range (rowGenerator r))

theorem row_le_box (r : Fin 8) : rowImage r ≤ NonsingularImages.boxImage := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact binaryProduct_mem _ _ _ NonsingularImages.FigureA.wholeGenerator_mem

private theorem generator_common_fixed : ∀ (r : Fin 8) (i : Fin 24),
    (∀ j, (rowGenerator r j).val i = i) ↔ ∃ j, tetrad (rowTetrad r) j = i := by
  decide +kernel

theorem row_common_fixed (r : Fin 8) (i : Fin 24) :
    (∀ p ∈ rowImage r, p.val i = i) ↔ ∃ j, tetrad (rowTetrad r) j = i := by
  rw [← generator_common_fixed]
  change rowImage r ≤ MulAction.stabilizer StarGroup i ↔ _
  rw [rowImage,closure_le,Set.range_subset_iff]
  rfl

theorem pair_mem_row (r : Fin 8) : pairPermutation ∈ rowImage r := by
  have he : rowGenerator r 0 = pairPermutation := by
    apply Subtype.ext
    revert r
    decide +kernel
  rw [← he]
  exact subset_closure (Set.mem_range_self 0)

theorem source_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 8)
    (hrow : (X.subgroupOf M).map starHom = rowImage r) :
    NonsingularC.zeroWitness X ≠ ⊥ ∧
      intrinsicElementaryForm (NonsingularC.zeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (NonsingularC.zeroWitness X : Set Model) := by
  apply fixed_tetrad_zeroWitness X hs (rowTetrad r)
  intro i
  rw [hrow]
  exact row_common_fixed r i

theorem maximal_source_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 8)
    (hrow : (X.subgroupOf M).map starHom = rowImage r)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    NonsingularC.zeroWitness X ≠ ⊥ ∧
      intrinsicElementaryForm (NonsingularC.zeroWitness X) = 0 ∧
      normalizer (X : Set Model) = normalizer (NonsingularC.zeroWitness X : Set Model) := by
  obtain ⟨hne,hzero,hle⟩ := source_zeroWitness X hs r hrow
  exact ⟨hne,hzero,hmax.eq_of_le
    ⟨NonsingularC.zeroWitness X,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hle⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxTetrads
