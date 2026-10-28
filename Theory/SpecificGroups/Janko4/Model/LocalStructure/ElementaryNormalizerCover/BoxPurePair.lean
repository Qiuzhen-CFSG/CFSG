module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualCore

/-!
# A zero-form witness for the cyclic residual box image

The eight transposition pairs of the marked permutation yield eight kernel
involutions permuted by the full centralizer. Its two-core fixes another one
besides the seed because the remaining set has odd cardinality seven. Both
involutions lie in the central omega of that two-core. Three fixed half-octad
masks force every central-omega element to have the same intrinsic character
on the eight pair involutions, so their nontrivial product lies in the form
radical. This canonical radical is preserved by the entire normalizer.

The maximal-two-local consumer upgrades containment to equality. The proof
uses only the literal image and seed; no signed-lift identification or purity
hypothesis is needed. Source motivation: Kleidman--Wilson (1988), Section 2.3,
Proposition 2.3.2 and Figure 1(b,c), printed pp.486,492.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxPurePair
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open ElementaryEightGeometry M22Images.KernelAction BoxImages BoxResidual
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def octPair : Fin 8 → Fin 24 × Fin 24 :=
  ![(0,1),(2,3),(6,23),(9,22),(10,18),(11,12),(13,21),(19,20)]
def octLabel (i : Fin 8) : ℕ := pairLabel (octPair i).1 (octPair i).2
def octValue (i : Fin 8) : Model := kernelValue (octLabel i)
def quadIndex : Fin 3 → Fin 4 → Fin 8 := ![![0,2,5,6],![0,1,5,7],![0,3,4,5]]
def halfMask : Fin 3 → ℕ := ![820,1256,132]
private def chosenPoint (i : Fin 8) (b : Bool) : Fin 24 :=
  if b then (octPair i).2 else (octPair i).1

private theorem oct_distinct : ∀ i, (octPair i).1 ≠ (octPair i).2 := by decide +kernel
private theorem labels_injective : Function.Injective octLabel := by decide +kernel
private theorem half_product : ∀ r, Nat.xor
    (pairLabel (octPair (quadIndex r 0)).1 (octPair (quadIndex r 1)).1)
    (pairLabel (octPair (quadIndex r 2)).1 (octPair (quadIndex r 3)).1) = halfMask r := by decide +kernel
private theorem half_uniform : ∀ f : Fin 8 → Bool,
    (∀ r : Fin 3, Nat.xor
      (pairLabel (chosenPoint (quadIndex r 0) (f (quadIndex r 0)))
        (chosenPoint (quadIndex r 1) (f (quadIndex r 1))))
      (pairLabel (chosenPoint (quadIndex r 2) (f (quadIndex r 2)))
        (chosenPoint (quadIndex r 3) (f (quadIndex r 3)))) = halfMask r) →
      ∀ i, f i = f 0 := by decide +kernel
private theorem pair_endpoints : ∀ (i : Fin 8) (a b : Fin 24),
    pairLabel a b = octLabel i →
      (a = (octPair i).1 ∧ b = (octPair i).2) ∨
      (a = (octPair i).2 ∧ b = (octPair i).1) := by decide +kernel
private theorem pair_fixed : ∀ (i : Fin 8) (j : Fin 3),
    SylowCore.starMask (BoxResidual.generator 0 j) (octLabel i) = octLabel i := by decide +kernel
private theorem half_fixed : ∀ (r : Fin 3) (j : Fin 3),
    SylowCore.starMask (BoxResidual.generator 0 j) (halfMask r) = halfMask r := by decide +kernel

private theorem mask_mem_core (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0)
    (m : Fin 2048) (hm : ∀ j, SylowCore.starMask (BoxResidual.generator 0 j) m.val = m.val) :
    (kernelValue m.val : Model) ∈ (centralizer (X : Set Model)).pCoreIn 2 := by
  apply kernelValue_mem_core_of_fixed_image X hs m.val
  rw [hrow]
  exact (starMask_closure_fixed_iff _ m).mpr hm

private theorem octValue_mem_core (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0) (i : Fin 8) :
    octValue i ∈ (centralizer (X : Set Model)).pCoreIn 2 :=
  mask_mem_core X hs hrow ⟨octLabel i,pairLabel_lt _ _⟩ (pair_fixed i)

private theorem octValue_zero : octValue 0 = (seed : Model) := by
  change (kernelValue 1 : Model) = _
  exact congrArg (fun x : M => (x : Model)) (maskValue_one _ _)

private theorem octValue_injective : Function.Injective octValue := by
  intro i j h
  exact labels_injective (kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) (Subtype.ext h))

private theorem element_swap : ∀ i b,
    (element 0 1).val (chosenPoint i b) = chosenPoint i (!b) := by decide +kernel
private theorem pair_signature : ∀ i k,
    (element 0 k).val (octPair i).1 = (octPair i).1 ↔
      (element 0 k).val 0 = 0 := by decide +kernel
private theorem signature_detect : ∀ y,
    (∀ k : Fin 8, (element 0 k).val y = y ↔
      (element 0 k).val 0 = 0) →
      ∃ (i : Fin 8) (b : Bool), chosenPoint i b = y := by decide +kernel
private theorem chosen_label : ∀ i b,
    pairLabel (chosenPoint i b) (chosenPoint i (!b)) = octLabel i := by decide +kernel

private theorem centralizer_oct_action (X : Subgroup Model)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0)
    (c : M) (hc : (c : Model) ∈ centralizer (X : Set Model)) (i : Fin 8) :
    ∃ j : Fin 8, c * kernelValue (octLabel i) * c⁻¹ = kernelValue (octLabel j) := by
  have hact (k : Fin 8) (a : Fin 24) :
      (starHom c).val ((element 0 k).val a) =
        (element 0 k).val ((starHom c).val a) := by
    obtain ⟨x,hx,hxk⟩ := hrow ▸ element_mem 0 k
    have hh : Commute c x := Subtype.ext (hc x hx).symm
    have he := congrArg (fun p : StarGroup => p.val a) (hh.map starHom).eq
    simpa only [hxk,coe_mul,Equiv.Perm.mul_apply] using he
  have hsig (k : Fin 8) :
      (element 0 k).val ((starHom c).val (octPair i).1) =
          (starHom c).val (octPair i).1 ↔ (element 0 k).val 0 = 0 := by
    rw [← hact]
    exact (starHom c).val.injective.eq_iff.trans (pair_signature i k)
  obtain ⟨j,b,hj⟩ := signature_detect _ hsig
  have ha : (starHom c).val (octPair i).1 = chosenPoint j b := hj.symm
  have hb : (starHom c).val (octPair i).2 = chosenPoint j (!b) := by
    have hs : (element 0 1).val (octPair i).1 = (octPair i).2 := element_swap i false
    rw [← hs,hact,ha,element_swap]
  refine ⟨j,?_⟩
  have he := congrArg Subtype.val (starHom_pair c (octPair i).1 (octPair i).2)
  change c * kernelValue (octLabel i) * c⁻¹ = _ at he
  rw [ha,hb,chosen_label] at he
  exact he

private def seven : Finset Model := by
  classical
  exact Finset.univ.image (fun i : Fin 7 => octValue i.succ)
private theorem seven_card : seven.card = 7 := by
  classical
  change (Finset.image (octValue ∘ Fin.succ) Finset.univ).card = 7
  rw [Finset.card_image_of_injective _ (octValue_injective.comp (Fin.succ_injective 7))]
  decide

private theorem seven_invariant (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0) :
    ∀ c ∈ centralizer (X : Set Model), ∀ t ∈ seven, c*t*c⁻¹ ∈ seven := by
  classical
  intro c hc t ht
  unfold seven at ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  let c0 : M := ⟨c,hCM hc⟩
  obtain ⟨j,hj⟩ := centralizer_oct_action X hrow c0 hc i.succ
  have hj' : c * octValue i.succ * c⁻¹ = octValue j :=
    congrArg (fun x : M => (x : Model)) hj
  have hj0 : j ≠ 0 := by
    intro he
    have hcseed := hc seed hs
    have heq : octValue i.succ = octValue 0 := by
      apply (MulAut.conj c).injective
      change c * _ * c⁻¹ = c * _ * c⁻¹
      rw [hj',he,octValue_zero,← hcseed,mul_inv_cancel_right]
    exact Fin.succ_ne_zero i (octValue_injective heq)
  obtain ⟨k,hk⟩ := Fin.exists_succ_eq.mpr hj0
  rw [hj',← hk]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩

private theorem exists_other_oct_mem_coreOmega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0) :
    ∃ i : Fin 7, octValue i.succ ∈ coreOmega X := by
  let Q := (centralizer (X : Set Model)).pCoreIn 2
  obtain ⟨t,ht,hct⟩ := exists_fixed_of_odd_conjugation Q (isPGroup_pCoreIn 2 _)
    seven (by rw [seven_card]; decide)
    (fun c hc => seven_invariant X hs hrow c (pCoreIn_le 2 _ hc))
  classical
  unfold seven at ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  refine ⟨i,(mem_omegaCenterIn_iff _ _).mpr ⟨octValue_mem_core X hs hrow i.succ,hct,?_⟩⟩
  rw [← pair_order (octPair i.succ).1 (octPair i.succ).2 (oct_distinct i.succ)]
  exact pow_orderOf_eq_one _

private theorem coreOmega_pair_inner (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0)
    (w : M) (hw : (w : Model) ∈ coreOmega X) (i : Fin 8) :
    InnerRelated (octValue 0) (w : Model) ↔ InnerRelated (octValue i) (w : Model) := by
  have hcomm (m : Fin 2048)
      (hm : ∀ j, SylowCore.starMask (BoxResidual.generator 0 j) m.val = m.val) :
      Commute w (kernelValue m.val) := by
    apply Subtype.ext
    exact (((mem_omegaCenterIn_iff _ _).mp hw).2.1 _ (mask_mem_core X hs hrow m hm)).symm
  have hpair (j : Fin 8) :
      pairLabel ((starHom w).val (octPair j).1) ((starHom w).val (octPair j).2) = octLabel j := by
    have he := congrArg Subtype.val (starHom_pair w (octPair j).1 (octPair j).2)
    change w * kernelValue (octLabel j) * w⁻¹ = _ at he
    rw [(hcomm ⟨octLabel j,pairLabel_lt _ _⟩ (pair_fixed j)).eq,mul_inv_cancel_right] at he
    exact kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) he.symm
  have hchoice (j : Fin 8) : ∃ b : Bool,
      (starHom w).val (octPair j).1 = chosenPoint j b ∧
      (starHom w).val (octPair j).2 = chosenPoint j (!b) := by
    rcases pair_endpoints j _ _ (hpair j) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨false,ha,hb⟩
    · exact ⟨true,ha,hb⟩
  choose f hf using hchoice
  have hhalf (r : Fin 3) : Nat.xor
      (pairLabel (chosenPoint (quadIndex r 0) (f (quadIndex r 0)))
        (chosenPoint (quadIndex r 1) (f (quadIndex r 1))))
      (pairLabel (chosenPoint (quadIndex r 2) (f (quadIndex r 2)))
        (chosenPoint (quadIndex r 3) (f (quadIndex r 3)))) = halfMask r := by
    have he0 := congrArg Subtype.val (starHom_pair w (octPair (quadIndex r 0)).1 (octPair (quadIndex r 1)).1)
    have he1 := congrArg Subtype.val (starHom_pair w (octPair (quadIndex r 2)).1 (octPair (quadIndex r 3)).1)
    change w * kernelValue (pairLabel (octPair (quadIndex r 0)).1 (octPair (quadIndex r 1)).1) * w⁻¹ = _ at he0
    change w * kernelValue (pairLabel (octPair (quadIndex r 2)).1 (octPair (quadIndex r 3)).1) * w⁻¹ = _ at he1
    have hc : Commute w (kernelValue (halfMask r)) :=
      hcomm ⟨halfMask r,by fin_cases r <;> decide⟩ (half_fixed r)
    have hm : kernelValue (halfMask r) =
        kernelValue (pairLabel (octPair (quadIndex r 0)).1 (octPair (quadIndex r 1)).1) *
          kernelValue (pairLabel (octPair (quadIndex r 2)).1 (octPair (quadIndex r 3)).1) := by
      rw [← kernelValue_xor,half_product]
    have he : kernelValue (halfMask r) = kernelValue (Nat.xor
        (pairLabel (chosenPoint (quadIndex r 0) (f (quadIndex r 0)))
          (chosenPoint (quadIndex r 1) (f (quadIndex r 1))))
        (pairLabel (chosenPoint (quadIndex r 2) (f (quadIndex r 2)))
          (chosenPoint (quadIndex r 3) (f (quadIndex r 3))))) := by
      calc
        kernelValue (halfMask r) = (MulAut.conj w).toMonoidHom (kernelValue (halfMask r)) := by
          change _ = w * _ * w⁻¹
          rw [hc.eq,mul_inv_cancel_right]
        _ = _ := by
          rw [hm,map_mul]
          change (w * _ * w⁻¹) * (w * _ * w⁻¹) = _
          rw [he0,he1,(hf (quadIndex r 0)).1,(hf (quadIndex r 1)).1,
            (hf (quadIndex r 2)).1,(hf (quadIndex r 3)).1,← kernelValue_xor]
    have hb : ∀ (r : Fin 3) (f : Fin 8 → Bool), Nat.xor
        (pairLabel (chosenPoint (quadIndex r 0) (f (quadIndex r 0)))
          (chosenPoint (quadIndex r 1) (f (quadIndex r 1))))
        (pairLabel (chosenPoint (quadIndex r 2) (f (quadIndex r 2)))
          (chosenPoint (quadIndex r 3) (f (quadIndex r 3)))) < 2048 := by decide +kernel
    exact kernelValue_injective (hb r f) (by fin_cases r <;> decide) he.symm
  have hfi := half_uniform f hhalf i
  have h0 := hf 0
  have hi := hf i
  rw [hfi] at hi
  cases h : f 0
  · simp only [h,chosenPoint,Bool.false_eq_true,if_false,Bool.not_false,if_true] at h0 hi
    exact iff_of_true (inner_of_star_fixed w _ _ (oct_distinct 0) h0.1 h0.2)
      (inner_of_star_fixed w _ _ (oct_distinct i) hi.1 hi.2)
  · simp only [h,chosenPoint,if_true,Bool.not_true,Bool.false_eq_true,if_false] at h0 hi
    exact iff_of_false (LinearFive.Geometry.not_inner_of_star_swap w _ _ (oct_distinct 0) h0.1 h0.2)
      (LinearFive.Geometry.not_inner_of_star_swap w _ _ (oct_distinct i) hi.1 hi.2)

/-- Row zero admits a nontrivial intrinsic radical in the central omega of
its full centralizer's two-core. The entire normalizer preserves this witness. -/
theorem source_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = residualImage 0) :
    coreZeroWitness X ≠ ⊥ ∧ intrinsicElementaryForm (coreZeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (coreZeroWitness X : Set Model) := by
  obtain ⟨i,hi⟩ := exists_other_oct_mem_coreOmega X hs hrow
  have h0 : octValue 0 ∈ coreOmega X := by rw [octValue_zero]; exact elementary_le_coreOmega X hs
  let t := octValue 0 * octValue i.succ
  have ht : t ∈ coreOmega X := (coreOmega X).mul_mem h0 hi
  have hne : t ≠ 1 := by
    intro he
    have hsq : octValue i.succ * octValue i.succ = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hi
    have heq := congrArg (fun x : Model => x * octValue i.succ) he
    change (octValue 0 * octValue i.succ) * octValue i.succ = 1 * octValue i.succ at heq
    rw [mul_assoc,hsq,mul_one,one_mul] at heq
    exact Fin.succ_ne_zero i (octValue_injective heq).symm
  have hrad : t ∈ coreZeroWitness X := by
    refine ⟨ht,?_⟩
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1,outerValue_one_right]
    have hCM : centralizer (X : Set Model) ≤ M :=
      (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
    let w0 : M := ⟨w,hCM (pCoreIn_le 2 _ (map_subtype_le _ hw))⟩
    have hw2 : orderOf w = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw) hw1
    have hti2 : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht) hne
    have ho (j : Fin 8) : orderOf (octValue j) = 2 := pair_order _ _ (oct_distinct j)
    have hc0 : Commute w (octValue 0) := setLike_mul_comm hw h0
    have hci : Commute w (octValue i.succ) := setLike_mul_comm hw hi
    have hh := coreOmega_pair_inner X hs hrow w0 hw i.succ
    have he : InnerRelated w (octValue 0) ↔ InnerRelated w (octValue i.succ) :=
      (innerRelated_symm _ _ (ho 0) hw2 hc0.symm).symm.trans
        (hh.trans (innerRelated_symm _ _ (ho i.succ) hw2 hci.symm))
    have hv : outerValue w (octValue 0) = outerValue w (octValue i.succ) := by
      simp only [outerValue,hw1,false_or]
      rw [he]
    have hz : outerValue w t = 0 := by
      rw [show t = octValue 0 * octValue i.succ from rfl,
        outerValue_mul_right w hw2 _ _ hc0 hci,hv,← two_mul]
      rw [show (2 : ZMod 2) = 0 from rfl,zero_mul]
    exact (outerValue_eq_zero_iff _ _ hne).mpr
      ((innerRelated_symm _ _ hw2 hti2 (setLike_mul_comm hw ht)).mp
        ((outerValue_eq_zero_iff _ _ hw1).mp hz))
  exact ⟨fun hz => hne (mem_bot.mp (hz ▸ hrad)),coreZeroWitness_form X,coreZeroWitness_normalizer X⟩

/-- Maximality upgrades the row-zero centralizer-core radical to its whole
normalizer. This is the actual pure-second branch consumer for the final cover. -/
theorem source_pair_maximal_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (himage : (X.subgroupOf M).map starHom = BoxImages.residualImage 0)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) = normalizer (Z : Set Model) := by
  obtain ⟨hne,hzero,hN⟩ := source_zeroWitness X hs himage
  exact ⟨coreZeroWitness X,hne,inferInstance,hzero,
    hmax.eq_of_le ⟨coreZeroWitness X,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hN⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxPurePair
