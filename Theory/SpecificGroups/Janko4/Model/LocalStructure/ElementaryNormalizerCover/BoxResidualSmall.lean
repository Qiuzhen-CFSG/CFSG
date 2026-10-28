module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualCore

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open ElementaryEightGeometry M22Images.KernelAction BoxImages
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def smallRow (r : Fin 3) : Fin 8 := ⟨r.val+1,by omega⟩
def quadPair : Fin 3 → Fin 4 → Fin 24 × Fin 24 :=
  ![![(0,1),(6,23),(11,12),(13,21)],
    ![(0,1),(2,3),(11,12),(19,20)],
    ![(0,1),(9,22),(10,18),(11,12)]]
def quadLabel (r : Fin 3) (i : Fin 4) : ℕ := pairLabel (quadPair r i).1 (quadPair r i).2
def quadValue (r : Fin 3) (i : Fin 4) : Model := kernelValue (quadLabel r i)
def halfMask : Fin 3 → ℕ := ![820,1256,132]
private def chosenPoint (r : Fin 3) (i : Fin 4) (b : Bool) : Fin 24 :=
  if b then (quadPair r i).2 else (quadPair r i).1

private theorem quad_distinct : ∀ r i, (quadPair r i).1 ≠ (quadPair r i).2 := by decide +kernel
private theorem labels_injective : ∀ r, Function.Injective (quadLabel r) := by decide +kernel
private theorem label_zero : ∀ r, quadLabel r 0 = 1 := by decide +kernel
private theorem half_product : ∀ r, Nat.xor
    (pairLabel (quadPair r 0).1 (quadPair r 1).1)
    (pairLabel (quadPair r 2).1 (quadPair r 3).1) = halfMask r := by decide +kernel
private theorem half_uniform : ∀ (r : Fin 3) (f : Fin 4 → Bool),
    Nat.xor (pairLabel (chosenPoint r 0 (f 0)) (chosenPoint r 1 (f 1)))
      (pairLabel (chosenPoint r 2 (f 2)) (chosenPoint r 3 (f 3))) = halfMask r →
      ∀ i, f i = f 0 := by decide +kernel
private theorem pair_endpoints : ∀ (r : Fin 3) (i : Fin 4) (a b : Fin 24),
    pairLabel a b = quadLabel r i →
      (a = (quadPair r i).1 ∧ b = (quadPair r i).2) ∨
      (a = (quadPair r i).2 ∧ b = (quadPair r i).1) := by decide +kernel
private theorem pair_fixed : ∀ (r : Fin 3) (i : Fin 4) (j : Fin 3),
    SylowCore.starMask (generator (smallRow r) j) (quadLabel r i) = quadLabel r i := by decide +kernel
private theorem half_fixed : ∀ (r : Fin 3) (j : Fin 3),
    SylowCore.starMask (generator (smallRow r) j) (halfMask r) = halfMask r := by decide +kernel

private theorem mask_mem_core (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r))
    (m : Fin 2048) (hm : ∀ j, SylowCore.starMask (generator (smallRow r) j) m.val = m.val) :
    (kernelValue m.val : Model) ∈ (centralizer (X : Set Model)).pCoreIn 2 := by
  apply kernelValue_mem_core_of_fixed_image X hs m.val
  rw [hrow]
  exact (starMask_closure_fixed_iff _ m).mpr hm

theorem quadValue_mem_core (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r)) (i : Fin 4) :
    quadValue r i ∈ (centralizer (X : Set Model)).pCoreIn 2 :=
  mask_mem_core X hs r hrow ⟨quadLabel r i,pairLabel_lt _ _⟩ (pair_fixed r i)

theorem quadValue_zero (r : Fin 3) : quadValue r 0 = (seed : Model) := by
  change (kernelValue (quadLabel r 0) : Model) = _
  rw [label_zero]
  exact congrArg (fun x : M => (x : Model)) (maskValue_one _ _)

theorem quadValue_injective (r : Fin 3) : Function.Injective (quadValue r) := by
  intro i j h
  exact labels_injective r (kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) (Subtype.ext h))

private theorem element_swap : ∀ r i b,
    (element (smallRow r) 1).val (chosenPoint r i b) = chosenPoint r i (!b) := by decide +kernel
private theorem pair_signature : ∀ r i k,
    (element (smallRow r) k).val (quadPair r i).1 = (quadPair r i).1 ↔
      (element (smallRow r) k).val 0 = 0 := by decide +kernel
private theorem signature_detect : ∀ r y,
    (∀ k : Fin 8, (element (smallRow r) k).val y = y ↔
      (element (smallRow r) k).val 0 = 0) →
      ∃ (i : Fin 4) (b : Bool), chosenPoint r i b = y := by decide +kernel
private theorem chosen_label : ∀ r i b,
    pairLabel (chosenPoint r i b) (chosenPoint r i (!b)) = quadLabel r i := by decide +kernel

private theorem centralizer_quad_action (X : Subgroup Model)
    (r : Fin 3) (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r))
    (c : M) (hc : (c : Model) ∈ centralizer (X : Set Model)) (i : Fin 4) :
    ∃ j : Fin 4, c * kernelValue (quadLabel r i) * c⁻¹ = kernelValue (quadLabel r j) := by
  have hact (k : Fin 8) (a : Fin 24) :
      (starHom c).val ((element (smallRow r) k).val a) =
        (element (smallRow r) k).val ((starHom c).val a) := by
    obtain ⟨x,hx,hxk⟩ := hrow ▸ element_mem (smallRow r) k
    have hh : Commute c x := Subtype.ext (hc x hx).symm
    have he := congrArg (fun p : StarGroup => p.val a) (hh.map starHom).eq
    simpa only [hxk,coe_mul,Equiv.Perm.mul_apply] using he
  have hsig (k : Fin 8) :
      (element (smallRow r) k).val ((starHom c).val (quadPair r i).1) =
          (starHom c).val (quadPair r i).1 ↔ (element (smallRow r) k).val 0 = 0 := by
    rw [← hact]
    exact (starHom c).val.injective.eq_iff.trans (pair_signature r i k)
  obtain ⟨j,b,hj⟩ := signature_detect r _ hsig
  have ha : (starHom c).val (quadPair r i).1 = chosenPoint r j b := hj.symm
  have hb : (starHom c).val (quadPair r i).2 = chosenPoint r j (!b) := by
    have hs : (element (smallRow r) 1).val (quadPair r i).1 = (quadPair r i).2 :=
      element_swap r i false
    rw [← hs,hact,ha,element_swap]
  refine ⟨j,?_⟩
  have he := congrArg Subtype.val (starHom_pair c (quadPair r i).1 (quadPair r i).2)
  change c * kernelValue (quadLabel r i) * c⁻¹ = _ at he
  rw [ha,hb,chosen_label] at he
  exact he

private def triple (r : Fin 3) : Finset Model := by
  classical
  exact Finset.univ.image (fun i : Fin 3 => quadValue r i.succ)
private theorem triple_card (r : Fin 3) : (triple r).card = 3 := by
  classical
  change (Finset.image (quadValue r ∘ Fin.succ) Finset.univ).card = 3
  rw [Finset.card_image_of_injective _ ((quadValue_injective r).comp (Fin.succ_injective 3))]
  decide

private theorem triple_invariant (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r)) :
    ∀ c ∈ centralizer (X : Set Model), ∀ t ∈ triple r, c*t*c⁻¹ ∈ triple r := by
  classical
  intro c hc t ht
  unfold triple at ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  let c0 : M := ⟨c,hCM hc⟩
  obtain ⟨j,hj⟩ := centralizer_quad_action X r hrow c0 hc i.succ
  have hj' : c * quadValue r i.succ * c⁻¹ = quadValue r j :=
    congrArg (fun x : M => (x : Model)) hj
  have hj0 : j ≠ 0 := by
    intro he
    have hcseed := hc seed hs
    have heq : quadValue r i.succ = quadValue r 0 := by
      apply (MulAut.conj c).injective
      change c * _ * c⁻¹ = c * _ * c⁻¹
      rw [hj',he,quadValue_zero,← hcseed,mul_inv_cancel_right]
    exact Fin.succ_ne_zero i (quadValue_injective r heq)
  obtain ⟨k,hk⟩ := Fin.exists_succ_eq.mpr hj0
  rw [hj',← hk]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩

theorem exists_other_quad_mem_coreOmega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r)) :
    ∃ i : Fin 3, quadValue r i.succ ∈ coreOmega X := by
  let Q := (centralizer (X : Set Model)).pCoreIn 2
  obtain ⟨t,ht,hct⟩ := exists_fixed_of_odd_conjugation Q (isPGroup_pCoreIn 2 _)
    (triple r) (by rw [triple_card]; decide)
    (fun c hc => triple_invariant X hs r hrow c (pCoreIn_le 2 _ hc))
  classical
  unfold triple at ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  refine ⟨i,(mem_omegaCenterIn_iff _ _).mpr ⟨quadValue_mem_core X hs r hrow i.succ,hct,?_⟩⟩
  rw [← pair_order (quadPair r i.succ).1 (quadPair r i.succ).2 (quad_distinct r i.succ)]
  exact pow_orderOf_eq_one _


private theorem coreOmega_pair_inner (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r))
    (w : M) (hw : (w : Model) ∈ coreOmega X) (i : Fin 4) :
    InnerRelated (quadValue r 0) (w : Model) ↔ InnerRelated (quadValue r i) (w : Model) := by
  have hcomm (m : Fin 2048)
      (hm : ∀ j, SylowCore.starMask (generator (smallRow r) j) m.val = m.val) :
      Commute w (kernelValue m.val) := by
    apply Subtype.ext
    exact (((mem_omegaCenterIn_iff _ _).mp hw).2.1 _ (mask_mem_core X hs r hrow m hm)).symm
  have hpair (j : Fin 4) :
      pairLabel ((starHom w).val (quadPair r j).1) ((starHom w).val (quadPair r j).2) = quadLabel r j := by
    have he := congrArg Subtype.val (starHom_pair w (quadPair r j).1 (quadPair r j).2)
    change w * kernelValue (quadLabel r j) * w⁻¹ = _ at he
    rw [(hcomm ⟨quadLabel r j,pairLabel_lt _ _⟩ (pair_fixed r j)).eq,mul_inv_cancel_right] at he
    exact kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) he.symm
  have hchoice (j : Fin 4) : ∃ b : Bool,
      (starHom w).val (quadPair r j).1 = chosenPoint r j b ∧
      (starHom w).val (quadPair r j).2 = chosenPoint r j (!b) := by
    rcases pair_endpoints r j _ _ (hpair j) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨false,ha,hb⟩
    · exact ⟨true,ha,hb⟩
  choose f hf using hchoice
  have hhalf : Nat.xor (pairLabel (chosenPoint r 0 (f 0)) (chosenPoint r 1 (f 1)))
      (pairLabel (chosenPoint r 2 (f 2)) (chosenPoint r 3 (f 3))) = halfMask r := by
    have he0 := congrArg Subtype.val (starHom_pair w (quadPair r 0).1 (quadPair r 1).1)
    have he1 := congrArg Subtype.val (starHom_pair w (quadPair r 2).1 (quadPair r 3).1)
    change w * kernelValue (pairLabel (quadPair r 0).1 (quadPair r 1).1) * w⁻¹ = _ at he0
    change w * kernelValue (pairLabel (quadPair r 2).1 (quadPair r 3).1) * w⁻¹ = _ at he1
    have hc : Commute w (kernelValue (halfMask r)) :=
      hcomm ⟨halfMask r,by fin_cases r <;> decide⟩ (half_fixed r)
    have hm : kernelValue (halfMask r) =
        kernelValue (pairLabel (quadPair r 0).1 (quadPair r 1).1) *
          kernelValue (pairLabel (quadPair r 2).1 (quadPair r 3).1) := by
      rw [← kernelValue_xor,half_product]
    have he : kernelValue (halfMask r) = kernelValue
        (Nat.xor (pairLabel (chosenPoint r 0 (f 0)) (chosenPoint r 1 (f 1)))
          (pairLabel (chosenPoint r 2 (f 2)) (chosenPoint r 3 (f 3)))) := by
      calc
        kernelValue (halfMask r) = (MulAut.conj w).toMonoidHom (kernelValue (halfMask r)) := by
          change _ = w * _ * w⁻¹
          rw [hc.eq,mul_inv_cancel_right]
        _ = _ := by
          rw [hm,map_mul]
          change (w * _ * w⁻¹) * (w * _ * w⁻¹) = _
          rw [he0,he1,(hf 0).1,(hf 1).1,(hf 2).1,(hf 3).1,← kernelValue_xor]
    have hb : ∀ (r : Fin 3) (f : Fin 4 → Bool), Nat.xor
        (pairLabel (chosenPoint r 0 (f 0)) (chosenPoint r 1 (f 1)))
        (pairLabel (chosenPoint r 2 (f 2)) (chosenPoint r 3 (f 3))) < 2048 := by decide +kernel
    exact kernelValue_injective (hb r f) (by fin_cases r <;> decide) he.symm
  have hfi := half_uniform r f hhalf i
  have h0 := hf 0
  have hi := hf i
  rw [hfi] at hi
  cases h : f 0
  · simp only [h,chosenPoint,Bool.false_eq_true,if_false,Bool.not_false,if_true] at h0 hi
    exact iff_of_true (inner_of_star_fixed w _ _ (quad_distinct r 0) h0.1 h0.2)
      (inner_of_star_fixed w _ _ (quad_distinct r i) hi.1 hi.2)
  · simp only [h,chosenPoint,if_true,Bool.not_true,Bool.false_eq_true,if_false] at h0 hi
    exact iff_of_false (LinearFive.Geometry.not_inner_of_star_swap w _ _ (quad_distinct r 0) h0.1 h0.2)
      (LinearFive.Geometry.not_inner_of_star_swap w _ _ (quad_distinct r i) hi.1 hi.2)

/-- The odd orbit supplies a second core-central pair. Its product with the
seed is a nonzero radical element, since the half-octad synchronizes their
characters on the entire central omega of the two-core. -/
theorem small_row_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r)) :
    coreZeroWitness X ≠ ⊥ ∧ intrinsicElementaryForm (coreZeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (coreZeroWitness X : Set Model) := by
  obtain ⟨i,hi⟩ := exists_other_quad_mem_coreOmega X hs r hrow
  have h0 : quadValue r 0 ∈ coreOmega X := by rw [quadValue_zero]; exact elementary_le_coreOmega X hs
  let t := quadValue r 0 * quadValue r i.succ
  have ht : t ∈ coreOmega X := (coreOmega X).mul_mem h0 hi
  have hne : t ≠ 1 := by
    intro he
    have hsq : quadValue r i.succ * quadValue r i.succ = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hi
    have heq := congrArg (fun x : Model => x * quadValue r i.succ) he
    change (quadValue r 0 * quadValue r i.succ) * quadValue r i.succ = 1 * quadValue r i.succ at heq
    rw [mul_assoc,hsq,mul_one,one_mul] at heq
    exact Fin.succ_ne_zero i ((quadValue_injective r heq).symm)
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
    have ho (j : Fin 4) : orderOf (quadValue r j) = 2 :=
      pair_order _ _ (quad_distinct r j)
    have hc0 : Commute w (quadValue r 0) := setLike_mul_comm hw h0
    have hci : Commute w (quadValue r i.succ) := setLike_mul_comm hw hi
    have hh := coreOmega_pair_inner X hs r hrow w0 hw i.succ
    have he : InnerRelated w (quadValue r 0) ↔ InnerRelated w (quadValue r i.succ) :=
      (innerRelated_symm _ _ (ho 0) hw2 hc0.symm).symm.trans
        (hh.trans (innerRelated_symm _ _ (ho i.succ) hw2 hci.symm))
    have hv : outerValue w (quadValue r 0) = outerValue w (quadValue r i.succ) := by
      simp only [outerValue,hw1,false_or]
      rw [he]
    have hz : outerValue w t = 0 := by
      rw [show t = quadValue r 0 * quadValue r i.succ from rfl,
        outerValue_mul_right w hw2 _ _ hc0 hci,hv,← two_mul]
      rw [show (2 : ZMod 2) = 0 from rfl,zero_mul]
    exact (outerValue_eq_zero_iff _ _ hne).mpr
      ((innerRelated_symm _ _ hw2 hti2 (setLike_mul_comm hw ht)).mp
        ((outerValue_eq_zero_iff _ _ hw1).mp hz))
  exact ⟨fun hz => hne (mem_bot.mp (hz ▸ hrad)),coreZeroWitness_form X,coreZeroWitness_normalizer X⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual

