module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Common
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
The literal seed and pair have distinct full centralizers. The explicit
odd-product conjugator transports the max2 generators into the full pair
centralizer. These marking and membership facts use the original matrix
carrier throughout. Source context: GLS3 Table 5.3i and ATLAS J4G1-max1W1.
-/
public section
namespace Janko4.AdequateLocal
open Subgroup Cardinality Simplicity.Max1Fusion Max1AmalgamRigidity Certificates
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed

abbrev L : Subgroup Model := M ⊔ C

theorem M_le_L : M ≤ L := le_sup_left
theorem C_le_L : C ≤ L := le_sup_right

theorem seed_mem_E : seed ∈ E :=
  mem_map.mpr ⟨localKernelSeed matrixA_mul_self matrixB_pow_four,
    localKernelSeed_mem matrixA_mul_self matrixB_pow_four, rfl⟩

theorem seed_mem_L : seed ∈ L := M_le_L (E_le_M seed_mem_E)
theorem pair_mem_L : pair ∈ L := M_le_L (E_le_M v_mem_E)

theorem seed_order : orderOf seed = 2 := InvolutionCentralizers.Second.seed_order

theorem pair_isConj_a : IsConj pair Janko4.a := by
  obtain ⟨g, hg⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
  exact isConj_iff.mpr ⟨g, hg.symm⟩

theorem pair_order : orderOf pair = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp pair_isConj_a
  exact ((MulAut.conj g).orderOf_eq pair).symm.trans
    ((congrArg orderOf hg).trans orderOf_a)

theorem seed_sq : seed ^ 2 = 1 := by
  rw [← seed_order]
  exact pow_orderOf_eq_one _

theorem pair_sq : pair ^ 2 = 1 := v_sq

theorem pair_centralizer_card : Nat.card C = 21799895040 :=
  (Subgroup.card_centralizer_eq_of_isConj pair Janko4.a pair_isConj_a).trans
    OuterReduction.OddIndex.modelCentralizer_card

theorem seed_not_isConj_pair : ¬ IsConj seed pair := by
  intro h
  have hc := Subgroup.card_centralizer_eq_of_isConj seed pair h
  have hu : Nat.card (centralizer ({seed} : Set Model)) = 1816657920 :=
    InvolutionCentralizers.Second.ambient_card
  have hv : Nat.card (centralizer ({pair} : Set Model)) = 21799895040 :=
    pair_centralizer_card
  rw [hu, hv] at hc
  norm_num at hc

/-- The precise orientation of the conjugator used in all packed witnesses. -/
theorem gp_conj_pair : gp * pair * gp⁻¹ = Janko4.a := by
  let r : Model := pair * Janko4.a
  have ht : pair⁻¹ = pair := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using pair_sq)
  have ha : Janko4.a⁻¹ = Janko4.a :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using a_pow_two)
  have hs : SemiconjBy pair r⁻¹ r := by
    change pair * (pair * Janko4.a)⁻¹ = (pair * Janko4.a) * pair
    rw [mul_inv_rev, ht, ha, mul_assoc]
  have hp : r ^ 11 = 1 := pair_mul_first_pow matrixA_mul_self matrixB_pow_four
  have h10 : r ^ 10 = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [← pow_succ] using hp)
  calc
    gp * pair * gp⁻¹ = r ^ 5 * (pair * (r⁻¹) ^ 5) := by
      simp only [gp, r, inv_pow, mul_assoc]
    _ = r ^ 5 * (r ^ 5 * pair) := by rw [(hs.pow_right 5).eq]
    _ = r ^ 10 * pair := by rw [← mul_assoc, ← pow_add]
    _ = r⁻¹ * pair := by rw [h10]
    _ = Janko4.a := by simp only [r, mul_inv_rev, ht, ha, mul_assoc,
        show pair * pair = 1 by simpa only [pow_two] using pair_sq, mul_one]

/-- Conjugating a generator of the full first centralizer gives an element
of the full pair centralizer, without requiring gp to lie in L. -/
theorem transported_mem_C (z : Model) (hz : z * Janko4.a = Janko4.a * z) :
    gp⁻¹ * z * gp ∈ C := by
  apply mem_centralizer_singleton_iff.mpr
  change (gp⁻¹ * z * gp) * pair = pair * (gp⁻¹ * z * gp)
  apply (MulAut.conj gp).injective
  have he : MulAut.conj gp (gp⁻¹ * z * gp) = z := by
    simp only [MulAut.conj_apply, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hv : MulAut.conj gp pair = Janko4.a := gp_conj_pair
  simpa only [map_mul, he, hv] using hz

theorem c_mem_C : c ∈ C :=
  transported_mem_C _
    OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cx_commute_a

theorem c_mem_L : c ∈ L := C_le_L c_mem_C

end Janko4.AdequateLocal
