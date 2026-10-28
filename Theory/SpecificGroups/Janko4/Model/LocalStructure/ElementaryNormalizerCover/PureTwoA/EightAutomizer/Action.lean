module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Evaluation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Seed
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Fusion

/-!
# Lifting the finite automizer action to the actual J₄ carrier

The three checked generator equations extend to every eight-bit vector and
every positive word. The two first-class orbit representatives are fused to the
literal first involution; the second-class representative is the native seed.
Thus the finite orbit certificate can be used as ambient class information,
without trusting the numerical discovery ranks.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Subgroup ElementaryEightGeometry ElementaryEightGeometry.Loewy
attribute [local irreducible] modelGroup matrixA matrixB nativeMask correctedLift

theorem actor_action (i : Fin 3) (m : Mask) :
    actor i * maskElement m * (actor i)⁻¹ = maskElement (generator i m) := by
  let f := (MulAut.conj (actor i)).toMonoidHom
  have hb : ∀ j, generator i (bitBasis j) = generatorColumns i j := by
    have h : ∀ i : Fin 3, ∀ j : Fin 8, generator i (bitBasis j) = generatorColumns i j := by
      decide +kernel
    exact h i
  have he := hom_ext (fun m => f (maskElement m)) (fun m => maskElement (generator i m))
    (· * ·) 1
    (by rw [maskElement_zero,map_one])
    (by rw [(generator_good i).zero,maskElement_zero])
    (fun a b => by rw [maskElement_xor,map_mul])
    (fun a b => by rw [(generator_good i).map_xor,maskElement_xor])
    (fun j => by rw [maskElement_basis,hb]; exact actor_conjugates i j)
  exact congrFun he m

def wordElement (w : List (Fin 3)) : Model := (w.map actor).prod

theorem word_mem_target (w : List (Fin 3)) : wordElement w ∈ target := by
  apply Subgroup.list_prod_mem
  rintro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact actor_mem_target i

theorem word_action (w : List (Fin 3)) (m : Mask) :
    wordElement w * maskElement m * (wordElement w)⁻¹ = maskElement (wordAction w m) := by
  induction w with
  | nil => simp [wordElement,wordAction]
  | cons i w ih =>
    change (actor i * wordElement w) * maskElement m * (actor i * wordElement w)⁻¹ = _
    calc
      _ = actor i * (wordElement w * maskElement m * (wordElement w)⁻¹) *
          (actor i)⁻¹ := by group
      _ = _ := by rw [ih,actor_action]; rfl

theorem word_isConj (w : List (Fin 3)) (m : Mask) :
    IsConj (maskElement m) (maskElement (wordAction w m)) :=
  isConj_iff.mpr ⟨wordElement w,word_action w m⟩

theorem mask_one_mem_target : maskElement 1 ∈ target := by
  rw [show (1 : Mask) = bitBasis 0 from rfl,maskElement_basis]
  exact seed_mem_target

theorem mask_three_first : IsConj Janko4.a (maskElement 3) := by
  have he : maskElement 3 =
      (Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four : Model) := by
    rw [show (3 : Mask) = xor 1 2 from rfl,maskElement_xor,
      show (1 : Mask) = bitBasis 0 from rfl,
      show (2 : Mask) = bitBasis 1 from rfl,maskElement_basis,maskElement_basis]
    change (nativeMask 1 : Model) * (nativeMask 2 : Model) = _
    calc
      _ = (nativeMask 3 : Model) := congrArg (fun x : Cardinality.max1Subgroup
        matrixA_mul_self matrixB_pow_four => (x : Model)) (nativeMask_xor 1 2).symm
      _ = _ := by
        unfold nativeMask
        exact congrArg (fun x : Cardinality.max1Subgroup
          matrixA_mul_self matrixB_pow_four => (x : Model))
            (Simplicity.Max1Fusion.KernelOrbits.maskValue_three _ _)
  rw [he]
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.pair_fuses_first matrixA_mul_self matrixB_pow_four
  exact (isConj_iff.mpr ⟨g,hg.symm⟩).symm

theorem mask_sixtyfour_first : IsConj Janko4.a (maskElement 64) := by
  rw [show (64 : Mask) = bitBasis 6 from rfl,maskElement_basis]
  have hs : nativeGenerator 6 ^ 2 = 1 := by
    change ((correctedLift 2 : Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) : Model) ^ 2 = 1
    simpa only [pow_two,Subgroup.coe_mul,OneMemClass.coe_one] using
      congrArg (fun x : Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four => (x : Model))
        (correctedLift_square 2)
  apply isConj_of_involutions_odd_product _ _ Janko4.a_pow_two hs
  exact (by decide : Odd 11).of_dvd_nat (orderOf_dvd_of_pow_eq_one outside_first_product)

theorem mask_one_not_first : ¬ IsConj Janko4.a (maskElement 1) := by
  rw [show (1 : Mask) = bitBasis 0 from rfl,maskElement_basis]
  intro h
  have he : nativeGenerator 0 =
      (Cardinality.localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
    change (nativeMask 1 : Model) = _
    unfold nativeMask
    exact congrArg (fun x : Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four => (x : Model))
      (Simplicity.Max1Fusion.KernelOrbits.maskValue_one _ _)
  rw [he] at h
  apply Cardinality.LocalInvolutionCensus.not_isConj_z_t
  simpa only [Cardinality.LocalInvolutionCensus.z_eq_a,Cardinality.LocalInvolutionCensus.t] using h

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
