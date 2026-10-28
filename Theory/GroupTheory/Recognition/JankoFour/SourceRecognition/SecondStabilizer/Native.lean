module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.FiveFrame
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.Certificates

/-!
# The second native and source vector stabilizers

The five-involution certificate realizes a surjection onto S₅ with elementary
kernel of order sixteen. Orbit–stabilizer gives order 1920 for the actual full
native stabilizer. The original full cubic action then transports this
structure to every source vector with the second singular label and to its
literal element-centralizer image under H → H/Q.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), p.597, DOI 10.1007/BF01232280.
-/

public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open SecondStabilizer.Certificates

private theorem generators_mem (j : Fin 4) : generators j ∈ nativeVectorStabilizer (VectorOrbits.decode 7) := by
  change binaryAction (generators j) (VectorOrbits.vector 7) = VectorOrbits.vector 7
  rw [generators_action,← VectorOrbits.vector_packedAction]
  revert j
  decide +kernel

private theorem word_mem (l : List (Fin 4)) : word l ∈ nativeVectorStabilizer (VectorOrbits.decode 7) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  exact generators_mem j

private theorem five_mem (j : Fin 5) : five j ∈ nativeVectorStabilizer (VectorOrbits.decode 7) := by
  have he : five j = word (fiveWords j) := by fin_cases j <;> rfl
  rw [he]
  exact word_mem _

private theorem kernel_mem (i : Fin 16) :
    kernelElement i ∈ nativeVectorStabilizer (VectorOrbits.decode 7) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  exact five_mem j

private theorem native_structure_of_card (hc : Nat.card (nativeVectorStabilizer (VectorOrbits.decode 7)) = 1920) :
    let S := nativeVectorStabilizer (VectorOrbits.decode 7)
    IsElementaryAbelian 2 (pCore 2 S) ∧ Nat.card (pCore 2 S) = 16 ∧
      Nonempty ((S ⧸ pCore 2 S) ≃* Equiv.Perm (Fin 5)) := by
  let v : Fin 5 → nativeVectorStabilizer (VectorOrbits.decode 7) := fun j => ⟨five j,five_mem j⟩
  let k : Fin 16 → nativeVectorStabilizer (VectorOrbits.decode 7) := fun j => ⟨kernelElement j,kernel_mem j⟩
  exact FiveFrame.structure_of_frame v
    (fun _ _ he => five_injective (congrArg Subtype.val he)) hc k
    (fun _ _ he => kernel_injective (congrArg Subtype.val he))
    (fun j => Subtype.ext (kernel_sq j))
    (fun i j => Subtype.ext (kernel_comm i j))
    ⟨word [2,1],word_mem _⟩ ⟨word [0,2,3,2,0],word_mem _⟩
    (fun j => Subtype.ext (cycle_conj j)) (fun j => Subtype.ext (swap_conj j))

@[instance_reducible] private noncomputable def nativeAction :
    MulAction actionGroup M22TripleCover.BinarySpace where
  smul g v := binaryAction g v
  one_smul v := by change binaryAction 1 v = v; rw [map_one]; rfl
  mul_smul a b v := by
    change binaryAction (a*b) v = binaryAction a (binaryAction b v)
    rw [map_mul,Module.End.mul_apply]

private theorem native_card : Nat.card actionGroup = 2661120 := by
  have hA : Nat.card (MulAut M22) = 887040 :=
    (Nat.card_congr (MulEquiv.ofBijective m22DesignAutToAut
      ⟨m22DesignAutToAut_injective,m22DesignAutToAut_surjective⟩).toEquiv).symm.trans
        m22DesignAut_order
  have hi : scalarSubgroup.index = 887040 :=
    (Nat.card_congr scalarQuotientEquiv.toEquiv).trans hA
  have hc := scalarSubgroup.card_mul_index
  rw [scalarSubgroup_card,hi] at hc
  exact hc.symm

/-- The second native vector stabilizer has the original orbit-stabilizer order. -/
theorem native_second_card : Nat.card (nativeVectorStabilizer (VectorOrbits.decode 7)) = 1920 := by
  let := nativeAction
  let : SMul actionGroup M22TripleCover.BinarySpace := nativeAction.toSMul
  have hc := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup actionGroup (VectorOrbits.decode 7))
  have ho : Nat.card (MulAction.orbit actionGroup (VectorOrbits.decode 7)) = 1386 := by
    have he : MulAction.orbit actionGroup (VectorOrbits.decode 7) =
        {v | VectorOrbits.label v = 7} := by
      ext v
      constructor
      · rintro ⟨g,rfl⟩
        exact (VectorOrbits.ambient_label_invariant g (VectorOrbits.decode 7)).trans
          (VectorOrbits.label_decode 7)
      · intro hv
        obtain ⟨g,hg⟩ := (VectorOrbits.orbit_iff_label (VectorOrbits.decode 7) v).mpr
          ((VectorOrbits.label_decode 7).trans hv.symm)
        exact ⟨coverInclusion g,hg⟩
    rw [he]
    exact VectorOrbits.label_seven_card
  rw [Nat.card_prod,ho,native_card] at hc
  change 1386 * Nat.card (nativeVectorStabilizer (VectorOrbits.decode 7)) = 2661120 at hc
  omega

/-- The full native stabilizer has elementary two-core of order sixteen and S₅ quotient. -/
theorem native_second_structure :
    let S := nativeVectorStabilizer (VectorOrbits.decode 7)
    IsElementaryAbelian 2 (pCore 2 S) ∧ Nat.card (pCore 2 S) = 16 ∧
      Nonempty ((S ⧸ pCore 2 S) ≃* Equiv.Perm (Fin 5)) :=
  native_structure_of_card native_second_card

/-- Equal native labels identify the actual full vector stabilizers by conjugation. -/
noncomputable def nativeStabilizerEquivOfLabel (v w : M22TripleCover.BinarySpace)
    (he : VectorOrbits.label v = VectorOrbits.label w) :
    nativeVectorStabilizer v ≃* nativeVectorStabilizer w := by
  let := nativeAction
  let : SMul actionGroup M22TripleCover.BinarySpace := nativeAction.toSMul
  let hex := (VectorOrbits.orbit_iff_label v w).mpr he
  exact MulAction.stabilizerEquivStabilizer (g := coverInclusion hex.choose) hex.choose_spec.symm

private theorem transport_structure {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (hb : IsElementaryAbelian 2 (pCore 2 B) ∧ Nat.card (pCore 2 B) = 16 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 5))) :
    IsElementaryAbelian 2 (pCore 2 A) ∧ Nat.card (pCore 2 A) = 16 ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 5)) := by
  let ec := (f.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 f))
  let := hb.1
  exact ⟨IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective,
    (Nat.card_congr ec.toEquiv).trans hb.2.1,
    ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans hb.2.2.some⟩⟩

variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

/-- The literal second source vector stabilizer has shape S₅/E₁₆. -/
theorem coreVectorStabilizer_structure_seven (r : core z)
    (hr : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 7) :
    IsElementaryAbelian 2 (pCore 2 (coreVectorStabilizer h r)) ∧
      Nat.card (pCore 2 (coreVectorStabilizer h r)) = 16 ∧
      Nonempty ((coreVectorStabilizer h r ⧸ pCore 2 (coreVectorStabilizer h r)) ≃*
        Equiv.Perm (Fin 5)) := by
  let f := (coreVectorStabilizerNativeEquiv h e X r).trans
    (nativeStabilizerEquivOfLabel _ (VectorOrbits.decode 7)
      (hr.trans (VectorOrbits.label_decode 7).symm))
  exact transport_structure f native_second_structure

/-- The second structure belongs to the original element-centralizer image. -/
theorem coreCentralizerImage_structure_seven (r : core z) (hrc : r ∉ center (core z))
    (hr : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 7) :
    let C := (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
      (QuotientGroup.mk' (core z))
    IsElementaryAbelian 2 (pCore 2 C) ∧ Nat.card (pCore 2 C) = 16 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5)) := by
  dsimp only
  rw [← coreVectorStabilizer_eq_centralizer_image h r hrc]
  exact coreVectorStabilizer_structure_seven h e X r hr

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
