module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SecondActorPosition.Certificates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Assembly
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer

/-!
# The actual moving Mathieu residual and its radical displacement

A native order-three word and the certified Sylow generators preserve the
binary plane spanned by vectors 1327 and 1047. Three checked coset representatives
bound their generated group; its cubic element then gives relative index three.
The full native actor catalogue identifies its two-residual with every moving
noncubic residual above the marked Sylow subgroup. Two explicit displacements
of the genuine point-radical inverter put this plane inside the commutator
of the marked orthogonal hyperplane with that radical.

This proves the second moved-space containment needed by the original source
12.8.11(1) bound in Aschbacher--Smith 14.4.12, printed pp.1011--1012.
No desired operator-image or hexad-alignment premise is used.
The imported native matrices retain their published ATLAS attribution;
SecondActorPosition/source documents the reproducible small certificates.
-/

@[expose] public section
open Matrix Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
open SylowCertificates OrbitCertificates RadicalAction

def movingParabolic : Subgroup Group := closure (Set.range actor)

theorem candidate_le_moving : candidate ≤ movingParabolic := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  apply Subgroup.subset_closure
  refine ⟨⟨i.val, by omega⟩, ?_⟩
  fin_cases i <;> rfl

theorem rotationActor_mem : rotationActor ∈ movingParabolic := subset_closure ⟨6,rfl⟩

theorem moving_cover (g : Group) (hg : g ∈ movingParabolic) :
    ∃ s ∈ candidate, ∃ i : Fin 3, g = s * representative i := by
  induction hg using closure_induction_right with
  | one => exact ⟨1,candidate.one_mem,0,by simp [representative]⟩
  | mul_right g _ a ha ih =>
    obtain ⟨a,rfl⟩ := ha
    obtain ⟨s,hs,i,rfl⟩ := ih
    exact ⟨s * coefficient a i,candidate.mul_mem hs (coefficient_mem a i),next a i,
      by rw [mul_assoc,transition,←mul_assoc]⟩
  | mul_inv_cancel g _ a ha ih =>
    obtain ⟨a,rfl⟩ := ha
    obtain ⟨s,hs,i,rfl⟩ := ih
    have he := transition a (previous a i)
    rw [next_previous] at he
    have hinv : representative i * (actor a)⁻¹ = (coefficient a (previous a i))⁻¹ * representative (previous a i) := by
      rw [←mul_right_cancel_iff (a := actor a)]
      simp only [inv_mul_cancel_right]
      rw [mul_assoc,he,inv_mul_cancel_left]
    exact ⟨s * (coefficient a (previous a i))⁻¹,
      candidate.mul_mem hs (candidate.inv_mem (coefficient_mem a (previous a i))),
      previous a i,by rw [mul_assoc,hinv,←mul_assoc]⟩

theorem representative_mem (i : Fin 3) : representative i ∈ movingParabolic := by
  fin_cases i
  · exact movingParabolic.one_mem
  · exact rotationActor_mem
  · exact movingParabolic.mul_mem rotationActor_mem rotationActor_mem

theorem moving_card_le : Nat.card movingParabolic ≤ Nat.card candidate * 3 := by
  let f : candidate × Fin 3 → movingParabolic := fun si =>
    ⟨si.1.val * representative si.2,
      movingParabolic.mul_mem (candidate_le_moving si.1.property) (representative_mem si.2)⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨s,hs,i,he⟩ := moving_cover g.val g.property
    exact ⟨(⟨s,hs⟩,i),Subtype.ext he.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

def firstVector : BinarySpace := markedVector
def secondVector : BinarySpace := packed 1047
def movingPlane : Submodule (ZMod 2) BinarySpace := Submodule.span (ZMod 2) {firstVector,secondVector}

theorem first_mem : firstVector ∈ movingPlane := Submodule.subset_span (Set.mem_insert _ _)
theorem second_mem : secondVector ∈ movingPlane := Submodule.subset_span (by simp)

theorem actor_planes (a : Fin 7) :
    representation (actor a) firstVector ∈ movingPlane ∧
    representation (actor a) secondVector ∈ movingPlane := by
  have hv : firstVector + secondVector ∈ movingPlane := movingPlane.add_mem first_mem second_mem
  have h : ∀ a : Fin 7,
      (actor a).val.val *ᵥ firstVector = (![firstVector,firstVector,firstVector,firstVector,firstVector,firstVector,secondVector] a) ∧
      (actor a).val.val *ᵥ secondVector = (![secondVector,secondVector,secondVector,secondVector,secondVector,firstVector+secondVector,firstVector+secondVector] a) := by
    intro a
    fin_cases a
    · change (s0.val.val *ᵥ firstVector = firstVector) ∧ (s0.val.val *ᵥ secondVector = secondVector)
      rw [s0_matrix]; decide +kernel
    · change (s1.val.val *ᵥ firstVector = firstVector) ∧ (s1.val.val *ᵥ secondVector = secondVector)
      rw [s1_matrix]; decide +kernel
    · change (s2.val.val *ᵥ firstVector = firstVector) ∧ (s2.val.val *ᵥ secondVector = secondVector)
      rw [s2_matrix]; decide +kernel
    · change (s3.val.val *ᵥ firstVector = firstVector) ∧ (s3.val.val *ᵥ secondVector = secondVector)
      rw [s3_matrix]; decide +kernel
    · change (s4.val.val *ᵥ firstVector = firstVector) ∧ (s4.val.val *ᵥ secondVector = secondVector)
      rw [s4_matrix]; decide +kernel
    · change (s5.val.val *ᵥ firstVector = firstVector) ∧ (s5.val.val *ᵥ secondVector = firstVector + secondVector)
      rw [s5_matrix]; decide +kernel
    · change (rotationActor.val.val *ᵥ firstVector = secondVector) ∧ (rotationActor.val.val *ᵥ secondVector = firstVector + secondVector)
      rw [rotationActor_matrix]; decide +kernel
  change (actor a).val.val *ᵥ firstVector ∈ movingPlane ∧ (actor a).val.val *ᵥ secondVector ∈ movingPlane
  rw [(h a).1,(h a).2]
  fin_cases a <;> exact ⟨by first | exact first_mem | exact second_mem,
    by first | exact second_mem | exact hv⟩

theorem moving_stabilizes : movingParabolic ≤ subspaceStabilizer representation movingPlane := by
  apply (closure_le _).mpr
  rintro _ ⟨a,rfl⟩
  have hstable : ∀ v ∈ movingPlane, representation (actor a) v ∈ movingPlane := by
    intro v hv
    exact Submodule.span_induction (fun w hw => by
      rcases hw with rfl | hw
      · exact (actor_planes a).1
      · exact (show w = secondVector from hw) ▸ (actor_planes a).2)
      (by simp) (fun x y _ _ hx hy => by rw [map_add]; exact movingPlane.add_mem hx hy)
      (fun c x _ hx => by rw [map_smul]; exact movingPlane.smul_mem c hx) hv
  have he : movingPlane.map (representation (actor a)) = movingPlane := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v,hv,rfl⟩; exact hstable v hv
    · exact (Submodule.equivMapOfInjective _ (representation.apply_bijective (actor a)).1 _).finrank_eq.symm
  intro v
  constructor
  · intro hv
    rw [← he] at hv
    obtain ⟨w,hw,hwv⟩ := hv
    exact (representation.apply_bijective (actor a)).1 hwv ▸ hw
  · exact hstable v

theorem moving_displacement_le :
    subspaceCommutator representation (binaryLine markedVector) (twoResidual movingParabolic) ≤ movingPlane := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,hv,rfl⟩
  have hvP : v ∈ movingPlane := (Submodule.span_mono (by simp [firstVector])) hv
  exact movingPlane.sub_mem ((moving_stabilizes (map_subtype_le _ ha) v).2 hvP) hvP

theorem movingPlane_le_radical_moved :
    movingPlane ≤ subspaceCommutator representation markedPerp pointRadical := by
  apply Submodule.span_le.mpr
  intro v hv
  have h0 := embedding_mem_parabolic (Pi.single 3 1)
  have h1 := embedding_mem_parabolic (Pi.single 4 1)
  have he0 : representation NativePositions.inverterWord (embedding (Pi.single 3 1)) - embedding (Pi.single 3 1) = firstVector := by
    change ((NativePositions.inverterWord : Matrix12ˣ) : Matrix12) *ᵥ _ - _ = _
    rw [NativePositions.inverterWord_matrix]
    decide +kernel
  have he1 : representation NativePositions.inverterWord (embedding (Pi.single 4 1)) - embedding (Pi.single 4 1) = secondVector := by
    change ((NativePositions.inverterWord : Matrix12ˣ) : Matrix12) *ᵥ _ - _ = _
    rw [NativePositions.inverterWord_matrix]
    decide +kernel
  rcases hv with rfl | hv
  · exact Submodule.subset_span ⟨NativePositions.inverterWord,NativePositions.inverterWord_radical,
      embedding (Pi.single 3 1),parabolicSpace_le_markedPerp h0,he0.symm⟩
  · rw [show v = secondVector from hv]
    exact Submodule.subset_span ⟨NativePositions.inverterWord,NativePositions.inverterWord_radical,
      embedding (Pi.single 4 1),parabolicSpace_le_markedPerp h1,he1.symm⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
open SylowCertificates OrbitCertificates RadicalAction
open ActorCatalogue.NativeParabolics

theorem moving_index : (markedSylow : Subgroup Group).relIndex movingParabolic = 3 := by
  have hSP : (markedSylow : Subgroup Group) ≤ movingParabolic := by
    rw [markedSylow_coe]; exact candidate_le_moving
  have hcS : Nat.card (markedSylow : Subgroup Group) = 256 := by
    rw [markedSylow.card_eq_multiplicity,group_card]; decide +kernel
  have hc : Nat.card ((markedSylow : Subgroup Group).subgroupOf movingParabolic) = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv).trans hcS
  have he := ((markedSylow : Subgroup Group).subgroupOf movingParabolic).card_mul_index
  rw [hc] at he
  have hu := moving_card_le
  rw [← markedSylow_coe,hcS] at hu
  have hlo : 3 ∣ Nat.card movingParabolic := by
    have hR3 : orderOf (⟨rotationActor,rotationActor_mem⟩ : movingParabolic) = 3 := by
      apply orderOf_eq_prime
      · apply Subtype.ext; exact rotationActor_cube
      · intro h
        have hm := congrArg (fun g : movingParabolic => ((g.val : Matrix12ˣ) : Matrix12)) h
        rw [rotationActor_matrix] at hm
        have hn : (fromRows ![58,718,3198,1236,2850,496,1979,3490,2131,1802,3256,628] : Matrix12) ≠ 1 := by decide +kernel
        exact hn hm
    exact hR3 ▸ orderOf_dvd_natCard (⟨rotationActor,rotationActor_mem⟩ : movingParabolic)
  have hp : 0 < Nat.card movingParabolic := Nat.card_pos
  change 256 * (markedSylow : Subgroup Group).relIndex movingParabolic = Nat.card movingParabolic at he
  omega

theorem scalar_not_mem_moving : centralScalar ∉ movingParabolic := by
  intro h
  have hm := (moving_stabilizes h firstVector).2 first_mem
  obtain ⟨a,b,hu⟩ := Submodule.mem_span_pair.mp hm
  have hab : ∀ a b : ZMod 2,
      a • firstVector + b • secondVector ≠ representation centralScalar firstVector := by
    decide +kernel
  exact hab a b hu

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
open SylowCertificates OrbitCertificates RadicalAction
open ActorCatalogue.NativeParabolics

theorem rotationActor_moves : representation rotationActor markedVector ≠ markedVector := by
  change ((rotationActor : Matrix12ˣ) : Matrix12) *ᵥ markedVector ≠ markedVector
  rw [rotationActor_matrix]
  decide +kernel

theorem moving_residual_moves : ¬ twoResidual movingParabolic ≤ ActorCatalogue.Native.pointCentralizer markedVector := by
  intro h
  have hS : (markedSylow : Subgroup Group) ≤ movingParabolic := by rw [markedSylow_coe]; exact candidate_le_moving
  have hfix : (markedSylow : Subgroup Group) ≤ ActorCatalogue.Native.pointCentralizer markedVector := by
    intro s hs
    have hv : markedVector ∈ fixedSpace representation markedSylow := by
      rw [markedSylow_fixedSpace]; exact Submodule.mem_span_singleton_self _
    exact hv ⟨s,hs⟩
  have hP := sup_le h hfix
  rw [residual_sup_sylow markedSylow movingParabolic hS] at hP
  exact rotationActor_moves (hP rotationActor_mem)

theorem moving_residual_ne_cubic : twoResidual movingParabolic ≠ twoResidual (pCore 3 Group) := by
  intro h
  have hs : centralScalar ∈ twoResidual movingParabolic := by
    rw [h,firstActor_eq_cubic,cubic_eq_zpowers]
    exact mem_zpowers cubicScalar
  exact scalar_not_mem_moving (map_subtype_le _ hs)

/-- The original moving noncubic rank-one residual, with all matrix positions
discharged, moves the marked binary line inside the point-radical commutator.
The source 12.8.11(1) then bounds its actual extraspecial lift by E. -/
theorem second_displacement_le_radical
    (P : Subgroup Group) (hSP : (markedSylow : Subgroup Group) ≤ P)
    (hi : (markedSylow : Subgroup Group).relIndex P = 3)
    (hd : Disjoint cubic P)
    (hm : ¬ twoResidual P ≤ ActorCatalogue.Native.pointCentralizer markedVector) :
    subspaceCommutator representation (binaryLine markedVector) (twoResidual P) ≤
      subspaceCommutator representation markedPerp pointRadical := by
  have hfix : ∀ s : markedSylow, ActorCatalogue.Native.action s.val markedVector = markedVector := by
    intro s
    have hv : markedVector ∈ fixedSpace representation markedSylow := by
      rw [markedSylow_fixedSpace]; exact Submodule.mem_span_singleton_self _
    exact hv s
  obtain ⟨q,i,_,_,hSB,hB,hiB,_⟩ :=
    (ActorCatalogue.Native.pointCentralizer_borel markedSylow markedVector markedVector_ne_zero hfix).2.2
  let B := ActorCatalogue.Native.pointBorel markedVector q i
  obtain ⟨P₂,g,hP₂,_,_,_,_,_,_,_,_,_,_,hf⟩ :=
    Catalogue.exists_catalogue markedSylow markedVector_ne_zero B hSB hB hiB
  have hS : (markedSylow : Subgroup Group) ≤ movingParabolic := by rw [markedSylow_coe]; exact candidate_le_moving
  have hC : twoResidual movingParabolic ∈ XFamily ⊤ (markedSylow : Subgroup Group) :=
    residual_threeExtension_of_index_three markedSylow movingParabolic hS moving_index
  have hP : twoResidual P ∈ XFamily ⊤ (markedSylow : Subgroup Group) :=
    residual_threeExtension_of_index_three markedSylow P hSP hi
  rw [hf] at hC hP
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hC hP
  have hBC : twoResidual B ≤ ActorCatalogue.Native.pointCentralizer markedVector :=
    borelResidual_le_pointCentralizer B hB
  have hCeq : twoResidual movingParabolic = twoResidual P₂ := by
    rcases hC with h | h | h
    · exact (moving_residual_ne_cubic h).elim
    · exact h
    · exact (moving_residual_moves (h ▸ hBC)).elim
  have hPeq : twoResidual P = twoResidual P₂ := by
    rcases hP with h | h | h
    · exact (Catalogue.firstActor_ne_residual_of_disjoint hd h.symm).elim
    · exact h
    · exact (hm (h ▸ hBC)).elim
  rw [hPeq,←hCeq]
  exact moving_displacement_le.trans movingPlane_le_radical_moved
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
