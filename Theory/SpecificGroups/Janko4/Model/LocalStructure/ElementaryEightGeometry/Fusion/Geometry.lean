module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Quotient
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.AmbientCentralizers

/-!
# Fusion of the displayed native elementary eights

The checked conjugator sends the marked (b) row into the constructed (d)
eight. Centralizing that inclusion reverses it; both full centralizers have
order 256, so they agree. This proves ambient conjugacy using an actual max1
word and keeps its kernel corrections and generator equations.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Theory.GroupTheory Subgroup Cardinality KernelCount QuotientCount.Image
open SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis nativeMask correctedLift localFusion nativeFusion
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

private def targetMask : Fin 4 → Fin 2048 := ![1129,823,1886,822]

private theorem targetMask_fixed : ∀ j, fixedTest 1 (targetMask j) := by decide +kernel

private theorem targetMask_mem (j : Fin 4) : nativeMask (targetMask j).val ∈ localEight 1 := by
  apply (show centralKernel 1 ≤ localEight 1 from le_sup_right)
  refine ⟨e (targetMask j),?_,(nativeMask_eq_maskEquiv (targetMask j)).symm⟩
  exact (mask_mem_pairRow_centralizer_iff (liftClosure 1) _
    (liftClosure_projection 1) _).mpr (targetMask_fixed j)

theorem fusionTarget_mem (j : Fin 4) : fusionTarget j ∈ localEight 1 := by
  fin_cases j
  · exact (localEight 1).mul_mem
      ((localEight 1).mul_mem (targetMask_mem 0) (correctedGenerator_mem_localEight 1 1))
      (correctedGenerator_mem_localEight 1 2)
  · exact (localEight 1).mul_mem
      ((localEight 1).mul_mem (targetMask_mem 1) (correctedGenerator_mem_localEight 1 0))
      (correctedGenerator_mem_localEight 1 2)
  · exact (localEight 1).mul_mem (targetMask_mem 2) (correctedGenerator_mem_localEight 1 1)
  · exact (localEight 1).mul_mem
      ((localEight 1).mul_mem (targetMask_mem 3) (correctedGenerator_mem_localEight 1 0))
      (correctedGenerator_mem_localEight 1 3)

private theorem map_generated_join_le {G H : Type*} [Group G] [Group H]
    (a : Fin 4 → G) (s : G) (f : G →* H) (K : Subgroup H)
    (ha : ∀ j, f (a j) ∈ K) (hs : f s ∈ K) :
    (closure (Set.range a) ⊔ closure ({s} : Set G)).map f ≤ K := by
  rw [Subgroup.map_sup]
  apply sup_le
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact ha j
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply (closure_le _).mpr
    exact Set.singleton_subset_iff.mpr hs

private theorem markedRow_map_le (g : L)
    (hgen : ∀ j, g * correctedGenerator 0 j * g⁻¹ ∈ localEight 1)
    (hseed : g * InvolutionCentralizers.Second.seed * g⁻¹ ∈ localEight 1) :
    (markedLocalRow 0).map (MulAut.conj g).toMonoidHom ≤ localEight 1 :=
  map_generated_join_le (correctedGenerator 0) InvolutionCentralizers.Second.seed
    (MulAut.conj g).toMonoidHom (localEight 1) hgen hseed

theorem localFusion_markedRow_le :
    (markedLocalRow 0).map (MulAut.conj localFusion).toMonoidHom ≤ localEight 1 := by
  apply markedRow_map_le localFusion
  · intro j
    exact (congrArg (fun z : L => z ∈ localEight 1)
      (localFusion_correctedGenerator j)).mpr (fusionTarget_mem j)
  · have hs : nativeMask 1 = InvolutionCentralizers.Second.seed := by
      unfold nativeMask
      exact Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four
    have he : localFusion * InvolutionCentralizers.Second.seed * localFusion⁻¹ = nativeMask 1 :=
      (congrArg (fun z : L => localFusion * z * localFusion⁻¹) hs).symm.trans localFusion_mask_1
    exact (congrArg (fun z : L => z ∈ localEight 1) he).mpr
      (show nativeMask 1 ∈ localEight 1 from kernelPair_mem_localEight 1 0)

/-- Conjugacy in the original local group, proved from the full centralizers. -/
theorem localFusion_eight :
    (localEight 0).map (MulAut.conj localFusion).toMonoidHom = localEight 1 := by
  have hc : centralizer ((markedLocalRow 0).map
      (MulAut.conj localFusion).toMonoidHom : Set L) =
      (localEight 0).map (MulAut.conj localFusion).toMonoidHom :=
    (map_centralizer_equiv (markedLocalRow 0 : Set L) (MulAut.conj localFusion)).symm.trans
      (congrArg (fun C : Subgroup L => C.map (MulAut.conj localFusion).toMonoidHom)
        (markedLocalRow_centralizer 0))
  have hle : localEight 1 ≤ (localEight 0).map (MulAut.conj localFusion).toMonoidHom := by
    rw [← hc]
    exact (localEight 1).le_centralizer.trans (centralizer_le localFusion_markedRow_le)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective (MulAut.conj localFusion).injective, localEight_card, localEight_card]

/-- Literal ambient fusion, using the original embedding of max1 into J4. -/
theorem nativeFusion_eight :
    (nativeEight 0).map (MulAut.conj nativeFusion).toMonoidHom = nativeEight 1 := by
  change ((localEight 0).map (L).subtype).map (MulAut.conj nativeFusion).toMonoidHom =
    (localEight 1).map (L).subtype
  rw [Subgroup.map_map]
  have he : (MulAut.conj nativeFusion).toMonoidHom.comp (L).subtype =
      (L).subtype.comp (MulAut.conj localFusion).toMonoidHom := by
    ext x
    unfold nativeFusion
    rfl
  rw [he, ← Subgroup.map_map, localFusion_eight]

/-- Choice of an explicit conjugator from either displayed unprimed eight to
the common representative; the signed primed row already has this centralizer. -/
def rowFusion (r : Fin 2) : Model := if r = 0 then nativeFusion else 1

theorem rowFusion_eight (r : Fin 2) :
    (nativeEight r).map (MulAut.conj (rowFusion r)).toMonoidHom = nativeEight 1 := by
  fin_cases r
  · exact nativeFusion_eight
  · simp [rowFusion]
    exact Subgroup.map_id (G := Model) (K := nativeEight 1)

end Janko4.LocalStructure.ElementaryEightGeometry
