module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCoreObstruction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticKernel

/-!
# Constructing the original plane model from a whole-core order bound

The original marked plane quotient and the full-module natural quotient are
already constructed. The full module lies in the whole intrinsic core, so
an upper bound of 256 on that core gives its exact order. The resulting
OriginalPlaneModel retains the original maps, their exact kernel, the
outside residual and its normalization. Whole-block recognition implies
this numerical bound, but the numerical bound suffices for the terminal
consumer without further representation recognition.

The bound is an explicit remaining source premise, not proved here.
Its discharge, including the non-Frattini whole-core reconstruction, stays
with qt-d-tensor-sp4-plane. Source: Aschbacher--Smith 9.3.10 and the final
paragraph of 9.3, pp.734--735; MS93 (3.6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

/-- Construct all original-plane fields from an order bound on the entire intrinsic core. -/
theorem originalPlaneModel_of_core_card_le (c : m.GenerationTwoOvergroup)
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier)
    (hbound : Nat.card (pCore 2 (pResidual 2 c.M)) ≤ 256) :
    Nonempty (OriginalPlaneModel D) := by
  let U := ((ChapterC.blockU (pResidual 2 c.M)).map
    (pResidual 2 c.M).subtype).map c.M.subtype
  have hVU : D.fullModule ≤ U := c.fullModule_le_blockU eK
  have hcard : Nat.card U = 256 := by
    apply le_antisymm
    · dsimp only [U]
      rwa [card_map_of_injective c.M.subtype_injective,
        card_map_of_injective (pResidual 2 c.M).subtype_injective,
        ← c.residual_twoCore_eq_blockU eK]
    · rw [← m.card_fullModule]
      exact Nat.card_le_card_of_injective (inclusion hVU) (inclusion_injective hVU)
  obtain ⟨q,hq,hk,hm⟩ := c.exists_marked_plane_quotient eK
  obtain ⟨p,hp,hpk,he⟩ := m.exists_fullModule_natural_quotient
  refine ⟨{ U := U
            K := (pResidual 2 c.M).map c.M.subtype
            quotient := q
            onto := hq
            kernel := hk
            natural := p
            natural_onto := hp
            natural_kernel := ?_
            equivariant := ?_
            card := hcard
            normalized := c.residual_normalizes_blockU
            outside := c.residual_outside }⟩
  · rw [hpk]
    exact comap_mono (comap_mono c.tensorPlane_le_blockU)
  · let := fullModule_component_normal (D := D)
    intro l v
    rw [hm l]
    exact he l v

/-- The remaining numerical source input concerns the complete original two-core. -/
@[expose] def SymplecticCoreBound (m : SourceA5TensorModel D e) : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    Nat.card (pCore 2 (pResidual 2 c.M)) ≤ 256

/-- The existing whole-block contract supplies the numerical premise of the terminal application. -/
theorem symplecticCoreBound_of_block
    (hblock : m.SymplecticBlockRecognition) : m.SymplecticCoreBound := by
  intro c eK
  have hcard := c.blockU_ambient_card (hblock c eK)
  rw [card_map_of_injective c.M.subtype_injective,
    card_map_of_injective (pResidual 2 c.M).subtype_injective,
    ← c.residual_twoCore_eq_blockU eK] at hcard
  exact hcard.le

/-- The literal action marking and the whole-core bound give the original plane model. -/
theorem symplecticPlaneRecognition_of_core_bound
    (hbound : m.SymplecticCoreBound) : m.SymplecticPlaneRecognition := by
  intro c W hr
  let := hr.normal
  intro hact
  obtain ⟨eact⟩ := hact
  have hker := m.symplecticKernelRecognition c hr ⟨eact⟩
  let eK := (c.residualActionEquiv hr hker).trans eact
  exact originalPlaneModel_of_core_card_le c eK (hbound c eK)

/-- Apply the numerical whole-core route to the actual tensor-exclusion consumer. -/
theorem false_of_generationTwo_source_inputs_of_core_bound
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion)
    (hbound : m.SymplecticCoreBound) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_core_bound hbound)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
