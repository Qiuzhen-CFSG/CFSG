module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions
public import Theory.Mathieu.M22.CyclicFourCover
public import Theory.GroupTheory.CyclicFourCentralSquares.Lifting
public import Theory.Mathieu.M22.Properties.PairCoreIncidence.Elementary

/-!
# Quartic fixed-pair restrictions and reduction to the binary cover

The square quotient retains every literal local preimage and sends its
two-residual onto the binary two-residual. Frattini nongeneration in the
order-four center then lifts central residual containment back to the
quartic cover. In particular the same hexad works for the native pair
stabilizer of {0,4}; no change of pair or hexad kernel occurs.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. The binary
intersection calculation remains an explicit input to this reduction.
Recognition of the second E₁₆ pullback as C₄ ∗ Q₈ ∗ Q₈ is a separate
calculation, not a consequence of the Frattini equality alone.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
/-- The actual fixed native pair satisfies the source S₅/E₁₆ hypothesis. -/
theorem fixed_pair_isSourceJ : IsSourceJ m22DisjointPairStabilizer :=
  ⟨pCore 2 m22DisjointPairStabilizer, inferInstance,
    m22DisjointPair_twoCore_elementary, m22DisjointPair_twoCore_card,
    ⟨m22DisjointPairQuotientEquiv⟩⟩

omit [Finite K] in
/-- The quotient by central squares maps each literal preimage onto the
preimage of the same native subgroup in the reduced cover. -/
theorem reduction_preimage (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    (preimage e H).map (QuotientGroup.mk' (centralSquares K)) =
      preimage (quarticReductionEquiv e) H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, hx⟩ := quarticReductionLocal_surjective e H ⟨y, hy⟩
    exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- Residual containment lifts from the double cover, even though the
central-square kernel need not have been separately placed in the residual. -/
theorem center_le_residual_of_reduction (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (H : Subgroup M22)
    (h : center (K ⧸ centralSquares K) ≤
      (pResidual 2 (preimage (quarticReductionEquiv e) H)).map
        (preimage (quarticReductionEquiv e) H).subtype) :
    center K ≤ (pResidual 2 (preimage e H)).map (preimage e H).subtype := by
  apply center_le_of_centralSquares_image_le hZ
  rw [map_embedded_pResidual, reduction_preimage]
  rwa [quarticReduction_center e, quarticReductionProjection_ker] at h

/-- The same chosen hexad works before and after the square quotient. -/
theorem fixed_pair_residual_of_reduction (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4)
    (h : ∃ B ∈ m22Blocks,
      center (K ⧸ centralSquares K) ≤ (pResidual 2
        (hexadPreimage (quarticReductionEquiv e) B ⊓
          preimage (quarticReductionEquiv e) m22DisjointPairStabilizer :
            Subgroup (K ⧸ centralSquares K))).map
        (hexadPreimage (quarticReductionEquiv e) B ⊓
          preimage (quarticReductionEquiv e) m22DisjointPairStabilizer).subtype) :
    ∃ B ∈ m22Blocks,
      center K ≤ (pResidual 2
        (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
        (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer).subtype := by
  obtain ⟨B, hB, h⟩ := h
  exact ⟨B, hB, center_le_residual_of_reduction e hZ
    (MulAction.stabilizer M22 B ⊓ m22DisjointPairStabilizer) h⟩

/-- The lifted pair core lies in the specific incident hexad preimage,
retaining the subgroup inclusion into K. -/
theorem fixed_pair_core_le_hexad234 (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) :
    (pCore 2 (preimage e m22DisjointPairStabilizer)).map
      (preimage e m22DisjointPairStabilizer).subtype ≤ hexadPreimage e m22Hexad234 := by
  rw [← preimage_twoCore e (IsPGroup.of_card (n := 2) (by simpa using hZ))]
  exact comap_mono m22DisjointPair_twoCore_le_hexad234

/-- Counting uses the actual local projection and its central kernel. -/
theorem fixed_pair_core_card (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) :
    Nat.card (pCore 2 (preimage e m22DisjointPairStabilizer)) = 64 := by
  rw [← card_map_of_injective (preimage e m22DisjointPairStabilizer).subtype_injective,
    ← preimage_twoCore e (IsPGroup.of_card (n := 2) (by simpa using hZ)), preimage_card,
    card_map_of_injective m22DisjointPairStabilizer.subtype_injective,
    m22DisjointPair_twoCore_card, hZ]

/-- In particular the pair core is not the radical of the hexad used above. -/
theorem fixed_pair_core_ne_hexadRadical (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (pCore 2 (preimage e m22DisjointPairStabilizer)).map
      (preimage e m22DisjointPairStabilizer).subtype ≠ hexadRadical e B := by
  rw [← preimage_twoCore e (IsPGroup.of_card (n := 2) (by simpa using hZ))]
  intro he
  have hn : m22DisjointPairStabilizer ≤
      normalizer ((pCore 2 m22DisjointPairStabilizer).map
        m22DisjointPairStabilizer.subtype : Set M22) := by
    have h := (pCore 2 m22DisjointPairStabilizer).le_normalizer_map
      m22DisjointPairStabilizer.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have hi := comap_injective (projection_surjective e) he
  rw [hi, m22HexadPointwiseKernel_normalizer hB] at hn
  exact m22_card1920_not_le_hexad _ m22DisjointPairStabilizer_card hB hn

/-- The published Frattini theorem now applies with the fixed pair's native
source hypothesis discharged, and with both ambient embeddings displayed. -/
theorem fixed_pair_frattini [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4) :
    ((frattini (pCore 2 (preimage e m22DisjointPairStabilizer))).map
      (pCore 2 (preimage e m22DisjointPairStabilizer)).subtype).map
        (preimage e m22DisjointPairStabilizer).subtype = centerSquares K :=
  sourceJ_quartic_frattini e hZ _ fixed_pair_isSourceJ

theorem fixed_pair_frattini_card [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4) :
    Nat.card (frattini (pCore 2 (preimage e m22DisjointPairStabilizer))) = 2 :=
  sourceJ_quartic_frattini_card e hZ _ fixed_pair_isSourceJ

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
