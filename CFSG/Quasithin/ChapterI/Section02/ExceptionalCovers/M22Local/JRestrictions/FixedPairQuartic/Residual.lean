module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.Recognition
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
public import Theory.Frattini.OmegaProducts

/-!
# Quartic residual placement from the marked hexad action

The actual central-square quotient sends the hexad section and radical to the
double cover. Frattini quotient coordinates identify its radical with the even
permutation core, preserving the pentad marking and the actual central line.
The published binary calculation supplies an incident hexad at the fixed pair.
Frattini nongeneration in the quartic center lifts its residual containment.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. Compatible quartic
hexad recognition remains explicit and is owned by the quartic-hexad assembly.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open BinaryPermutation GLS3.Chapter5
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K]
variable [Finite K] [IsCyclic (center K)]
variable (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
variable {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (rec : Recognition e hB)
/-- The literal square quotient on the named hexad radical. -/
noncomputable def radicalReduction : hexadRadical e B →* hexadRadical (quarticReductionEquiv e) B :=
  quarticReductionLocal e (m22HexadPointwiseKernel B)
/-- The same ambient quotient on the full named hexad preimage. -/
noncomputable def hexadReduction : hexadPreimage e B →* hexadPreimage (quarticReductionEquiv e) B :=
  quarticReductionLocal e (MulAction.stabilizer M22 B)

/-- Coordinates on the actual reduced radical, obtained through its Frattini quotient. -/
noncomputable def reductionCoordinates :
    hexadRadical (quarticReductionEquiv e) B ≃* Multiplicative (core (Fin 6)) :=
  (Quartic.radicalReductionEquiv e hZ hB).symm.trans
    ((QuotientGroup.congr _ _ rec.coordinates (frattini_map_equiv rec.coordinates)).trans
      EvenCliffordSix.frattiniQuotientEquiv)

@[simp] theorem reductionCoordinates_apply (r : hexadRadical e B) :
    reductionCoordinates e hZ hB rec (radicalReduction e (B := B) r) =
      EvenCliffordSix.projection (rec.coordinates r) := by
  change reductionCoordinates e hZ hB rec
    (Quartic.radicalReductionEquiv e hZ hB (QuotientGroup.mk r)) = _
  simp only [reductionCoordinates, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private theorem center_vector (x : EvenCliffordSix.Model) :
    x ∈ center EvenCliffordSix.Model ↔ x.vector.val ∈ constants (Fin 6) := by
  rw [← EvenCliffordSix.Structure.naturalProjection_ker_eq_center]
  change coreToNatural (Fin 6) x.vector = 0 ↔ _
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

omit [Finite K] [IsCyclic (center K)] in
include e in
private theorem reduction_mem_center (x : K) :
    QuotientGroup.mk' (centralSquares K) x ∈ center (K ⧸ centralSquares K) ↔
      x ∈ center K := by
  rw [quarticReduction_center e]
  change projection e x = 1 ↔ x ∈ center K
  rw [← MonoidHom.mem_ker, projection_ker]

/-- The required binary recognition, with its native quotient and pentad marking retained. -/
noncomputable def binaryRecognition : FixedPairBinary.Recognition (quarticReductionEquiv e) hB where
  sectionMap := (hexadReduction e (B := B)).comp rec.sectionMap
  section_eq a := by
    change hexadSixMap e hB (rec.sectionMap a) = a
    exact rec.section_eq a
  coordinates := reductionCoordinates e hZ hB rec
  equivariant a r := by
    obtain ⟨x, rfl⟩ := (show Function.Surjective (radicalReduction e (B := B)) from
      quarticReductionLocal_surjective e (m22HexadPointwiseKernel B)) r
    have he : hexadConjugation (quarticReductionEquiv e) B
        (hexadReduction e (B := B) (rec.sectionMap a))
        (radicalReduction e (B := B) x) =
      radicalReduction e (B := B)
        (hexadConjugation e B (rec.sectionMap a) x) := by
      apply Subtype.ext
      change _ = QuotientGroup.mk' (centralSquares K) (_ * _ * _)
      simp only [map_mul]
      rfl
    change (reductionCoordinates e hZ hB rec (hexadConjugation _ _ _ _)).toAdd = _
    simp only [MonoidHom.comp_apply]
    rw [he, reductionCoordinates_apply, reductionCoordinates_apply, rec.equivariant]
    rfl
  center_eq r := by
    obtain ⟨x, rfl⟩ := (show Function.Surjective (radicalReduction e (B := B)) from
      quarticReductionLocal_surjective e (m22HexadPointwiseKernel B)) r
    rw [reductionCoordinates_apply]
    exact (reduction_mem_center e x.val).trans ((rec.center_eq x).trans (center_vector _))

include hZ hB rec in
/-- The residual calculation retains the incident relative position of the chosen hexad. -/
theorem fixed_pair_incident_residual : ∃ C ∈ m22Blocks, m22DisjointPair04 ⊆ C ∧
      center K ≤ (pResidual 2
        (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
          (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer).subtype := by
  obtain ⟨C, hC, hPC, hc⟩ := FixedPairBinary.fixed_pair_incident_residual
    (quarticReductionEquiv e) hB (binaryRecognition e hZ hB rec)
  exact ⟨C, hC, hPC, center_le_residual_of_reduction e hZ
    (MulAction.stabilizer M22 C ⊓ m22DisjointPairStabilizer) hc⟩

include hZ hB rec in
/-- The quartic fixed-pair residual conclusion, conditional only on compatible hexad recognition. -/
theorem fixed_pair_residual : ∃ C ∈ m22Blocks,
      center K ≤ (pResidual 2
        (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
          (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer).subtype := by
  obtain ⟨C, hC, _, hc⟩ := fixed_pair_incident_residual e hZ hB rec
  exact ⟨C, hC, hc⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
