module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFour

/-!
# Exact shifted-root intersections with the source derived and Frattini groups

For the shifted Suzuki root A = U_i^(s_j s_i), the order-four obstruction
forces Φ(V) ∩ A into Ω₁(A). Every element of Ω₁(A) is a square in A ≤ V,
so the reverse inclusion holds for every parameter, including Sz(2).
For positive parameters Ω₁(A)=[A,A], giving [V,V] ∩ A = Ω₁(A) as well.

These are the precise support restrictions underlying the exclusion of
whole shifted Suzuki roots at the start of Fong--Seitz I (1973), p.53.
The markings and independent-field size inequality remain explicit.
OriginalShiftedIntersections retains the literal original-core images,
both endpoint orientations and Q.q. No perpendicular-root support or
unconditional near-commutator equality is asserted here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
  (hm : rotationOrder Q = 8) (hij : i ≠ j)
  (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)

include ν hC μ hB hc hm hij hsize in
/-- The shifted root meets the actual Frattini subgroup in exactly its Omega, including Sz(2). -/
theorem source_shifted_frattini_intersection :
    (frattiniRadicalSection Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB)).numerator ⊓
        rootAt Q split i (Q.simple j*Q.simple i) =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  apply le_antisymm
  · intro a ha
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl a ha.2
    by_contra hsq
    have hh := frattini_root_order_four_forces_card Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB) m μ hB hc hm j hij
      (source_six_three Q split i j m μ hB ν T hC hm hij).2 ⟨a,ha.2⟩ ha.1 hsq
    rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
    exact hh.not_gt hsize
  · exact le_inf (source_omega_le_frattini Q split i m μ hB _
      (source_six_four_shifted_root_le_remainder Q split i j hm hij)) (omegaOneAmbient_le _)

include ν hC μ hB hc hm hij hsize in
/-- For positive parameters the derived intersection is the same precise Omega subgroup. -/
theorem source_positive_shifted_derived_intersection (hmpos : 0 < m) :
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⊓
        rootAt Q split i (Q.simple j*Q.simple i) =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  let V := simpleRemainder Q split i
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hD : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  apply le_antisymm
  · exact (inf_le_inf_right _ hD).trans
      (source_shifted_frattini_intersection Q split i j ν T hC m μ hB hc hm hij hsize).le
  · exact le_inf (source_positive_omega_le_derived Q split i m μ hB hmpos _
      (source_six_four_shifted_root_le_remainder Q split i j hm hij)) (omegaOneAmbient_le _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

