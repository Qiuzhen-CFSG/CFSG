module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.PositiveFixedPoints
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.VectorOrbit
public import Theory.AlgebraicGroup.Parabolic.Transitivity

/-!
# Borel and parabolic self-normalization

For a connected algebraic group, dimension induction proves that each Borel is
its own normalizer. The positive fixed-torus cases use a central quotient or a
proper connected torus centralizer. The finite case uses the Chevalley line and
constancy of its Borel-fixed vector orbit. All three source branches are proved.
Conjugacy of Borels inside a parabolic then gives its self-normalization, and
applying that conclusion to its identity component proves connectedness.

This is Borel, *Linear Algebraic Groups*, IV, Theorem 11.16,
`refs/KGroup/Bor1/Chapter4.tex`, including the parabolic input to §13.7.
-/

namespace Theory.AlgebraicGroup.BorelSelfNormalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

/-- Borel 11.16: a Borel of a connected algebraic group is self-normalizing. -/
public theorem normalizer_eq (hG : Variety.IsConnected G)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) : B.normalizer = B := by
  obtain ⟨T, hT, hTB⟩ := BorelIntersectionGeometry.exists_maximalTorus_le_borel_of_conjugacy
    (fun _ _ hA hB => BorelGeometricConjugacy.conjugacy hA hB) B hB
  apply normalizer_eq_of_fixed_torus_cases ?_ ?_ hG B T hB hT hTB
  · intro H _ hH C S hC hS hSC n hnC hnS hfinite
    exact eq_top_of_finite_fixedPoints_of_vectorOrbit_constancy hH C S hC hS hSC n hnC hnS
      hfinite (normalizerChevalley_fixed_of_borel_fixed hH C hC)
  · intro H _ hH ih C S hC hS hSC n hnC hnS hinfinite
    exact mem_borel_of_infinite_fixedPoints hH ih C S hC hS hSC n hnC hnS hinfinite

/-- The parabolic normalizer clause of Borel 11.16, with no connectedness
assumption on the parabolic subgroup. -/
public theorem parabolic_normalizer_eq (hG : Variety.IsConnected G)
    (P : ClosedSubgroup G) (hP : IsParabolicSubgroup P) : P.normalizer = P := by
  obtain ⟨B, hB, hBP⟩ := hP
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro n hn
    have hCP : B.conjugate n ≤ P := by
      intro x hx
      have hxP := hBP ((B.mem_conjugate_iff n x).mp hx)
      have h := (Subgroup.mem_normalizer_iff.mp hn _).mp hxP
      change x ∈ P.toSubgroup
      simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] using h
    obtain ⟨p, hp⟩ := BorelGeometricConjugacy.conjugacy
      (hB.preimage_inclusion_of_le hBP) ((hB.conjugate n).preimage_inclusion_of_le hCP)
    have hconj : B.conjugate n = B.conjugate (P.inclusion.onPoints p) := by
      have himage := congrArg (fun L : ClosedSubgroup P.carrierVariety =>
        letI := L.carrierAlgebraicGroup
        (P.inclusion.comp L.inclusion).imageClosedSubgroup) hp
      rw [P.inclusion_image_preimage_of_le (B.conjugate n) hCP,
        P.inclusion_image_conjugate,
        P.inclusion_image_preimage_of_le B hBP] at himage
      exact himage
    let a := (P.inclusion.onPoints p)⁻¹ * n
    have ha : B.conjugate a = B := by
      dsimp only [a]
      rw [← B.conjugate_conjugate, hconj, ClosedSubgroup.conjugate_conjugate,
        inv_mul_cancel, B.conjugate_one]
    have haN : a ∈ B.normalizer.toSubgroup := by
      apply Subgroup.mem_normalizer_iff.mpr
      intro x
      have hx := (B.mem_conjugate_iff a (a * x * a⁻¹))
      rw [ha] at hx
      change (a * x * a⁻¹ ∈ B.toSubgroup ↔ a⁻¹ * (a * x * a⁻¹) * a ∈ B.toSubgroup) at hx
      simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hx.symm
    rw [normalizer_eq hG B hB] at haN
    have hpa := P.toSubgroup.mul_mem (P.pointEquiv p).property (hBP haN)
    change P.inclusion.onPoints p * ((P.inclusion.onPoints p)⁻¹ * n) ∈ P.toSubgroup at hpa
    change n ∈ P.toSubgroup
    simpa only [mul_inv_cancel_left] using hpa
  · intro n hn
    exact Subgroup.le_normalizer hn

/-- The identity component of an actual parabolic is the entire parabolic. -/
public theorem parabolic_identityComponent_eq (hG : Variety.IsConnected G)
    (P : ClosedSubgroup G) (hP : IsParabolicSubgroup P) : P.identityComponentAmbient = P := by
  obtain ⟨B, hB, hBP⟩ := hP
  have hBI : B ≤ P.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient B P hB.connected hBP
  have hI := parabolic_normalizer_eq hG P.identityComponentAmbient ⟨B, hB, hBI⟩
  have hPI : P ≤ P.identityComponentAmbient.normalizer :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer P.identityComponentAmbient_le).mp
      P.identityComponentAmbient_normal
  rw [hI] at hPI
  apply SetLike.coe_injective
  exact Set.Subset.antisymm P.identityComponentAmbient_le hPI

/-- The connectedness clause of Borel 11.16 for the original parabolic. -/
public theorem parabolic_isConnected (hG : Variety.IsConnected G)
    (P : ClosedSubgroup G) (hP : IsParabolicSubgroup P) :
    _root_.IsConnected (P : Set (Variety.Point G)) := by
  rw [← parabolic_identityComponent_eq hG P hP]
  exact P.identityComponentAmbient_isConnected

end Theory.AlgebraicGroup.BorelSelfNormalizer
