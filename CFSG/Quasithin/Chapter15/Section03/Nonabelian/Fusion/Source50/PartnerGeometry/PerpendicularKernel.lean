module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.RankOneGeneration
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Intersection

/-!
# The transverse intersection lies in the original two-core

Each elementary partner contains, and therefore centralizes, its marked
plane. Their intersection centralizes the sum of the two planes, namely
the singular perpendicular hyperplane. The determinant group acts faithfully
on that hyperplane, placing the intersection in the original two-core.
Source: Aschbacher–Smith 15.3.56(5), printed p.1148.
-/
@[expose] public noncomputable section
open Matrix Subgroup ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup

namespace MatrixOrbit
/-- Pointwise fixation of a singular perpendicular forces the determinant
actor to be the identity. -/
theorem perp_pointwise_kernel (X : M) (hX : X ≠ 0) (hs : X.det = 0)
    (a : PairSL (F := ZMod 2))
    (ha : ∀ v : M, determinantForm.polarBilin v X = 0 → matrixAction a v = v) : a = 1 := by
  have hh : ∀ v : M, (v+X).det-v.det-X.det=0 → matrixAction a v = v := by
    intro v hv
    apply ha v
    simpa only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      determinantForm_apply] using hv
  by_contra hne
  obtain ⟨v,hv,hm⟩ := (show ∀ X : M, X ≠ 0 → X.det=0 →
    ∀ a : PairSL (F := ZMod 2), a ≠ 1 →
      ∃ v : M, (v+X).det-v.det-X.det=0 ∧ matrixAction a v ≠ v
    by decide +kernel) X hX hs a hne
  exact hm (hh v hv)

end MatrixOrbit

variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

include d in
theorem centralizer_perpendicular_le_core :
    D.I g ⊓ centralizer (D.V : Set G) ≤ D.S g := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  intro i hi
  let iI : D.I g := ⟨i,hi.1⟩
  have hmatrix : matrixSection d iI = 1 := by
    apply MatrixOrbit.perp_pointwise_kernel _ hz (d.pointVector_det z)
    intro v hv
    have hV : matrixLift d (Multiplicative.ofAdd v) ∈ D.V := by
      change (d.coordinates.symm (Multiplicative.ofAdd v) : G) ∈ D.V
      apply (d.perpendicular _).mpr
      intro w
      rw [d.coordinates.apply_symm_apply]
      change determinantForm.polarBilin v (d.pointVector w) = 0
      rcases d.pointVector_zero_or_eq z hz w with hw | hw
      · rw [hw,map_zero]
      · rw [hw]
        exact hv
    apply Multiplicative.ofAdd.injective
    apply matrixLift_injective d
    change matrixLift d (Multiplicative.ofAdd
      (matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' _ iI))
        (Multiplicative.ofAdd v).toAdd)) = _
    rw [matrixLift_equivariant]
    have hc := hi.2 _ hV
    change matrixLift d (Multiplicative.ofAdd v) * i = i * matrixLift d (Multiplicative.ofAdd v) at hc
    change i * matrixLift d (Multiplicative.ofAdd v) * i⁻¹ = _
    rw [← hc,mul_inv_cancel_right]
  refine ⟨iI, ?_, rfl⟩
  rw [← matrixSection_ker d]
  exact hmatrix

include d in
/-- An arbitrary elementary subgroup with these literal plane markings
satisfies the precise original-core containment needed by the factor argument. -/
theorem elementary_transverse_intersection_le_core (E V₀ : Subgroup G) (t : G)
    (hEI : E ≤ D.I g) (hVE : V₀ ≤ E) (hE : IsElementaryAbelian 2 E)
    (hjoin : V₀ ⊔ rightConjugate V₀ t = D.V) :
    E ⊓ rightConjugate E t ≤ D.S g := by
  let := hE
  have hEC : E ≤ centralizer (V₀ : Set G) := E.le_centralizer.trans (centralizer_le hVE)
  have hEtC : rightConjugate E t ≤ centralizer (rightConjugate V₀ t : Set G) := by
    rw [← rightConjugate_centralizer]
    exact map_mono hEC
  apply (le_inf (inf_le_left.trans hEI) ?_).trans (centralizer_perpendicular_le_core d)
  intro x hx
  have hV : V₀ ⊔ rightConjugate V₀ t ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hEC hx.1 v hv)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hEtC hx.2 v hv)
  rw [hjoin] at hV
  exact fun v hv => mem_centralizer_singleton_iff.mp (hV hv)

/-- Literal source56 consumer for the actual F∩Fʸ. -/
theorem intersectionE_transverse_le_core (Z ZS : Subgroup G) (y t : G)
    (hU : closureU Z ZS = D.U)
    (hV₀ : localSpan D.V₁ (leftResidual d) ≤ intersectionE Z ZS y)
    (hE : IsElementaryAbelian 2 (intersectionE Z ZS y))
    (hjoin : localSpan D.V₁ (leftResidual d) ⊔
      rightConjugate (localSpan D.V₁ (leftResidual d)) t = D.V) :
    intersectionE Z ZS y ⊓ rightConjugate (intersectionE Z ZS y) t ≤ D.S g := by
  apply elementary_transverse_intersection_le_core d _ _ t ?_ hV₀ hE hjoin
  exact (inf_le_left.trans inf_le_left : intersectionE Z ZS y ≤ closureU Z ZS).trans
    (hU.symm ▸ (show D.U ≤ D.I g from le_sup_left))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
