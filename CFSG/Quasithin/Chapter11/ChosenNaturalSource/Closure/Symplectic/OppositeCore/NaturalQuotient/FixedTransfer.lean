module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Elementary
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Extracting the Cartan fixed subgroup from natural coordinates

For the literal induced I-action on Q/N, an intertwining additive isomorphism
with copies of the natural plane converts a nonidentity diagonal Cartan
element into the scalars t and t⁻¹. Both fixed coordinates vanish. A member
of C_Q(X₁) therefore maps to the identity in the original quotient, so lies
in its actual denominator N.

The natural coordinates and the marked diagonal element are explicit
inputs here. Their construction is not asserted by this extraction lemma.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative Matrix

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Natural coordinates for this same conjugation action give the Cartan
fixed-space bound, using an actual diagonal element of X₁. -/
theorem centralizer_le_of_natural_coordinates
    (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    {F : Type*} [Field F] (s : ℕ) :
    let I := oppositeJoin (auxiliaryW E) y
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    let _ := quotient_elementary E m hy hW hPhi hcore
    ∀ (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
      (_hρ : ∀ i : I, ∀ q : Q, ∀ hq : (i : G) * (q : G) * (i : G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i : G) * (q : G) * (i : G)⁻¹,hq⟩)
      (α : I →* SL(2,F))
      (e : Additive (Q ⧸ N.subgroupOf Q) ≃+ (Fin s → Fin 2 → F))
      (_he : ∀ i u k, e (Additive.ofMul (ρ i u)) k =
        Matrix.mulVec (α i).val (e (Additive.ofMul u) k))
      (x : G) (hx : x ∈ cartanKernel E) (t : F),
      t ≠ 1 → (α ⟨x,hXI hx⟩).val = Matrix.diagonal ![t,t⁻¹] →
      Q ⊓ centralizer (cartanKernel E : Set G) ≤ N := by
  dsimp only
  intro ρ hρ α e he x hx t ht hdiag
  let Q := corePair (auxiliaryW E) y
  let N := pairDenominator E y
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  let _ := quotient_elementary E m hy hW hPhi hcore
  let π := QuotientGroup.mk' (N.subgroupOf Q)
  intro q hq
  let qQ : Q := ⟨q,hq.1⟩
  let xI : oppositeJoin (auxiliaryW E) y := ⟨x,hXI hx⟩
  have hconj : x * q * x⁻¹ = q := by
    have hc := mem_centralizer_iff.mp hq.2 x hx
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : ρ xI (π qQ) = π qQ := by
    rw [hρ xI qQ (by change x * q * x⁻¹ ∈ Q; rw [hconj]; exact hq.1)]
    congr 1
    exact Subtype.ext hconj
  have hcoord := he xI (π qQ)
  have hz : e (Additive.ofMul (π qQ)) = 0 := by
    funext k j
    have hh := congrFun (hcoord k) j
    rw [hfix, hdiag] at hh
    simp only [Matrix.mulVec_diagonal] at hh
    fin_cases j
    · exact (mul_left_eq_self₀.mp hh.symm).resolve_left ht
    · exact (mul_left_eq_self₀.mp hh.symm).resolve_left (inv_ne_one.mpr ht)
  have hzero : Additive.ofMul (π qQ) = 0 := e.injective (hz.trans e.map_zero.symm)
  exact (QuotientGroup.eq_one_iff qQ).mp (congrArg Additive.toMul hzero)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
