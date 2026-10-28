module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FieldCompatibility

/-!
# Exact U₅ mixed collection from the actual natural flag

Collect the actual displacement A(a)⁻¹ B(p) A(a) B(p)⁻¹ in the
intersection of the two source radicals. The ordered source root product
writes it as D(r) C(z). Evaluate this equality in the normalized SU₃ natural
section: the middle coordinate gives r.first = a*p.first, and the first
coordinate gives z = a*conj(p.second). Cancellation lifts this to the exact
B–A product in the original quotient. Thus the remaining Hermitian
correction is a constructed function, with only its central coordinate
still to be determined by the source torus argument.

The full nonabelian B and D roots are retained. MixedApplication constructs
all the natural-flag premises from the authorized original profile and
cover, and supplies the literal Q.q equation in either orientation.
Source: Fong--Seitz II (8C), (8.24), printed p.207, following (8.15).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X E K : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
local notation "d" => reflectedUnitaryChart Q split i j s b
local notation "N" => naturalSectionMap Q split j c
variable
  (hA : ∀ a : E, (naturalSectionMap Q split j c
    (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])
  (hC : ∀ a : E, (naturalSectionMap Q split j c
    (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])
  (hD : ∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c
    (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm)
      (reflectedUnitaryChart Q split i j s b p))).toAdd = ![0,k*J.conj p.val.1,0])

include hm hb hc hk hA hC hD in
omit [Finite E] in
/-- Full natural flag coordinates determine the noncentral D parameter and
the entire C parameter of the actual B–A crossing. Only D's central
coordinate is left as a constructed function. -/
theorem mixed_root_correction :
    ∃ T : hermitianUnipotentCoord J → E → hermitianUnipotentCoord J,
      (∀ p a, (T p a).val.1 = a*p.val.1) ∧
      ∀ p a, (b p : X ⧸ Q.D)*A a =
        A a*(d (T p a) : X ⧸ Q.D)*(γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
  have hex (p : hermitianUnipotentCoord J) (a : E) :
      ∃ r : hermitianUnipotentCoord J, r.val.1 = a*p.val.1 ∧
        (b p : X ⧸ Q.D)*A a = A a*(d r : X ⧸ Q.D)*
          (γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
    let bv := θ (hermitianUnipotentSU J hJ p)
    let v := (av a)⁻¹ * remainderRankOneAction Q split j hVj bv (av a)
    have hv : (v : X ⧸ Q.D) = (A a)⁻¹*(b p : X ⧸ Q.D)*A a*(b p : X ⧸ Q.D)⁻¹ := by
      change (A a)⁻¹ * (remainderRankOneAction Q split j hVj bv (av a) : X ⧸ Q.D) = _
      rw [remainderRankOneAction_apply]
      change (A a)⁻¹*((θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D)*A a*(θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D)⁻¹) = _
      rw [←hb]
      group
    let bi := inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 (b p)
    let ai := alignedPinning Q split i hVi μ s (Theory.PSL2.SemilinearCoverage.uni (ξ a))
    let w := remainderRankOneAction Q split i hVi ai⁻¹ bi * bi⁻¹
    have hw : (w : X ⧸ Q.D) = v := by
      change (remainderRankOneAction Q split i hVi ai⁻¹ bi : X ⧸ Q.D)*(bi : X ⧸ Q.D)⁻¹ = _
      rw [remainderRankOneAction_apply,hv]
      change (A a)⁻¹*(b p : X ⧸ Q.D)*((A a)⁻¹)⁻¹*(b p : X ⧸ Q.D)⁻¹ = _
      rw [inv_inv]
    obtain ⟨D,C,hDC⟩ := radical_intersection_factors Q split hm i j hij v (hw ▸ w.property) v.property
    let r := (d).symm D
    let z := (γ.symm C).toAdd
    have hr : d r = D := (d).apply_symm_apply D
    have hz : γ (.ofAdd z) = C := γ.apply_symm_apply C
    let dv := inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d r)
    let cv := inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd z))
    have hvdc : v = dv*cv := by
      apply Subtype.ext
      change (v : X ⧸ Q.D) = (d r : X ⧸ Q.D)*(γ (.ofAdd z) : X ⧸ Q.D)
      exact hDC.trans (congrArg₂ (· * ·) (congrArg Subtype.val hr.symm) (congrArg Subtype.val hz.symm))
    have hvec : (N v).toAdd = ![k*J.conj (a*J.conj p.val.2),k*J.conj (a*p.val.1),0] := by
      have he := hc (hermitianUnipotentSU J hJ p)
        (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) (av a)))
      change c (.ofMul (remainderFrattiniAction Q split j hVj bv
        (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) (av a)))) = _ at he
      rw [remainderFrattiniAction_mk] at he
      change (N (remainderRankOneAction Q split j hVj bv (av a))).toAdd =
        Matrix.mulVec (hermitianUnipotentMatrix J p) (N (av a)).toAdd at he
      change (N ((av a)⁻¹ * _)).toAdd = _
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he,hA]
      ext t
      fin_cases t <;> simp [hermitianUnipotentMatrix,CharTwo.neg_eq,map_mul]
      all_goals try rw [J.conj_involutive]
      all_goals ring_nf
      all_goals simp only [CharTwo.two_eq_zero,mul_zero]
    have hdcvec : (N v).toAdd = ![k*J.conj z,k*J.conj r.val.1,0] := by
      rw [hvdc,map_mul,toAdd_mul]
      change (N (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d r))).toAdd +
        (N (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd z)))).toAdd = _
      rw [hD,hC]
      ext t
      fin_cases t <;> simp
    have hrfirst : r.val.1 = a*p.val.1 := by
      apply J.conj.injective
      apply mul_left_cancel₀ hk
      exact congrFun (hdcvec.symm.trans hvec) 1
    have hzval : z = a*J.conj p.val.2 := by
      apply J.conj.injective
      apply mul_left_cancel₀ hk
      exact congrFun (hdcvec.symm.trans hvec) 0
    refine ⟨r,hrfirst,?_⟩
    have he : (A a)⁻¹*(b p : X ⧸ Q.D)*A a*(b p : X ⧸ Q.D)⁻¹ =
        (d r : X ⧸ Q.D)*(γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D) := by
      rw [←hv]
      have hh := congrArg Subtype.val hvdc
      change (v : X ⧸ Q.D) = (d r : X ⧸ Q.D)*(γ (.ofAdd z) : X ⧸ Q.D) at hh
      rwa [hzval] at hh
    calc
      _ = A a*((A a)⁻¹*(b p : X ⧸ Q.D)*A a*(b p : X ⧸ Q.D)⁻¹)*(b p : X ⧸ Q.D) := by group
      _ = _ := by rw [he]; group
  choose T hT using hex
  exact ⟨T,fun p a => (hT p a).1,fun p a => (hT p a).2⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
