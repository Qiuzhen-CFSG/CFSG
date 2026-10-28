module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The literal orthogonal action of a normalized quaternion seed

Conjugation on an embedded quaternion central product is expressed in the
concrete binary plus-space wreath model. Its kernel consists exactly of
actors centralizing the original seed modulo its center. Elementary
commutator images give singular displacement vectors in that same model.
Source: Aschbacher–Smith F.9.5(6.i), printed p.319.
-/
public section
open scoped commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- The wreath coordinates retain exactly the intrinsic quotient-action kernel. -/
theorem quotientWreathAction_eq_one_iff (a : MulAut Q) :
    d.quotientWreathAction a = 1 ↔ quotientAut (center Q) a = 1 := by
  constructor
  · intro ha
    rw [d.quotientWreathAction_eq] at ha
    have hs : d.squareIsometryAction a = 1 := d.squareIsometriesEquivWreath.injective
      (ha.trans d.squareIsometriesEquivWreath.map_one.symm)
    ext v
    have hh := congrArg (fun z : d.squareIsometries => z.val (Additive.ofMul v)) hs
    rw [d.squareIsometryAction_apply] at hh
    exact congrArg Additive.toMul hh
  · intro ha
    have hs : d.squareIsometryAction a = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      have hh := d.squareIsometryAction_apply a v.toMul
      rw [ha] at hh
      exact hh
    rw [d.quotientWreathAction_eq]
    rw [hs,map_one]

/-- Singular displacements are invariant under the exact square-form coordinates. -/
theorem wreath_singular_displacement (a : MulAut Q)
    (hs : ∀ x : Q, (a x * x⁻¹)^2 = 1) :
    ∀ v : BinaryFourPlus.V,
      BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val v-v) = 0 := by
  intro v
  obtain ⟨u,rfl⟩ := d.squareCoordinates.surjective v
  have ha : (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val
      (d.squareCoordinates u) = d.squareCoordinates ((d.squareIsometryAction a).val u) := by
    have hh (i : BinaryFourPlus.C2) :
        BinaryFourPlus.coordinate
          ((BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val (d.squareCoordinates u)) i =
        BinaryFourPlus.coordinate (d.squareCoordinates ((d.squareIsometryAction a).val u)) i := by
      rw [BinaryFourPlus.wreathToIsometry_coordinate]
      exact (d.quotientWreathAction_apply a u.toMul i).symm.trans
        (congrArg (fun w => BinaryFourPlus.coordinate (d.squareCoordinates w) i)
          (d.squareIsometryAction_apply a u.toMul).symm)
    exact Prod.ext (by simpa only [BinaryFourPlus.coordinate,ite_true] using hh 1)
      (by simpa only [BinaryFourPlus.coordinate,BinaryFourPlus.swapIndex_ne_one,ite_false]
        using hh BinaryFourPlus.swapIndex)
  rw [ha,←map_sub]
  rw [BinaryFourPlus.q_apply,←d.quadraticForm_squareCoordinates]
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center Q) u.toMul
  have hu : u = Additive.ofMul (QuotientGroup.mk' (center Q) x) :=
    congrArg Additive.ofMul hx.symm
  rw [hu,d.squareIsometryAction_apply,quotientAut_apply_mk]
  rw [←ofMul_div,←map_div,d.quadraticForm_apply,d.binarySquare_mk,
    d.centerCoordinate_eq_zero_iff]
  apply Subtype.ext
  change (a x / x)^2=1
  simpa only [div_eq_mul_inv] using hs x
end Subgroup.QuaternionCentralProductData

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Actual conjugation on a normalized embedded subgroup. -/
@[expose] def seedConjugation (I P : Subgroup G) (hn : I ≤ normalizer (P : Set G)) : I →* MulAut P :=
  P.normalizerMonoidHom.comp (inclusion hn)

omit [Finite G] in
theorem seedConjugation_apply (I P : Subgroup G) (hn : I ≤ normalizer (P : Set G))
    (x : I) (p : P) : (seedConjugation I P hn x p : G) = x*p*x⁻¹ := rfl

/-- The concrete orthogonal action of the original pair. -/
@[expose] noncomputable def seedOrthogonalAction (I P : Subgroup G)
    (hn : I ≤ normalizer (P : Set G)) (d : QuaternionCentralProductData P) :
    I →* BinaryFourPlus.Wreath := d.quotientWreathAction.comp (seedConjugation I P hn)

/-- The exact ambient centralizer-modulo-center is the action kernel. -/
theorem seedOrthogonalAction_ker (I P Z : Subgroup G)
    (hn : I ≤ normalizer (P : Set G)) (d : QuaternionCentralProductData P)
    (hz : (center P).map P.subtype = Z) (hIZ : I ≤ normalizer (Z : Set G)) :
    (seedOrthogonalAction I P hn d).ker = (commutatorPreimage I P Z).subgroupOf I := by
  ext x
  change d.quotientWreathAction (seedConjugation I P hn x) = 1 ↔ _
  rw [d.quotientWreathAction_eq_one_iff]
  change _ ↔ (x:G) ∈ commutatorPreimage I P Z
  rw [mem_commutatorPreimage_iff I P Z hIZ]
  simp only [x.property,true_and]
  constructor
  · intro hx p hp
    let pP : P := ⟨p,hp⟩
    have hh := DFunLike.congr_fun hx (QuotientGroup.mk' (center P) pP)
    rw [quotientAut_apply_mk] at hh
    have hc := QuotientGroup.eq_iff_div_mem.mp hh
    apply hz.le
    refine ⟨seedConjugation I P hn x pP / pP,hc,?_⟩
    change ((x:G)*p*(x:G)⁻¹)/p=⁅(x:G),p⁆
    simp only [div_eq_mul_inv,commutatorElement_def]
  · intro hx
    ext v
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hp := hx p p.property
    rw [←hz] at hp
    obtain ⟨z,hz',he⟩ := hp
    have he' : z = seedConjugation I P hn x p / p := by
      apply Subtype.ext
      change (z:G) = ((x:G)*(p:G)*(x:G)⁻¹)/(p:G)
      change (z:G) = ⁅(x:G),(p:G)⁆ at he
      simpa only [div_eq_mul_inv,commutatorElement_def] using he
    exact he' ▸ hz'
end Subgroup
