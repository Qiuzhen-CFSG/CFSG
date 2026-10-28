module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicCentralizer
public import Theory.Mathieu.M22.CyclicFourCover
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Involutions in the original full cubic centralizer

Let H = C_G(z) and let X be the original cubic Sylow subgroup. Quotienting
C_H(X) by X produces a central double extension of the literal M22. The
native M22 involution-lifting theorem forces squares above M22 involutions
into X. For the original map C_H(X) → C_H(X)/⟨z⟩, those squares also lie
in the kernel of order two, so they are trivial.

Thus every lift of a square-one element in the original triple cover has
square one, and full inverse images of elementary two-subgroups are
elementary. The quotient maps and the original cubic marking are retained.
This supplies the involution-lifting step inside the centralizer used in
Aschbacher--Segev (4.8), printed p.599. An involution in the other coset of
N_H(X)/C_H(X), needed for (4.9), is a separate obligation.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), pp.598--599, DOI 10.1007/BF01232280.
The literal original Mathieu application is in
MathieuJ4RecognitionApplication.FullCubicInvolutions.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The original cubic, regarded as a subgroup of its full centralizer. -/
noncomputable def fullCubicScalar : Subgroup (fullCubicCentralizer e X) :=
  (cubicSylowImage e X).subgroupOf (fullCubicCentralizer e X)

theorem fullCubicScalar_central : fullCubicScalar e X ≤ center (fullCubicCentralizer e X) := by
  intro x hx
  exact mem_center_iff.mpr (fun c => Subtype.ext (c.property x.val hx).symm)

instance fullCubicScalar_normal : (fullCubicScalar e X).Normal :=
  ⟨fun x hx g => by
    rw [mem_center_iff.mp (fullCubicScalar_central e X hx) g, mul_inv_cancel_right]
    exact hx⟩

include h

private theorem cubic_le_centralizer : cubicSylowImage e X ≤ fullCubicCentralizer e X := by
  have hc : Nat.card (cubicSylowImage e X) = 3 := by
    rw [cubicSylowImage,card_map_of_injective (CubicLift.subgroup e).subtype_injective,
      cubicSylow_card e h X]
  let := isCyclic_of_prime_card hc
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨y,hy⟩ : cubicSylowImage e X) ⟨x,hx⟩)

theorem fullCubicScalar_card : Nat.card (fullCubicScalar e X) = 3 := by
  rw [fullCubicScalar,Nat.card_congr (subgroupOfEquivOfLe (cubic_le_centralizer h e X)).toEquiv,
    cubicSylowImage,card_map_of_injective (CubicLift.subgroup e).subtype_injective,
    cubicSylow_card e h X]

/-- Descend the original M22 marking through the same cubic subgroup. -/
noncomputable def fullCubicDoubleProjection :
    (fullCubicCentralizer e X ⧸ fullCubicScalar e X) →* M22 :=
  QuotientGroup.lift _ (fullCubicSimpleProjection h e X) (by
    rw [fullCubicSimpleProjection_ker]
    exact fullCubicScalar_central e X)

theorem fullCubicDoubleProjection_surjective : Function.Surjective (fullCubicDoubleProjection h e X) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (fullCubicSimpleProjection_surjective h e X) _

theorem fullCubicDoubleProjection_kernel_central :
    (fullCubicDoubleProjection h e X).ker ≤ center (fullCubicCentralizer e X ⧸ fullCubicScalar e X) := by
  rw [fullCubicDoubleProjection,QuotientGroup.ker_lift,fullCubicSimpleProjection_ker]
  rintro _ ⟨x,hx,rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (fullCubicScalar e X) y
  exact congrArg (QuotientGroup.mk' (fullCubicScalar e X)) (mem_center_iff.mp hx w)

theorem fullCubicDoubleProjection_kernel_card : Nat.card (fullCubicDoubleProjection h e X).ker = 2 := by
  have hc := Theory.GroupTheory.kernel_card_eq_mul_of_surjective_factor
    (fullCubicSimpleProjection h e X) (fullCubicDoubleProjection h e X)
    (QuotientGroup.mk' (fullCubicScalar e X)) (fullCubicDoubleProjection_surjective h e X)
    (QuotientGroup.mk'_surjective _) rfl
  rw [fullCubicSimpleProjection_ker,fullCubicCentralizer_center_card h e X,
    QuotientGroup.ker_mk',fullCubicScalar_card h e X] at hc
  omega

/-- Every square above an M22 involution belongs to the original cubic. -/
theorem fullCubic_square_mem_scalar (x : fullCubicCentralizer e X)
    (hx : fullCubicSimpleProjection h e X x ^ 2 = 1) : x ^ 2 ∈ fullCubicScalar e X := by
  have hs := M22CentralCover.square_eq_one_of_central_kernel_card_two
    (fullCubicDoubleProjection h e X) (fullCubicDoubleProjection_surjective h e X)
    (fullCubicDoubleProjection_kernel_central h e X) (fullCubicDoubleProjection_kernel_card h e X)
    (QuotientGroup.mk' _ x) hx
  apply (QuotientGroup.eq_one_iff (x ^ 2)).mp
  change (QuotientGroup.mk' (fullCubicScalar e X)) (x ^ 2) = 1
  rw [map_pow]
  exact hs

/-- Every lift of a square-one element in the original triple cover is square-one. -/
theorem fullCubic_square_eq_one (x : fullCubicCentralizer e X)
    (hx : fullCubicProjection h e X x ^ 2 = 1) : x ^ 2 = 1 := by
  have hm : x ^ 2 ∈ fullCubicScalar e X := fullCubic_square_mem_scalar h e X x (by
    change (innerProjection e) ((cubicCentralizerProjection h e X) (fullCubicProjection h e X x)) ^ 2 = 1
    rw [←map_pow,←map_pow,hx,map_one,map_one])
  have hk : x ^ 2 ∈ (fullCubicProjection h e X).ker := by
    rw [MonoidHom.mem_ker,map_pow,hx]
  have hthree := pow_card_eq_one' (x := (⟨x^2,hm⟩ : fullCubicScalar e X))
  rw [fullCubicScalar_card h e X] at hthree
  have htwo := pow_card_eq_one' (x := (⟨x^2,hk⟩ : (fullCubicProjection h e X).ker))
  rw [fullCubicProjection_kernel_card h e X] at htwo
  have h3 : (x^2)^3=1 := congrArg Subtype.val hthree
  have h2 : (x^2)^2=1 := congrArg Subtype.val htwo
  rw [show (x^2)^3 = (x^2)^2 * (x^2) from pow_succ _ 2,h2,one_mul] at h3
  exact h3

/-- The original triple-cover quotient lifts each involution to an involution. -/
theorem fullCubic_involution_lift (u : cubicCentralizer e X) (hu : orderOf u = 2) :
    ∃ x : fullCubicCentralizer e X, fullCubicProjection h e X x = u ∧ orderOf x = 2 := by
  obtain ⟨x,rfl⟩ := fullCubicProjection_surjective h e X u
  refine ⟨x,rfl,orderOf_eq_prime (fullCubic_square_eq_one h e X x
    ((orderOf_eq_prime_iff.mp hu).1)) ?_⟩
  intro he
  rw [he,map_one,orderOf_one] at hu
  omega
/-- Full inverse images of elementary subgroups of the original triple cover
are elementary, including the original central involution upstairs. -/
theorem fullCubic_elementary_preimage (A : Subgroup (cubicCentralizer e X))
    [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.comap (fullCubicProjection h e X)) := by
  have hs (x : A.comap (fullCubicProjection h e X)) : x ^ 2 = 1 :=
    Subtype.ext (fullCubic_square_eq_one h e X x.val
      (elemPow_eq_one_of_isElementaryAbelian _ x.property))
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

/-- Commuting involutions of the triple quotient have commuting lifts,
with the central involution retained. -/
theorem fullCubic_commute_of_square_one (a b : fullCubicCentralizer e X)
    (ha : fullCubicProjection h e X a ^ 2 = 1)
    (hb : fullCubicProjection h e X b ^ 2 = 1)
    (hab : Commute (fullCubicProjection h e X a) (fullCubicProjection h e X b)) :
    Commute a b := by
  have ha2 := fullCubic_square_eq_one h e X a ha
  have hb2 := fullCubic_square_eq_one h e X b hb
  have hab2 : (a*b)^2=1 := fullCubic_square_eq_one h e X (a*b) (by
    rw [map_mul,hab.mul_pow,ha,hb,one_mul])
  have haI : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
  have hbI : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb2)
  have habI : (a*b)⁻¹ = a*b := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using hab2)
  rw [mul_inv_rev,haI,hbI] at habI
  exact habI.symm

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
