module
public import Theory.Frattini.SquareImage
public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.Group.Hom.Instances
public import Theory.ElementaryAbelian.Injective

/-!
# The second central quotient paired with the Frattini quotient

For a finite group P with elementary abelian center, the commutator of an
element of Z₂(P) with an arbitrary element of P is central. The commutator
identities make this multiplicative in both variables. Each row kills Φ(P)
because its image has exponent two. The kernel in the first variable is
exactly Z(P), giving a faithful pairing of Z₂(P)/Z(P) with P/Φ(P), valued
in the actual center and equivariant under every automorphism of P.

Consequently Z₂(P) centralizes Φ(P), its central quotient is elementary,
and its exponent divides four. For a nonabelian finite two-group the
upper section is nontrivial. No class-two hypothesis on P is used.
The application in LinearThreeMS.NonbinarySource.SecondCenterSections
retains the original groups and center marking in the upper-section
reconstruction for Aschbacher–Smith C.1.34, printed pp.136–137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.SecondCenterFrattini
variable {P : Type*} [Group P]
local notation "Z₂" => Subgroup.upperCentralSeries P 2

private theorem bracket_mem (x : Z₂) (y : P) : ⁅(x:P),y⁆ ∈ center P := by
  simpa only [Subgroup.upperCentralSeries_one] using
    (Subgroup.mem_upperCentralSeries_succ_iff.mp x.property y)

private def bracket : Z₂ →* (P →* center P) where
  toFun x := {
    toFun y := ⟨⁅(x:P),y⁆,bracket_mem x y⟩
    map_one' := Subtype.ext (by simp)
    map_mul' y z := by
      apply Subtype.ext
      change ⁅(x:P),y*z⁆=⁅(x:P),y⁆*⁅(x:P),z⁆
      rw [commutatorElement_mul_right_eq_mul_conj,
        mul_assoc ⁅(x:P),y⁆ y ⁅(x:P),z⁆,
        mem_center_iff.mp (bracket_mem x z) y]
      simp only [←mul_assoc,mul_inv_cancel_right] }
  map_one' := by
    ext y
    change ⁅(1:P),y⁆=1
    simp
  map_mul' x y := by
    ext z
    change ⁅(x:P)*(y:P),z⁆=⁅(x:P),z⁆*⁅(y:P),z⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (bracket_mem y z) (x:P),mul_inv_cancel_right]
    exact (mem_center_iff.mp (bracket_mem y z) ⁅(x:P),z⁆).symm

variable [Finite P] [IsElementaryAbelian 2 (center P)]
private theorem bracket_frattini (x : Z₂) : frattini P ≤ (bracket x).ker :=
  frattini_le_ker_of_square_image (bracket x) (fun y =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center P)) (bracket x y))

private def frattiniBracket : Z₂ →* ((P ⧸ frattini P) →* center P) where
  toFun x := QuotientGroup.lift (frattini P) (bracket x) (bracket_frattini x)
  map_one' := by
    apply MonoidHom.ext
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) y
    apply Subtype.ext
    change (bracket 1 y : P)=1
    simp only [map_one,MonoidHom.one_apply,coe_one]
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) z
    apply Subtype.ext
    change (bracket (x*y) z:P)=(bracket x z:P)*(bracket y z:P)
    rw [map_mul]
    rfl

private theorem frattiniBracket_kernel :
    (frattiniBracket (P := P)).ker=(center P).subgroupOf Z₂ := by
  ext x
  change frattiniBracket x=1 ↔ (x:P)∈center P
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    have hh := congrArg (fun f : (P ⧸ frattini P) →* center P =>
      (f (QuotientGroup.mk' (frattini P) y):P)) hx
    change ⁅(x:P),y⁆=1 at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  · intro hx
    apply MonoidHom.ext
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) y
    apply Subtype.ext
    change ⁅(x:P),y⁆=1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm

/-- The actual commutator embeds the second central quotient in the dual
of the whole Frattini quotient with values in the whole center. -/
def pairing : (Z₂ ⧸ (center P).subgroupOf Z₂) →* ((P ⧸ frattini P) →* center P) :=
  QuotientGroup.lift _ frattiniBracket frattiniBracket_kernel.ge

/-- Evaluation is the original commutator, on the original quotient maps. -/
theorem pairing_apply (x : Z₂) (y : P) :
    (pairing (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini P) y):P)=⁅(x:P),y⁆ := by rfl

/-- The whole center is exactly the left radical. -/
theorem pairing_injective : Function.Injective (pairing (P := P)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective ((center P).subgroupOf Z₂) v
  apply (QuotientGroup.eq_one_iff x).mpr
  exact frattiniBracket_kernel.le (show x∈(frattiniBracket (P := P)).ker from hv)

/-- Simultaneous transport of both arguments transports the central value. -/
theorem pairing_automorphism (a : MulAut P) (x : Z₂) (y : P) :
    pairing (QuotientGroup.mk' _ (MulAut.characteristic Z₂ a x))
      (QuotientGroup.mk' (frattini P) (a y)) =
        centerCongr a (pairing (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini P) y)) := by
  apply Subtype.ext
  rw [pairing_apply]
  change ⁅a (x:P),a y⁆=a ⁅(x:P),y⁆
  exact (map_commutatorElement a (x:P) y).symm

/-- The second center lies in the actual centralizer of the Frattini subgroup. -/
theorem second_le_frattini_centralizer : Z₂ ≤ centralizer (frattini P : Set P) := by
  intro x hx y hy
  have hh := congrArg (center P).subtype (bracket_frattini (⟨x,hx⟩ : Z₂) hy)
  change ⁅x,y⁆=1 at hh
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

/-- The second central quotient has exponent two and is commutative. -/
theorem second_quotient_elementary : IsElementaryAbelian 2 (Z₂ ⧸ (center P).subgroupOf Z₂) := by
  let E := ((P ⧸ frattini P) →* center P)
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro f
      apply MonoidHom.ext
      intro y
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center P)) (f y)) }
  exact IsElementaryAbelian.of_injective pairing pairing_injective

/-- Squares in the second center are central. -/
theorem second_square_mem_center (x : Z₂) : (x:P)^2∈center P := by
  let := second_quotient_elementary (P := P)
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Z₂ ⧸ (center P).subgroupOf Z₂))
    (QuotientGroup.mk' _ x)
  rw [←map_pow] at hh
  exact (QuotientGroup.eq_one_iff (x^2)).mp hh

/-- The second center has exponent dividing four. -/
theorem second_fourth_power (x : Z₂) : (x:P)^4=1 := by
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) ((x:P)^2) (second_square_mem_center x)
  simpa only [←pow_mul] using hh

omit [IsElementaryAbelian 2 (center P)] in
/-- For a nonabelian finite two-group this is a genuine nonzero upper section. -/
theorem center_lt_second (hP : IsPGroup 2 P) (hna : ¬IsMulCommutative P) :
    center P < Z₂ := by
  have hle : center P ≤ Z₂ := by
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono P (show 1≤2 by decide)
  apply lt_of_le_of_ne hle
  intro he
  have ht : center P ≠ ⊤ := fun hh => hna (center_eq_top_iff.mp hh)
  let : Nontrivial (P ⧸ center P) := QuotientGroup.nontrivial_iff.mpr ht
  have hn := (hP.to_quotient (center P)).bot_lt_center
  have hc : center (P ⧸ center P) = ⊥ := by
    apply bot_unique
    intro x hx
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    have hy : y∈Z₂ := by
      rw [←Subgroup.comap_upperCentralSeries_quotient_center 1,
        Subgroup.upperCentralSeries_one]
      exact hx
    exact (QuotientGroup.eq_one_iff y).mpr (he.ge hy)
  exact hn.ne hc.symm

end Theory.GroupTheory.SecondCenterFrattini
