module

public import Theory.GroupTheory.ClassTwoCentralPairing
import Mathlib.Tactic.Group

/-!
# Canonical coordinates and lifts for cubic central extensions

An involution inverting a central quotient and fixing its exponent-three
center gives canonical coordinates x ↦ (xZ, x α(x)). The coordinate map is
bijective; the multiplication cocycle is the original commutator pairing.
Consequently every compatible pair of quotient and center isomorphisms lifts
to an isomorphism of the groups, commuting with the distinguished involutions.
The construction uses no group-recognition input or preselected group model.

This is the extraspecial extension-lifting step in Aschbacher,
*Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {D : Type*} [Group D]
structure CubicCentralInversion (α : MulAut D) : Prop where
  center_cube : ∀ c : center D, c^3=1
  involutive : Function.Involutive α
  norm_central : ∀ x : D, x*α x ∈ center D
  fixes_center : ∀ c : center D, α c = c

namespace CubicCentralInversion
variable {α : MulAut D} (h : CubicCentralInversion α)

def norm (x : D) : center D := ⟨x*α x,h.norm_central x⟩
@[simp] theorem norm_coe (x : D) : (h.norm x : D) = x*α x := by rfl
@[simp] theorem norm_one : h.norm 1 = 1 := by apply Subtype.ext; simp

theorem norm_mul_center (x : D) (c : center D) : h.norm (x*c) = h.norm x*c^2 := by
  apply Subtype.ext
  change x*c*α (x*c) = (x*α x)*((c:D)^2)
  rw [map_mul,h.fixes_center c,pow_two]
  have hc := mem_center_iff.mp c.property (α x)
  calc
    x*c*(α x*c) = x*(c*α x)*c := by group
    _ = x*(α x*c)*c := by rw [hc]
    _ = _ := by group

theorem norm_center (c : center D) : h.norm c = c^2 := by
  simpa using h.norm_mul_center 1 c

theorem norm_involution (x : D) : h.norm (α x) = h.norm x := by
  apply Subtype.ext
  change α x * α (α x) = x*α x
  rw [h.involutive]
  have hc := mem_center_iff.mp (h.norm_central x) x
  exact mul_left_cancel (show x*(α x*x)=x*(x*α x) by simpa only [mul_assoc] using hc.symm)


def coordinatesFun (x : D) : (D ⧸ center D) × center D :=
  (QuotientGroup.mk' (center D) x,h.norm x)

theorem coordinates_injective : Function.Injective h.coordinatesFun := by
  intro x y he
  have hq := congrArg Prod.fst he
  have hn := congrArg Prod.snd he
  change h.norm x=h.norm y at hn
  let c : center D := ⟨x⁻¹*y,QuotientGroup.eq.mp hq⟩
  have hy : x*(c:D)=y := by simp [c]
  have hm := h.norm_mul_center x c
  rw [hy] at hm
  have htwo : c^2=1 := by
    apply mul_left_cancel (a := h.norm x)
    simpa only [mul_one] using hm.symm.trans hn.symm
  have hone : c=1 := by
    have hh := h.center_cube c
    simpa only [show 3=2+1 from rfl,pow_succ,htwo,one_mul] using hh
  have hc : x⁻¹*y=1 := congrArg Subtype.val hone
  exact inv_mul_eq_one.mp hc

theorem coordinates_surjective : Function.Surjective h.coordinatesFun := by
  rintro ⟨q,n⟩
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center D) q
  let c : center D := (n*(h.norm x)⁻¹)^2
  have hc : c^2=n*(h.norm x)⁻¹ := by
    change ((n*(h.norm x)⁻¹)^2)^2 = _
    rw [←pow_mul,show 2*2=3+1 from rfl,pow_succ,h.center_cube,one_mul]
  refine ⟨x*c,Prod.ext ?_ ?_⟩
  · change QuotientGroup.mk' (center D) (x*c)=q
    have hcq : QuotientGroup.mk' (center D) (c:D)=1 := (QuotientGroup.eq_one_iff _).mpr c.property
    rw [map_mul,hcq,mul_one,hx]
  · change h.norm (x*c)=n
    rw [h.norm_mul_center,hc]
    simp

noncomputable def coordinates : D ≃ (D ⧸ center D) × center D :=
  Equiv.ofBijective h.coordinatesFun ⟨h.coordinates_injective,h.coordinates_surjective⟩

@[simp] theorem coordinates_apply (x : D) :
    h.coordinates x = (QuotientGroup.mk' (center D) x,h.norm x) := by rfl

include h in
theorem quotient_involution (x : D) : QuotientGroup.mk' (center D) (α x) =
    (QuotientGroup.mk' (center D) x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [←map_mul]
  exact (QuotientGroup.eq_one_iff _).mpr (h.norm_central x)

variable [IsMulCommutative (D ⧸ center D)]

theorem norm_mul (x y : D) :
    h.norm (x*y) = CentralQuotient.pairing (QuotientGroup.mk' (center D) x)
      (QuotientGroup.mk' (center D) y) * h.norm x * h.norm y := by
  apply Subtype.ext
  simp only [norm_coe,Subgroup.coe_mul,CentralQuotient.pairing_mk_mk,map_mul]
  symm
  have hc := mem_center_iff.mp (h.norm_central x) y⁻¹
  calc
    ⁅x,y⁆*(x*α x)*(y*α y) = x*y*x⁻¹*(y⁻¹*(x*α x))*(y*α y) := by
      simp only [commutatorElement_def]; group
    _ = x*y*x⁻¹*((x*α x)*y⁻¹)*(y*α y) := by rw [hc]
    _ = _ := by group


variable {D' : Type*} [Group D'] {α' : MulAut D'} (h' : CubicCentralInversion α')
  [IsMulCommutative (D' ⧸ center D')]

noncomputable def coordinateLift (eQ : (D ⧸ center D) ≃* (D' ⧸ center D'))
    (eZ : center D ≃* center D') : D ≃ D' :=
  h.coordinates.trans ((eQ.toEquiv.prodCongr eZ.toEquiv).trans h'.coordinates.symm)

omit [IsMulCommutative (D ⧸ center D)] [IsMulCommutative (D' ⧸ center D')] in
@[simp] theorem coordinateLift_quotient
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D') (x : D) :
    QuotientGroup.mk' (center D') (h.coordinateLift h' eQ eZ x) =
      eQ (QuotientGroup.mk' (center D) x) := by
  have hh : h'.coordinates (h.coordinateLift h' eQ eZ x) =
      (eQ (QuotientGroup.mk' (center D) x),eZ (h.norm x)) := by
    simp [coordinateLift]
  exact congrArg Prod.fst hh

omit [IsMulCommutative (D ⧸ center D)] [IsMulCommutative (D' ⧸ center D')] in
@[simp] theorem coordinateLift_norm
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D') (x : D) :
    h'.norm (h.coordinateLift h' eQ eZ x) = eZ (h.norm x) := by
  have hh : h'.coordinates (h.coordinateLift h' eQ eZ x) =
      (eQ (QuotientGroup.mk' (center D) x),eZ (h.norm x)) := by
    simp [coordinateLift]
  exact congrArg Prod.snd hh

noncomputable def lift
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D')
    (hp : ∀ q r, eZ (CentralQuotient.pairing q r) =
      CentralQuotient.pairing (eQ q) (eQ r)) : D ≃* D' :=
  { h.coordinateLift h' eQ eZ with
    map_mul' x y := by
      apply h'.coordinates_injective
      apply Prod.ext
      · change QuotientGroup.mk' (center D') (h.coordinateLift h' eQ eZ (x*y)) =
          QuotientGroup.mk' (center D') (h.coordinateLift h' eQ eZ x * h.coordinateLift h' eQ eZ y)
        simp only [coordinateLift_quotient,map_mul]
      · change h'.norm (h.coordinateLift h' eQ eZ (x*y)) =
          h'.norm (h.coordinateLift h' eQ eZ x * h.coordinateLift h' eQ eZ y)
        rw [coordinateLift_norm,h.norm_mul,h'.norm_mul,map_mul,map_mul,hp,
          coordinateLift_quotient,coordinateLift_quotient,coordinateLift_norm,coordinateLift_norm] }

@[simp] theorem lift_quotient
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D')
    (hp : ∀ q r, eZ (CentralQuotient.pairing q r) = CentralQuotient.pairing (eQ q) (eQ r))
    (x : D) : QuotientGroup.mk' (center D') (h.lift h' eQ eZ hp x) =
      eQ (QuotientGroup.mk' (center D) x) := h.coordinateLift_quotient h' eQ eZ x

@[simp] theorem lift_norm
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D')
    (hp : ∀ q r, eZ (CentralQuotient.pairing q r) = CentralQuotient.pairing (eQ q) (eQ r))
    (x : D) : h'.norm (h.lift h' eQ eZ hp x) = eZ (h.norm x) :=
  h.coordinateLift_norm h' eQ eZ x


theorem lift_involution
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D')
    (hp : ∀ q r, eZ (CentralQuotient.pairing q r) = CentralQuotient.pairing (eQ q) (eQ r))
    (x : D) : h.lift h' eQ eZ hp (α x) = α' (h.lift h' eQ eZ hp x) := by
  apply h'.coordinates_injective
  apply Prod.ext
  · change QuotientGroup.mk' (center D') (h.lift h' eQ eZ hp (α x)) =
      QuotientGroup.mk' (center D') (α' (h.lift h' eQ eZ hp x))
    rw [lift_quotient,h.quotient_involution,h'.quotient_involution,lift_quotient,map_inv]
  · change h'.norm (h.lift h' eQ eZ hp (α x)) = h'.norm (α' (h.lift h' eQ eZ hp x))
    rw [lift_norm,h.norm_involution,h'.norm_involution,lift_norm]

theorem lift_center
    (eQ : (D ⧸ center D) ≃* (D' ⧸ center D')) (eZ : center D ≃* center D')
    (hp : ∀ q r, eZ (CentralQuotient.pairing q r) = CentralQuotient.pairing (eQ q) (eQ r))
    (c : center D) : h.lift h' eQ eZ hp c = eZ c := by
  apply h'.coordinates_injective
  apply Prod.ext
  · change QuotientGroup.mk' (center D') (h.lift h' eQ eZ hp c) =
      QuotientGroup.mk' (center D') (eZ c)
    rw [lift_quotient]
    have hc : QuotientGroup.mk' (center D) (c:D)=1 := (QuotientGroup.eq_one_iff _).mpr c.property
    have hc' : QuotientGroup.mk' (center D') (eZ c:D')=1 :=
      (QuotientGroup.eq_one_iff _).mpr (eZ c).property
    rw [hc,hc',map_one]
  · change h'.norm (h.lift h' eQ eZ hp c)=h'.norm (eZ c)
    rw [lift_norm,h.norm_center,h'.norm_center,map_pow]

end CubicCentralInversion
end Theory.GroupTheory
