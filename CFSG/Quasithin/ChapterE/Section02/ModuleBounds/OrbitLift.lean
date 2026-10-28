module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ZeroIntersection

/-!
# Elementary cores from the original nonzero conjugation orbit

If the original conjugation action is transitive on nonzero vectors of
P/Z, every element outside Z is a conjugate of a fixed element of A,
up to a central involution. Thus every element of P has square one.
This retains both original quotient maps and supplies the elementary
lifting step of Aschbacher–Smith E.2.14(5), printed p.227.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation
open Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem P_elementary_of_quotient_nonzero_transitive
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    (∀ (a b : Additive ((P V M g).map q)), a ≠ 0 → b ≠ 0 →
      ∃ x : X, normalRepresentation ((P V M g).map q) (q x) a = b) →
      IsElementaryAbelian 2 (P V M g) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.elementary
  let := h.A_elementary
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  dsimp only
  intro ht
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A V M g, a ∉ Z V g := by
    by_contra! hh
    have ht := h.actor_rank_pos hproper hfit
    have hi : (Z V g).relIndex (A V M g) = 1 := relIndex_eq_one.mpr hh
    rw [hi,Nat.log_one_right] at ht
    omega
  have haU : q a ∈ U := mem_map_of_mem q (show a ∈ P V M g from
    (show A V M g ≤ P V M g from le_sup_right) ha)
  let av : Additive U := Additive.ofMul ⟨q a,haU⟩
  have ha0 : av ≠ 0 := by
    intro he0
    have he1 : q a = 1 := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g)) he0
    exact han ((QuotientGroup.eq_one_iff _).mp he1)
  have hp2 (p : P V M g) : p^2 = 1 := by
    apply Subtype.ext
    change (p : X)^2 = 1
    by_cases hpZ : (p : X) ∈ Z V g
    · exact elemPow_eq_one_of_isElementaryAbelian (A := V) p hpZ.1
    · have hpU : q p ∈ U := mem_map_of_mem q p.property
      let pv : Additive U := Additive.ofMul ⟨q p,hpU⟩
      have hp0 : pv ≠ 0 := by
        intro he0
        have he1 : q p = 1 := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g)) he0
        exact hpZ ((QuotientGroup.eq_one_iff _).mp he1)
      obtain ⟨x,hx⟩ := ht av pv ha0 hp0
      have hq : q (x*a*x⁻¹) = q p := by
        have hd := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g)) hx
        change q x * q a * (q x)⁻¹ = q p at hd
        simpa only [map_mul,map_inv] using hd
      let c := x*a*x⁻¹
      let z := c⁻¹ * (p : X)
      have hz : z ∈ Z V g := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q z = 1
        rw [map_mul,map_inv,hq,inv_mul_cancel]
      have hc2 : c^2 = 1 := by
        change (MulAut.conj x a)^2 = 1
        rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := A V M g) a ha,map_one]
      have hz2 : z^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := V) z hz.1
      have hcz : Commute c z := (mem_center_iff.mp
        ((h.core_geometry.2.2.trans inf_le_right) hz) c)
      have hpc : (p : X) = c*z := by dsimp [z]; group
      rw [hpc,hcz.mul_pow,hc2,hz2,one_mul]
  have hinv (p : P V M g) : p⁻¹ = p :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp2 p)
  exact { toIsMulCommutative := ⟨⟨fun a b => by
            calc a*b = (a*b)⁻¹ := (hinv _).symm
                 _ = b⁻¹*a⁻¹ := mul_inv_rev _ _
                 _ = b*a := by rw [hinv,hinv]⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp2 }
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
