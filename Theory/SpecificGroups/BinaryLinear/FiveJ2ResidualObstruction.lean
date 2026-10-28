module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Involutions
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The printed PSL₅(2) rank-two residual has an elementary-kernel obstruction

Let t = (1 + E₁₃)(1 + E₂₄) in the actual binary SL₅, hence PSL₅.
A simultaneous order-three action c on the two Jordan blocks commutes with t.
The shears u = 1 + E₁₅ and v = 1 + E₅₃ also commute with t. Thus c and
its conjugates by u and v lie in O²(C(t)). The product
(u c u c²)(v c v c²) has order four, as direct matrix calculations certify.
The canonical center quotient transports this element to the PSL fixed residual.

An extension of C₃ by an elementary abelian two-group has no element of
order four, whether or not the extension is given with a splitting.
Consequently the literal Z₃/(E₄ × E₄) entry in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 16.1.4(3), printed p.1171,
cannot describe this residual. The later use in 16.5.12, printed p.1200,
has the different expression Z₃/2^(4+4). This module proves the obstruction
to the former expression; it does not assume or identify the latter extension.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace BinaryLinear.FiveJ2ResidualObstruction
private abbrev G := SL(5, ZMod 2)
private def e (i j : Fin 5) : G :=
  if h : i ≠ j then Matrix.SpecialLinearGroup.transvection h 1 else 1
/-- The existing rank-two unipotent representative on the natural module. -/
abbrev slJ2 : SL(5, ZMod 2) := Representation.SL5ExteriorSquare.j₂
private def c : G := e 0 1 * e 1 0 * e 2 3 * e 3 2
private def u : G := e 0 4
private def v : G := e 4 2
private abbrev C := (MulAut.conj slJ2).fixedSubgroup
private def fixedOfCommutes {H : Type*} [Group H] (t x : H)
    (hx : x * t = t * x) : (MulAut.conj t).fixedSubgroup :=
  ⟨x, by
    rw [MulAut.mem_fixedSubgroup]
    change t * x * t⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr hx.symm⟩
private def c0 : C := fixedOfCommutes slJ2 c (by decide +kernel)
private def c1 : C := fixedOfCommutes slJ2 (u * c * u) (by decide +kernel)
private def c2 : C := fixedOfCommutes slJ2 (v * c * v) (by decide +kernel)
private theorem cubic_mem (x : C) (hx : x ^ 3 = 1) : x ∈ pResidual 2 C :=
  mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one hx))
private theorem c0_mem : c0 ∈ pResidual 2 C := cubic_mem c0 (by
  apply Subtype.ext
  change c ^ 3 = 1
  decide +kernel)
private theorem c1_mem : c1 ∈ pResidual 2 C := cubic_mem c1 (by
  apply Subtype.ext
  change (u * c * u) ^ 3 = 1
  decide +kernel)
private theorem c2_mem : c2 ∈ pResidual 2 C := cubic_mem c2 (by
  apply Subtype.ext
  change (v * c * v) ^ 3 = 1
  decide +kernel)
private def w : pResidual 2 C :=
  (⟨c1, c1_mem⟩ * ⟨c0, c0_mem⟩ * ⟨c0, c0_mem⟩) *
    (⟨c2, c2_mem⟩ * ⟨c0, c0_mem⟩ * ⟨c0, c0_mem⟩)
/-- The rank-two involution's actual SL fixed two-residual contains an
order-four element, exhibited by products of three-elements. -/
theorem sl_residual_has_four_element :
    ∃ w : pResidual 2 (MulAut.conj slJ2).fixedSubgroup, w ^ 4 = 1 ∧ w ^ 2 ≠ 1 := by
  refine ⟨w, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change ((u * c * u * c * c) * (v * c * v * c * c)) ^ 4 = 1
    decide +kernel
  · intro he
    have hh := congrArg (fun x : pResidual 2 C => ((x : C) : G)) he
    exact (by decide +kernel :
      ((u * c * u * c * c) * (v * c * v * c * c)) ^ 2 ≠ 1) hh

private theorem no_extension_of_four {N H : Type*} [Group N] [Group H]
    (hN : ∀ x : N, x ^ 2 = 1) (hH : ∃ w : H, w ^ 4 = 1 ∧ w ^ 2 ≠ 1) :
    ¬ Nonempty (GroupExtension N H (Multiplicative (ZMod 3))) := by
  rintro ⟨ext⟩
  obtain ⟨w, hw4, hw2⟩ := hH
  have hq3 : ext.rightHom w ^ 3 = 1 :=
    (by decide : ∀ x : Multiplicative (ZMod 3), x ^ 3 = 1) _
  have hq4 : ext.rightHom w ^ 4 = 1 := by rw [← map_pow, hw4, map_one]
  have hq : ext.rightHom w = 1 := by
    simpa only [show 4 = 3 + 1 from rfl, pow_add, hq3, pow_one, one_mul] using hq4
  have hwker : w ∈ ext.inl.range := by
    rw [ext.range_inl_eq_ker_rightHom]
    exact hq
  obtain ⟨x, rfl⟩ := hwker
  apply hw2
  rw [← map_pow, hN, map_one]
private noncomputable def pslEquivSL : PSL(5, ZMod 2) ≃* G :=
  BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)
/-- The image of the marked rank-two matrix under the actual central quotient. -/
noncomputable def pslJ2 : PSL(5, ZMod 2) := pslEquivSL.symm slJ2
private noncomputable def residualEquiv :
    pResidual 2 (MulAut.conj pslJ2).fixedSubgroup ≃* pResidual 2 C :=
  MulAut.fixedResidualEquivOfCompatible 2 pslEquivSL (MulAut.conj pslJ2) (MulAut.conj slJ2)
    (fun x => by
      simp only [MulAut.conj_apply, map_mul, map_inv]
      have ht : pslEquivSL pslJ2 = slJ2 := pslEquivSL.apply_symm_apply slJ2
      rw [ht])
/-- The order-four obstruction holds in the genuine PSL fixed two-residual. -/
theorem psl_residual_has_four_element : ∃ w : pResidual 2 (MulAut.conj pslJ2).fixedSubgroup,
    w ^ 4 = 1 ∧ w ^ 2 ≠ 1 := by
  obtain ⟨w, hw4, hw2⟩ := sl_residual_has_four_element
  refine ⟨residualEquiv.symm w, ?_, ?_⟩
  · rw [← map_pow, hw4, map_one]
  · intro he
    apply hw2
    apply residualEquiv.symm.injective
    rw [map_pow, he, map_one]
/-- No elementary abelian two-kernel and cyclic-three quotient can describe
the fixed two-residual, independently of any asserted action or splitting. -/
theorem psl_residual_no_elementary_cubic_extension {N : Type*} [Group N]
    (hN : ∀ x : N, x ^ 2 = 1) :
    ¬ Nonempty (GroupExtension N (pResidual 2 (MulAut.conj pslJ2).fixedSubgroup)
      (Multiplicative (ZMod 3))) :=
  no_extension_of_four hN psl_residual_has_four_element

/-- Transported versions of the same residual cannot have the printed
extension structure either. -/
theorem model_no_elementary_cubic_extension {N H : Type*} [Group N] [Group H]
    (hN : ∀ x : N, x ^ 2 = 1)
    (d : pResidual 2 (MulAut.conj pslJ2).fixedSubgroup ≃* H) :
    ¬ Nonempty (GroupExtension N H (Multiplicative (ZMod 3))) := by
  apply no_extension_of_four hN
  obtain ⟨w, hw4, hw2⟩ := psl_residual_has_four_element
  refine ⟨d w, ?_, ?_⟩
  · rw [← map_pow, hw4, map_one]
  · intro he
    apply hw2
    apply d.injective
    rw [map_pow, he, map_one]

/-- The marked projective element has exactly Suzuki type j₂: its natural
commutator space is two-dimensional. -/
theorem pslJ2_natural_rank :
    Module.finrank (ZMod 2) (LinearMap.range
      (Representation.SL5ExteriorSquare.naturalDisplacement
        (OuterCyclic.projectiveEquivSL (by decide) pslJ2))) = 2 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (Representation.SL5ExteriorSquare.naturalDisplacement (pslEquivSL pslJ2))) = 2
  rw [show pslEquivSL pslJ2 = slJ2 from pslEquivSL.apply_symm_apply slJ2]
  exact Representation.SL5ExteriorSquare.finrank_naturalDisplacement_j₂

private theorem conj_ne_one_of_noncommuting {H : Type*} [Group H] (a b : H)
    (hab : a * b ≠ b * a) : MulAut.conj a ≠ 1 := by
  intro he
  have hb := congrArg (fun r : MulAut H => r b) he
  change a * b * a⁻¹ = b at hb
  exact hab (mul_inv_eq_iff_eq_mul.mp hb)

/-- The actor in the counterexample is an involution of Aut(PSL₅(2)),
not merely an element whose square is one modulo the center. -/
theorem pslJ2_action_order : orderOf (MulAut.conj pslJ2) = 2 := by
  have ht : slJ2 ^ 2 = 1 := by decide +kernel
  have hs : MulAut.conj slJ2 ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hn : MulAut.conj slJ2 ≠ 1 := conj_ne_one_of_noncommuting slJ2 (e 2 0)
    (by decide +kernel)
  have ho : orderOf (MulAut.conj slJ2) = 2 := orderOf_eq_prime hs hn
  have hc : MulAut.congr pslEquivSL (MulAut.conj pslJ2) = MulAut.conj slJ2 := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj (pslEquivSL.apply_symm_apply slJ2)
  rw [← (MulAut.congr pslEquivSL).orderOf_eq, hc]
  exact ho

end BinaryLinear.FiveJ2ResidualObstruction
