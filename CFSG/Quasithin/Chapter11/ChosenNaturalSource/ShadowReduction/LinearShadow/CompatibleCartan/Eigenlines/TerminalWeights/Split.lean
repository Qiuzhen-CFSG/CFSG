module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.DiagonalMatrix
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Mathlib.Algebra.CharP.Two
/-!
# Split eigenvalues of the primitive Cartan actor

A nonidentity odd actor normalizing a rank-one Sylow subgroup is conjugate
to a split diagonal. A previously constructed nonidentity element in its
cyclic subgroup supplies a split basis; commuting with that element makes
the original actor diagonal in the same basis. The diagonal embedding
preserves multiplicative order, so no primitivity is lost.

TerminalWeights.GeneratorSource applies this to the actual generator of
X intersect K and its first-factor image.
Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "J" => SL(2,F)

/-- A nonidentity odd actor normalizing a root Sylow is split, with its
full multiplicative order retained by the displayed eigenvalue. -/
theorem split_odd_actor (R : Sylow 2 J) (g : J)
    (hg : g ∈ normalizer (R : Set J)) (ho : Odd (orderOf g)) (hne : g ≠ 1) :
    ∃ b : J, ∃ a : F, a ≠ 0 ∧ orderOf a = orderOf g ∧
      (b*g*b⁻¹).val = !![a,0;0,a⁻¹] := by
  have hC : zpowers g ≤ normalizer (R : Set J) := zpowers_le.mpr hg
  have hodd : Odd (Nat.card (zpowers g)) := by rwa [Nat.card_zpowers]
  have hnot : zpowers g ≠ ⊥ := by
    intro he
    have hm := mem_zpowers g
    rw [he,mem_bot] at hm
    exact hne hm
  obtain ⟨d,hd,b,a,ha,hdiag⟩ := CommonCore.Hall.exists_conjugate_diagonal
    (MonoidHom.id J) Function.surjective_id R (by simp) (zpowers g) hC hodd hnot
  let z := b*g*b⁻¹
  have hc : Commute g d := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hd
    exact (Commute.refl g).zpow_right n
  have he : z.val * !![a,0;0,a⁻¹] = !![a,0;0,a⁻¹] * z.val := by
    have hh := congrArg (fun x : J => x.val) ((hc.map (MulAut.conj b)).eq)
    change (z * (b*d*b⁻¹)).val = ((b*d*b⁻¹) * z).val at hh
    have hh' : z.val * (b*d*b⁻¹).val = (b*d*b⁻¹).val * z.val := hh
    simpa only [show (b*d*b⁻¹).val = !![a,0;0,a⁻¹] from hdiag] using hh'
  have hdiff : a ≠ a⁻¹ := by
    intro h
    have ha0 : a ≠ 0 := by
      intro hz
      have hdet := (b*d*b⁻¹).property
      change (b*d*b⁻¹).val.det = 1 at hdet
      rw [show (b*d*b⁻¹).val = !![a,0;0,a⁻¹] from hdiag,hz] at hdet
      simp at hdet
    apply ha
    apply CharTwo.sq_injective
    calc
      a^2 = a*a⁻¹ := by rw [sq,←h]
      _ = 1^2 := by rw [mul_inv_cancel₀ ha0,one_pow]
  have h01 : z.val 0 1 = 0 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) he
    have hh' : z.val 0 1 * a⁻¹ = z.val 0 1 * a := by
      simpa [mul_apply,Fin.sum_univ_two,mul_comm] using hh
    exact (mul_eq_mul_left_iff.mp hh').resolve_left (Ne.symm hdiff)
  have h10 : z.val 1 0 = 0 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) he
    have hh' : z.val 1 0 * a = z.val 1 0 * a⁻¹ := by
      simpa [mul_apply,Fin.sum_univ_two,mul_comm] using hh
    exact (mul_eq_mul_left_iff.mp hh').resolve_left hdiff
  have hdet : z.val 0 0 * z.val 1 1 = 1 := by
    simpa only [det_fin_two,h01,mul_zero,zero_mul,sub_zero] using z.property
  have hz0 : z.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : z.val 1 1 = (z.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hz : z = diag2 (z.val 0 0) hz0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe',h01,h10,h11]
  let f : Fˣ →* J := (rankOneBorel F).subtype.comp borelDiagonalHom
  have hf : Function.Injective f := by
    intro u v huv
    apply Units.ext
    exact congrArg (fun t : J => t.val 0 0) huv
  have horder : orderOf (z.val 0 0) = orderOf z := by
    have ht := orderOf_injective f hf (Units.mk0 (z.val 0 0) hz0)
    have hfz : f (Units.mk0 (z.val 0 0) hz0) = z := hz.symm
    rw [hfz] at ht
    exact (orderOf_units (y := Units.mk0 (z.val 0 0) hz0)).trans ht.symm
  refine ⟨b,z.val 0 0,hz0,?_,?_⟩
  · exact horder.trans (orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective g)
  · exact congrArg (fun t : J => t.val) hz |>.trans (diag2_coe' hz0)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
