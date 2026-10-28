module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Tactic
/-!
# Ten zeros from a singular plane in a binary four-space

A totally singular plane E is its own polar orthogonal complement. In any
linear complement F, the zero fiber over zero has four elements; every
nonzero fiber is an affine fiber of a nonzero linear functional on E, and
has two elements. Since F has four elements, the original form has ten
zeros. This proves the needed plus-type count without classifying forms.

Source application: Aschbacher--Smith, 14.3.15, the dihedral order-ten branch.
-/
public section
open Module Classical
namespace QuadraticForm.BinaryFour
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem card_linear_fiber_two {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hd : finrank (ZMod 2) E = 2)
    (l : E →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) (c : ZMod 2) :
    Nat.card {e : E // l e = c} = 2 := by
  have hs : Function.Surjective l := LinearMap.surjective hl
  have hk : finrank (ZMod 2) l.ker = 1 := by
    have hh := l.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_self, hd] at hh
    omega
  have he := AddMonoidHom.fiberEquivKerOfSurjective (f := l.toAddMonoidHom) hs c
  calc
    Nat.card {e : E // l e = c} = Nat.card l.ker := Nat.card_congr he
    _ = 2 := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hk]; decide

private theorem orthogonal_eq (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) V = 4)
    (E : Submodule (ZMod 2) V) (hE : finrank (ZMod 2) E = 2)
    (hs : ∀ e ∈ E, Q e = 0) : LinearMap.BilinForm.orthogonal Q.polarBilin E = E := by
  apply (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · intro e he x hx
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hs _ (E.add_mem hx he), hs _ hx, hs _ he, sub_zero]
  · rw [LinearMap.BilinForm.finrank_orthogonal hQ, hd, hE]

private theorem fiber_count (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) V = 4)
    (E : Submodule (ZMod 2) V) (hE : finrank (ZMod 2) E = 2)
    (hs : ∀ e ∈ E, Q e = 0) (F : Submodule (ZMod 2) V) (hc : IsCompl E F)
    (f : F) : Nat.card {e : E // Q ((e : V) + f) = 0} = if f = 0 then 4 else 2 := by
  classical
  by_cases hf : f = 0
  · subst f
    rw [if_pos rfl]
    have he : {e : E // Q ((e : V) + (0 : F)) = 0} ≃ E :=
      Equiv.subtypeUnivEquiv (by intro e; simpa using hs e e.property)
    rw [Nat.card_congr he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hE]
    decide
  · rw [if_neg hf]
    let l : E →ₗ[ZMod 2] ZMod 2 := (Q.polarBilin.flip f).comp E.subtype
    have hl : l ≠ 0 := by
      intro hz
      have hp : (f : V) ∈ LinearMap.BilinForm.orthogonal Q.polarBilin E := by
        intro e he
        exact LinearMap.congr_fun hz (⟨e,he⟩ : E)
      rw [orthogonal_eq Q hQ hd E hE hs] at hp
      have hz' : (f : V) = 0 := (Submodule.disjoint_def.mp hc.disjoint) f hp f.property
      exact hf (Subtype.ext hz')
    have he : {e : E // Q ((e : V) + f) = 0} ≃ {e : E // l e = -Q f} :=
      Equiv.subtypeEquivRight (fun e => by
        rw [QuadraticMap.map_add Q, hs e e.property, zero_add]
        change Q f + l e = 0 ↔ l e = -Q f
        constructor <;> intro hh
        · exact ((neg_eq_iff_add_eq_zero).mpr (by simpa [add_comm] using hh)).symm
        · exact (add_eq_zero_iff_eq_neg (a := Q f) (b := l e)).mpr (by simpa [eq_comm] using congrArg Neg.neg hh))
    rw [Nat.card_congr he]
    exact card_linear_fiber_two hE l hl _
/-- A singular plane in a nondegenerate binary four-space gives exactly ten
zeros of its original quadratic form. -/
theorem card_zero_of_singular_plane (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) V = 4)
    (E : Submodule (ZMod 2) V) (hE : finrank (ZMod 2) E = 2)
    (hs : ∀ e ∈ E, Q e = 0) : Nat.card {v : V // Q v = 0} = 10 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨F,hF⟩ := Submodule.exists_isCompl E
  let : Fintype F := Fintype.ofFinite _
  have hdF : finrank (ZMod 2) F = 2 := by
    have he := Submodule.finrank_add_eq_of_isCompl hF
    rw [hE,hd] at he
    omega
  have hcF : Fintype.card F = 4 := by
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdF]
    decide
  let e := Submodule.prodEquivOfIsCompl E F hF
  let e' : V ≃ (F × E) := e.toEquiv.symm.trans (Equiv.prodComm E F)
  have hcoord (v : V) : Q v = Q ((e' v).2.val + (e' v).1.val) := by
    exact congrArg Q (e.apply_symm_apply v).symm
  let c : {v : V // Q v = 0} ≃ (f : F) × {w : E // Q ((w : V) + f) = 0} :=
    (e'.subtypeEquiv (fun v => by rw [hcoord])).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun f : F => fun w : E => Q ((w : V) + f) = 0))

  rw [Nat.card_congr c,Nat.card_sigma]
  simp_rw [fiber_count Q hQ hd E hE hs F hF]
  have he : (∑ f : F, if f = 0 then 4 else 2) = 2 * Fintype.card F + 2 := by
    have hx : ∀ f : F, (if f = 0 then 4 else 2) = 2 + if f = 0 then 2 else 0 := by
      intro f
      split_ifs <;> rfl
    simp_rw [hx]
    simp [Finset.sum_add_distrib, Nat.mul_comm]
  rw [he,hcF]

end QuadraticForm.BinaryFour
