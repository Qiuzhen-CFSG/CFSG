module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.SpecificGroups.SL2.UpperUnipotent
import Mathlib.Data.Matrix.Basis

/-!
# Orders of quadratic actors on the binary determinant module

A quadratic subgroup of `SL₂(F₄) × SL₂(F₄)` embeds in one of the two
coordinate factors. Indeed, if it contains a nonidentity actor `(1,b)`,
quadraticity says that every actor fixes every matrix `M (b⁻¹ - 1)`.
Testing matrix units shows that the first coordinate of every actor is
scalar, hence one in characteristic two. If there is no such actor,
the first coordinate projection is injective.

The existing upper-unipotent Sylow subgroup then bounds the order of an
elementary abelian two-subgroup by `|F₄| = 4`. This argument uses the literal
determinant action and needs neither an orthogonal-carrier comparison nor
a classification of fixed spaces.

Source: the quadratic-actor calculation in Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined manuscript (1 March 2004),
proof of 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
-/

public section
open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.QuadraticActors

/-- A nonzero family of matrices `M N` detects the left scalar factor. -/
private lemma left_eq_one {K : Type*} [Field K] [CharP K 2]
    (a : SpecialLinearGroup (Fin 2) K) (N P : Mat (F := K)) (hN : N ≠ 0)
    (h : ∀ M : Mat (F := K), a.val * M * N = M * P) : a = 1 := by
  obtain ⟨k, j, hkj⟩ : ∃ k j, N k j ≠ 0 := by
    by_contra! hn
    exact hN (by ext k j; exact hn k j)
  have he (r i : Fin 2) : a i r * N k j = if r = i then P k j else 0 := by
    have hh := congrArg (fun M : Mat (F := K) => M i j) (h (Matrix.single r k 1))
    fin_cases r <;> fin_cases k <;> fin_cases i <;>
      simpa [Matrix.mul_apply, Matrix.single] using hh
  have h10 : a 1 0 = 0 := by
    exact (mul_eq_zero.mp (by simpa using he 0 1)).resolve_right hkj
  have h01 : a 0 1 = 0 := by
    exact (mul_eq_zero.mp (by simpa using he 1 0)).resolve_right hkj
  have h0 : a 0 0 * N k j = P k j := by simpa using he 0 0
  have h1 : a 1 1 * N k j = P k j := by simpa using he 1 1
  have hd : a 0 0 = a 1 1 := mul_right_cancel₀ hkj (h0.trans h1.symm)
  have hs : a 0 0 ^ 2 = 1 := by
    simpa only [Matrix.det_fin_two, h10, h01, ← hd, mul_zero, sub_zero, pow_two]
      using a.property
  have h00 : a 0 0 = 1 := CharTwo.sq_injective (by simpa using hs)
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, ← hd, h00]

/-- The unipotent Sylow subgroup controls all two-subgroups of SL₂(F₄). -/
private lemma pgroup_card_le (H : Subgroup Representation.SL2FourNatural.SL)
    (hH : IsPGroup 2 H) : Nat.card H ≤ 4 := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  have hc : Nat.card P = 4 := by
    calc
      Nat.card P = Nat.card (SpecialLinearGroup.upperUnipotentSylow Binary.F 2) :=
        Nat.card_congr (P.equiv (SpecialLinearGroup.upperUnipotentSylow Binary.F 2)).toEquiv
      _ = Nat.card Binary.F := SpecialLinearGroup.card_upperUnipotent Binary.F
      _ = 4 := by rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
  exact (Subgroup.card_le_of_le hP).trans_eq hc

open Binary

/-- A nontrivial actor in the right factor forces the left projection to be trivial. -/
private lemma fst_eq_one_of_right_actor (a b : G) (hb : b.1 = 1) (hb2 : b.2 ≠ 1)
    (hq : ∀ M : V, action a (action b M - M) = action b M - M) : a.1 = 1 := by
  let N : V := b.2⁻¹.val - 1
  have hN : N ≠ 0 := by
    intro hh
    have he : b.2⁻¹ = 1 := Subtype.ext (sub_eq_zero.mp hh)
    exact hb2 (inv_eq_one.mp he)
  apply left_eq_one a.1 N (N * a.2.val) hN
  intro M
  have hd : action b M - M = M * N := by
    simp [action_apply, hb, N, mul_sub]
  have hh := hq M
  rw [hd] at hh
  have ht := congrArg (fun X : V => X * a.2.val) hh
  simpa only [action_apply, mul_assoc, ← SpecialLinearGroup.coe_mul,
    inv_mul_cancel, SpecialLinearGroup.coe_one, mul_one] using ht

private lemma card_le_of_injective (A : Subgroup G) (hA : IsPGroup 2 A)
    (f : A →* Representation.SL2FourNatural.SL) (hf : Function.Injective f) :
    Nat.card A ≤ 4 := by
  calc
    Nat.card A = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    _ ≤ 4 := pgroup_card_le f.range (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective)

/-- Every elementary abelian two-subgroup acting quadratically on the binary
determinant module has order at most four, including the trivial subgroup. -/
theorem card_le_four (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hq : Representation.BinaryOffender.IsQuadratic action A) : Nat.card A ≤ 4 := by
  classical
  let : IsElementaryAbelian 2 A := hA
  have hp := IsElementaryAbelian.isPGroup 2 A
  by_cases ht : ∀ a ∈ A, (a : G).1 = 1
  · let f : A →* Representation.SL2FourNatural.SL := (MonoidHom.snd _ _).comp A.subtype
    apply card_le_of_injective A hp f
    intro a b hab
    apply Subtype.ext
    exact Prod.ext ((ht a a.property).trans (ht b b.property).symm) hab
  · push Not at ht
    obtain ⟨a, ha, ha1⟩ := ht
    let f : A →* Representation.SL2FourNatural.SL := (MonoidHom.fst _ _).comp A.subtype
    apply card_le_of_injective A hp f
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro b hb
    have hb1 : (b.val : G).1 = 1 := hb
    have hb2 : (b.val : G).2 = 1 := by
      by_contra hne
      exact ha1 (fst_eq_one_of_right_actor a b.val hb1 hne (hq a ha b.val b.property))
    exact Subtype.ext (Prod.ext hb1 hb2)

end ClassicalOrthogonal.FourPlusMatrix.QuadraticActors
