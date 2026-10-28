module

public import Theory.Representation.NormalNineCentralInvolution.Action
public import Theory.Representation.NormalNineCentralInvolution.Weights

/-!
# The normal-nine binary obstruction

Let P be a normal elementary nine-group. A two-perfect subgroup Y whose
two-core acts nontrivially on P has the full SL₂(3) conjugation image.
If A centralizes Y and moves P, it contains an inverter of P. Pulling
back the original representation along P ⋊ X → X preserves faithfulness
on P and the literal action of A. The eight positive, equally sized
nonzero weights then give four moved dimensions.

No complement to P, faithful representation of the external semidirect
product, or equality A = Z(Y) is assumed. In fact the image and weight
arguments do not need the source's additional cardinality hypotheses on
A and Y/O₂(Y); they are retained in the source-facing statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.20, printed p.923 (PDF p.940).
-/

public section
open Subgroup Matrix
namespace Representation.NormalNineCentralInvolution
open AffineNine BinaryOffender
open Matrix.GeneralLinearGroup

/-- A faithful binary representation of the original ambient group has at
least four dimensions moved by the indicated order-two subgroup. -/
theorem four_le_fixedCodim
    {X V : Type*} [Group X] [Finite X] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (P Y A : Subgroup X) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (_hA : Nat.card A = 2)
    (hY : IsPPerfect 2 Y) (_hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hYA : Y ≤ centralizer (A : Set X))
    (hcore : ¬ Y.pCoreIn 2 ≤ centralizer (P : Set X))
    (hm : ⁅P, A⁆ ≠ ⊥) : 4 ≤ fixedCodim ρ A := by
  obtain ⟨t, j, _, ht, hconj, hSL, a, ha, haj, _⟩ :=
    exists_marked_action P Y A hP hY hcore hYA hm
  have hcompat : ∀ g : X, t.comp ((naturalAction.comp j) g).toMonoidHom =
      (MulAut.conj ((MonoidHom.id X) g)).toMonoidHom.comp t := by
    intro g
    ext x
    exact hconj g x
  let f : Affine j →* X := SemidirectProduct.lift t (MonoidHom.id X) hcompat
  have hfaith : Function.Injective (translationRepresentation j (ρ.comp f)) := by
    have he : translationRepresentation j (ρ.comp f) = ρ.comp t := by
      apply MonoidHom.ext
      intro x
      change ρ (f (SemidirectProduct.inl x)) = ρ (t x)
      exact congrArg ρ (SemidirectProduct.lift_inl t (MonoidHom.id X) hcompat x)
    rw [he]
    exact hρ.comp ht
  have hSL' : threeSpecialLinear ≤ j.range := by
    rw [← hSL]
    rintro s ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hb := affine_pullback_bound j (ρ.comp f) hfaith hSL' a haj
  have hmap : (zpowers (SemidirectProduct.inr a : Affine j)).map f = zpowers a := by
    rw [MonoidHom.map_zpowers]
    simp only [f, SemidirectProduct.lift_inr, MonoidHom.id_apply]
  have hb' : 4 ≤ fixedCodim ρ (zpowers a) := by
    unfold fixedCodim at hb ⊢
    rw [fixedSpace_comp_map ρ f _, hmap] at hb
    exact hb
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha))
  have hA := fixedCodim_add_finrank ρ A
  have ha' := fixedCodim_add_finrank ρ (zpowers a)
  omega

end Representation.NormalNineCentralInvolution
