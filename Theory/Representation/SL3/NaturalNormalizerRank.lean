module
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary actors normalizing the natural SL₃ action

On an elementary two-group, a natural-module action and its induced
SL₃ automorphism action have the same kernel. An involution in the latter
kernel is a scalar on the natural module, hence is the identity in
characteristic two. Faithfulness of the natural representation gives the
reverse inclusion.

Perfectness embeds Aut(SL₃) into Aut(PSL₃) without discarding the full
scalar center. The proved automorphism rank calculation therefore bounds
the natural action image by 2^(2n). This includes field automorphisms.
The original MS application is in NonblockMSOutsideRank.

Source: Aschbacher–Smith C.1.35, printed p.139, the bound on the outside
image in (**); the automorphism rank is recorded in G.9.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.SL3NaturalFixed
variable {F H : Type*} [Field F] [Finite F] [CharP F 2] [Group H]

omit [Finite F] in
/-- An involutory additive centralizer of natural SL₃ is the identity. -/
theorem involution_centralizer_eq_one
    (f : (Fin 3 → F) ≃+ (Fin 3 → F)) (hsq : Function.Involutive f)
    (hf : ∀ g v, f (specialLinearNatural 3 g v) = specialLinearNatural 3 g (f v)) :
    f = AddEquiv.refl _ := by
  obtain ⟨a,ha⟩ := SL3OddNaturalNormalizer.centralizer_scalar f.toAddMonoidHom hf
  change ∀ v, f v = a • v at ha
  have haa : a * a = 1 := by
    have h := congrFun (hsq (Pi.single 0 1)) 0
    rw [ha,ha,smul_smul] at h
    simpa using h
  have ha1 : a = 1 := by
    have h : (a + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq,pow_two,haa,one_pow,CharTwo.add_self_eq_zero]
    have hz := sq_eq_zero_iff.mp h
    have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
    exact (eq_neg_of_add_eq_zero_left hz).trans hneg
  apply AddEquiv.ext
  intro v
  change f v = v
  simpa only [ha1,one_smul] using ha v

omit [Finite F] in
/-- On actors of exponent two, the natural and induced automorphism actions
have the same kernel, with the full SL₃ center retained. -/
theorem natural_actor_ker_eq
    (β : H →* MulAut (Multiplicative (Fin 3 → F)))
    (α : H →* MulAut (Matrix.SpecialLinearGroup (Fin 3) F))
    (hsq : ∀ x : H, x^2=1)
    (hi : ∀ x g v, (β x (Multiplicative.ofAdd (specialLinearNatural 3 g v))).toAdd =
      specialLinearNatural 3 (α x g) (β x (Multiplicative.ofAdd v)).toAdd) :
    β.ker = α.ker := by
  ext x
  change β x = 1 ↔ α x = 1
  constructor
  · intro hx
    apply MulEquiv.ext
    intro g
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    change specialLinearNatural 3 (α x g) v = specialLinearNatural 3 g v
    have hh := hi x g v
    rw [hx] at hh
    exact hh.symm
  · intro hx
    let f := (β x).toAdditive
    have hff : Function.Involutive f := by
      intro v
      have hh : (β x)^2=1 := by rw [←map_pow,hsq,map_one]
      exact congrArg (fun a : MulAut (Multiplicative (Fin 3 → F)) =>
        (a (Multiplicative.ofAdd v)).toAdd) hh
    have hf : f = AddEquiv.refl _ := involution_centralizer_eq_one f hff
      (fun g v => by
        change (β x (Multiplicative.ofAdd (specialLinearNatural 3 g v))).toAdd =
          specialLinearNatural 3 g (β x (Multiplicative.ofAdd v)).toAdd
        simpa only [hx,MulAut.one_apply] using hi x g v)
    apply MulEquiv.ext
    intro v
    exact congrArg (fun a : (Fin 3 → F) ≃+ (Fin 3 → F) => a v.toAdd) hf

/-- An elementary natural-normalizing action has image of order at most q². -/
theorem natural_actor_card_le [IsElementaryAbelian 2 H]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (β : H →* MulAut (Multiplicative (Fin 3 → F)))
    (α : H →* MulAut (Matrix.SpecialLinearGroup (Fin 3) F))
    (hi : ∀ x g v, (β x (Multiplicative.ofAdd (specialLinearNatural 3 g v))).toAdd =
      specialLinearNatural 3 (α x g) (β x (Multiplicative.ofAdd v)).toAdd) :
    Nat.card β.range ≤ 2^(2*n) := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) := Atlas.sl_perfect 3 (by decide)
  let q := quotientAut (center (Matrix.SpecialLinearGroup (Fin 3) F))
  let γ := q.comp α
  have hq : Function.Injective q := MulAut.quotient_center_injective
  have hk : β.ker = γ.ker := by
    rw [natural_actor_ker_eq β α
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 H)) hi]
    exact (MonoidHom.ker_comp_of_injective α q hq).symm
  have he : Nat.card β.range = Nat.card γ.range := by
    rw [←index_ker,←index_ker,hk]
  rw [he]
  have hγ : IsElementaryAbelian 2 γ.range :=
    IsElementaryAbelian.of_surjective γ.rangeRestrict γ.rangeRestrict_surjective
  exact (primeRank_le_iff_elementary_card_le
    (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))).mp
    (Matrix.PSL3Even.automorphism_two_rank_eq F hn hF).le γ.range hγ

end Representation.SL3NaturalFixed
end
