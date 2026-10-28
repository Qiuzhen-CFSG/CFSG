module
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# Two-rank of the binary natural-plus-dual normalizer

The natural-plus-dual action is faithful and has trivial invertible commutant.
Conjugation therefore embeds its full linear normalizer in Aut(SL₃(2)). The
intrinsic two-rank is two, and the outer quotient has order two, giving the
sufficient upper bound three. No irreducibility of the six-space is assumed.

Source application: Aschbacher--Smith 10.1.1(5) and 10.2.12, pp.741,754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

theorem action_injective : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v, 0))

def normalizerAutomorphism : linearNormalizer action →* MulAut Group :=
  let hf : Function.Injective action.asGroupHom :=
    fun _ _ h => action_injective (congrArg Units.val h)
  let e : Group ≃* actionImage action := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage action).normalizerMonoidHom

theorem normalizerAutomorphism_intertwines
    (t : linearNormalizer action) (g : Group) (v : Space) :
    t.val.val (action g v) = action (normalizerAutomorphism t g) (t.val.val v) := by
  let hf : Function.Injective action.asGroupHom :=
    fun _ _ h => action_injective (congrArg Units.val h)
  let e : Group ≃* actionImage action := MonoidHom.ofInjective hf
  have he : action.asGroupHom (normalizerAutomorphism t g) =
      t.val * action.asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage action).normalizerMonoidHom t (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) Space)ˣ => u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change action (normalizerAutomorphism t g) (t.val.val v) =
    t.val.val (action g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

theorem normalizerAutomorphism_injective : Function.Injective normalizerAutomorphism := by
  apply (injective_iff_map_eq_one _).mpr
  intro t ht
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
  have hf : ∀ g v, f (action g v) = action g (f v) := by
    intro g v
    have he := normalizerAutomorphism_intertwines t g v
    rw [ht] at he
    exact he
  have he := centralizer_eq_one f hf
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact congrArg (fun e : Space ≃ₗ[ZMod 2] Space => e v) he

theorem automorphism_two_rank_le_three : primeRank 2 (MulAut Group) ≤ 3 := by
  have h := automorphism_primeRank_le_add_of_outer_card (p := 2) (n := 1)
    Matrix.PSL3Two.center_eq_bot
    (show Nat.card (MulAut.Outer Group) ≤ 2 ^ 1 by
      rw [Matrix.PSL3Two.Automorphisms.card_outer_sl]; decide)
  have hr : primeRank 2 Group = 2 := by
    rw [primeRank_equiv 2 Matrix.PSL3Two.equiv]
    exact Matrix.PSL3Even.two_rank (ZMod 2) (n := 1) (by decide) (by simp)
  simpa only [hr] using h

theorem linearNormalizer_two_rank_le_three : primeRank 2 (linearNormalizer action) ≤ 3 := by
  let : Finite Space := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) Space) :=
    Finite.of_injective (fun x : Module.End (ZMod 2) Space => (x : Space → Space))
      DFunLike.coe_injective
  exact (primeRank_le_of_injective 2 normalizerAutomorphism
    normalizerAutomorphism_injective).trans automorphism_two_rank_le_three

end BinaryLinearThree.NaturalDual
