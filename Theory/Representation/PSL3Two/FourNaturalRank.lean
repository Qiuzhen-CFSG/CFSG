module
public import Theory.Representation.PSL3Two.NaturalDualRank
public import Theory.Representation.ScalarMultiplicity.Faithful
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.GroupTheory.PrimeRankHom

/-!
# A sufficient two-rank bound for four equal binary natural copies

The normalizer acts on the faithfully marked SL₃(2). The kernel of this action
commutes with every natural operator, hence embeds in GL₄(2) on multiplicities.
Its two-rank is at most six by the group order. Aut(SL₃(2)) has two-rank at most
three, giving the sufficient full-normalizer bound nine. This avoids any
classification of elementary subgroups of the twelve-dimensional linear group.

Source application: Aschbacher--Smith 10.1.1(6) and 10.2.12, pp.741,754--755.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace BinaryLinearThree.FourNatural

/-- Four identical copies of the binary natural three-space. -/
abbrev Space := Fin 4 → Vector

local instance : Finite (Module.End (ZMod 2) Space) :=
  Finite.of_injective (fun x : Module.End (ZMod 2) Space => (x : Space → Space))
    DFunLike.coe_injective
local instance : Finite (Module.End (ZMod 2) (Fin 4 → ZMod 2)) :=
  Finite.of_injective (fun x : Module.End (ZMod 2) (Fin 4 → ZMod 2) =>
    (x : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))) DFunLike.coe_injective

/-- The same natural SL₃(2) operator on all four copies. -/
def action : Representation (ZMod 2) Group Space where
  toFun g := {
    toFun v i := W g (v i)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun W.map_one (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun (W.map_mul g h) (v i)

/-- The marked four-copy action is faithful. -/
theorem action_injective : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrFun (LinearMap.congr_fun he (fun _ => v)) 0

/-- Conjugation by the full linear normalizer on the marked component. -/
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

/-- The component centralizer embeds in the full multiplicity group GL₄(2). -/
theorem kernel_embeds_multiplicity :
    ∃ f : normalizerAutomorphism.ker →* (Module.End (ZMod 2) (Fin 4 → ZMod 2))ˣ,
      Function.Injective f := by
  let ρ : Representation (ZMod 2) normalizerAutomorphism.ker Space :=
    (normalizerRepresentation action).comp normalizerAutomorphism.ker.subtype
  apply ScalarMultiplicity.exists_injective_unit W ?_ ρ ?_ ?_
  · intro f hf
    exact SL3DoubledNaturalOffenders.natural_centralizer_scalar f.toAddMonoidHom hf
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hab
  · intro a g v
    have hh := normalizerAutomorphism_intertwines a.val g v
    rw [show normalizerAutomorphism a.val = 1 from a.property] at hh
    exact hh

/-- The order of GL₄(2) has two-part 64, a sufficient elementary rank bound. -/
theorem multiplicity_two_rank_le_six :
    primeRank 2 (Module.End (ZMod 2) (Fin 4 → ZMod 2))ˣ ≤ 6 := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2)
  let : Finite ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    Finite.of_equiv _ e.toEquiv
  rw [primeRank_equiv 2 e]
  apply primeRank_le_of_prime_pow_not_dvd
  rw [BinaryLinear.card_GL_of_finrank (by simp : Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4)]
  norm_num [BinaryLinear.order,Fin.prod_univ_succ]

/-- The full four-copy normalizer has two-rank at most nine. -/
theorem linearNormalizer_two_rank_le_nine : primeRank 2 (linearNormalizer action) ≤ 9 := by
  obtain ⟨f,hf⟩ := kernel_embeds_multiplicity
  have hk : primeRank 2 normalizerAutomorphism.ker ≤ 6 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans multiplicity_two_rank_le_six
  have hn := primeRank_le_ker_add (p := 2) normalizerAutomorphism
  have ha := NaturalDual.automorphism_two_rank_le_three
  omega

end BinaryLinearThree.FourNatural
