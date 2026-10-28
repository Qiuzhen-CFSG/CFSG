module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer
public import Mathlib.Algebra.Module.ZMod

/-!
# Six-letter permutations induced by natural alternating-six blocks

An automorphism of a marked A₆ block acts linearly on the literal module
U(L)/C_U(L) and normalizes the prescribed A₆ action. The linear normalizer
is the natural S₆, whose faithful action gives a unique permutation.
This construction is a homomorphism; on inner automorphisms it agrees
with the original quotient L/O₂(L), and it retains the exact module action.

This supplies the compatible six-letter action needed in the source
3.3.31 marking. It assumes neither a split block extension nor an
identification of U(L) with any separately chosen module.
Source: Aschbacher–Smith B.3 and 3.3.31, printed pp.81–85 and 602.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterC
namespace AlternatingSixBlockAction
abbrev Vector := BinaryPermutation.natural (Fin 6)
abbrev Actor := alternatingGroup (Fin 6)
open BinaryAlternatingSixNaturalNormalizer

private def linearize : MulAut (Multiplicative Vector) →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun a :=
    let e : Vector ≃+ Vector :=
      { toFun v := (a (Multiplicative.ofAdd v)).toAdd
        invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
        left_inv v := a.symm_apply_apply v
        right_inv v := a.apply_symm_apply v
        map_add' v w := a.map_mul v w }
    { e with map_smul' := fun c v => ZMod.map_smul e c v }
  map_one' := by ext v; rfl
  map_mul' a b := by ext v; rfl

private theorem natural_injective : Function.Injective naturalLinearAction := by
  intro g h he
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun he v

variable {L : Type*} [Group L]
  {ρ : Actor →* MulAut (Multiplicative Vector)} (m : BlockModuleModel L ρ)
  (hρ : ∀ g v, (ρ g v).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)

/-- Automorphisms of the actual block act linearly on its marked quotient module. -/
def linearAction : MulAut L →* (Vector ≃ₗ[ZMod 2] Vector) :=
  linearize.comp m.moduleAction

include hρ in
private theorem linear_compatible (a : MulAut L) (g : Actor) (v : Vector) :
    linearAction m a (naturalLinearAction g v) =
      naturalLinearAction (m.quotientAction a g) (linearAction m a v) := by
  have hh := congrArg Multiplicative.toAdd (m.actions_compatible a g (Multiplicative.ofAdd v))
  have he : Multiplicative.ofAdd (naturalLinearAction g v) = ρ g (Multiplicative.ofAdd v) :=
    Multiplicative.toAdd.injective (hρ g _).symm
  change (m.moduleAction a (Multiplicative.ofAdd (naturalLinearAction g v))).toAdd = _
  rw [he, hh, hρ]
  rfl

include hρ in
private theorem linear_mem_range (a : MulAut L) :
    linearAction m a ∈ naturalLinearAction.range := by
  rw [← BinaryAlternatingSixNaturalNormalizer.normalizer]
  let f := naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype
  have he : (MulAut.conj (linearAction m a)).toMonoidHom.comp f =
      f.comp (m.quotientAction a).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    apply LinearEquiv.ext
    intro v
    change linearAction m a (naturalLinearAction g ((linearAction m a).symm v)) =
      naturalLinearAction (m.quotientAction a g) v
    rw [linear_compatible m hρ, (linearAction m a).apply_symm_apply]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change f.range.map (MulAut.conj (linearAction m a)).toMonoidHom = f.range
  rw [← MonoidHom.range_comp, he, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (m.quotientAction a).surjective,
    ← MonoidHom.range_eq_map]

/-- The actual block automorphisms induce permutations of the six natural letters. -/
def permutationAction : MulAut L →* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective natural_injective).symm.toMonoidHom.comp
    ((linearAction m).codRestrict naturalLinearAction.range (linear_mem_range m hρ))

/-- This permutation has exactly the original action on U(L)/C_U(L). -/
theorem permutationAction_linear (a : MulAut L) :
    naturalLinearAction (permutationAction m hρ a) = linearAction m a :=
  MonoidHom.apply_ofInjective_symm natural_injective _

/-- Pointwise equivariance uses the original multiplicative quotient module. -/
theorem permutationAction_apply (a : MulAut L) (v : Multiplicative Vector) :
    BinaryPermutation.naturalRepresentation (Fin 6) (permutationAction m hρ a) v.toAdd =
      (m.moduleAction a v).toAdd :=
  LinearEquiv.congr_fun (permutationAction_linear m hρ a) v.toAdd

/-- On inner automorphisms the permutation is the prescribed core quotient. -/
theorem permutationAction_inner (l : L) :
    permutationAction m hρ (MulAut.conj l) =
      (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) : Equiv.Perm (Fin 6)) := by
  apply natural_injective
  rw [permutationAction_linear]
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu⟩ := m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective (blockFixed L))
    (Multiplicative.ofAdd v)
  dsimp only [Function.comp_apply] at hu
  have hh := m.moduleAction_mk (MulAut.conj l) u
  have hc : MulAut.characteristic (blockU L) (MulAut.conj l) u = blockConjugate L l u := by
    apply Subtype.ext
    rfl
  rw [hc, m.intertwining, hu] at hh
  exact (congrArg Multiplicative.toAdd hh).trans (hρ _ _)

/-- The permutation kernel is precisely fixation of the marked quotient module. -/
theorem permutationAction_eq_one_iff (a : MulAut L) :
    permutationAction m hρ a = 1 ↔ m.moduleAction a = 1 := by
  constructor
  · intro he
    have hh := permutationAction_linear m hρ a
    rw [he, map_one] at hh
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun hh.symm v.toAdd)
  · intro he
    apply natural_injective
    rw [permutationAction_linear, map_one]
    change linearize (m.moduleAction a) = 1
    rw [he, map_one]

end AlternatingSixBlockAction
end CFSG.Quasithin.ChapterC
