module
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point

/-!
# Recover the whole F₄-linear actor from the original central cubic

Inside the additive automorphisms of the actual quadratic field K, the
centralizer of the center of the original order-thirty Singer actor is
exactly the full F₄-linear group. Commuting with its nontrivial cubic scalar
forces F₄-linearity; the four field elements make this explicit. This is
the invariant needed to extend a marked point-group automorphism to its
whole affine plane normalizer.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
open Subgroup
open BaumeisterParabolics

/-- The actual full F₄-linear action on the same additive field carrier. -/
@[expose] def linearAction : (K ≃ₗ[F] K) →* MulAut (Multiplicative K) where
  toFun f := f.toAddEquiv.toMultiplicative
  map_one' := rfl
  map_mul' _ _ := rfl

theorem linearAction_injective : Function.Injective linearAction := by
  intro a b h
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : MulAut (Multiplicative K) => (f (Multiplicative.ofAdd x)).toAdd) h

private abbrev c₃ : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
private abbrev z : SingerField.normalizer := complementEquiv (c₃,1)
private abbrev b : F := (cubicUnits c₃ : K).re

private theorem b_cases (c : F) : c=0 ∨ c=1 ∨ c=b ∨ c=1+b := by
  revert c
  decide +kernel

private theorem z_action (x : K) :
    action z (Multiplicative.ofAdd x) = Multiplicative.ofAdd (b • x) := by
  change Multiplicative.ofAdd (complementHom (c₃,1) x) = _
  change Multiplicative.ofAdd ((multiplication (cubicUnits c₃) * dihedralHom 1) x) = _
  rw [map_one,mul_one]
  have hb : (cubicUnits c₃ : K) = algebraMap F K b := by decide +kernel
  change Multiplicative.ofAdd ((cubicUnits c₃ : K)*x) = _
  rw [hb,Algebra.smul_def]

private theorem center_actor : center SingerField.normalizer = zpowers z := by
  have hz : center Seventeen.Complement = zpowers ((c₃,1) : Seventeen.Complement) := by
    have h3 : orderOf ((c₃,1) : Seventeen.Complement) = 3 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    ext x
    rw [mem_center_iff,mem_zpowers_iff_mem_range_orderOf,h3]
    revert x
    decide +kernel
  have hm : (center Seventeen.Complement).map complementEquiv.toMonoidHom =
      center SingerField.normalizer := by
    ext x
    rw [mem_map_equiv]
    constructor
    · intro hx
      have hh := (centerCongr complementEquiv ⟨complementEquiv.symm x,hx⟩).property
      change complementEquiv (complementEquiv.symm x) ∈ center SingerField.normalizer at hh
      simpa only [MulEquiv.apply_symm_apply] using hh
    · intro hx
      exact (centerCongr complementEquiv.symm ⟨x,hx⟩).property
  rw [←hm,hz,MonoidHom.map_zpowers]
  rfl

/-- The full linear actor is recovered intrinsically from the center of
the same original order-thirty actor. -/
theorem range_eq_center_centralizer : linearAction.range =
    centralizer (((center SingerField.normalizer).map action :
      Subgroup (MulAut (Multiplicative K))) : Set (MulAut (Multiplicative K))) := by
  rw [center_actor,MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure]
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro x
    change linearAction f (action z x) = action z (Multiplicative.ofAdd (f x.toAdd))
    rw [show x = Multiplicative.ofAdd x.toAdd from rfl,z_action,z_action]
    exact congrArg Multiplicative.ofAdd (f.map_smul b x.toAdd)
  · intro f hf
    let a : K ≃+ K := AddEquiv.toMultiplicative.symm f
    have hb (x : K) : a (b • x) = b • a x := by
      have hh := congrArg (fun e : MulAut (Multiplicative K) =>
        (e (Multiplicative.ofAdd x)).toAdd) (mem_centralizer_singleton_iff.mp hf)
      change (f (action z (Multiplicative.ofAdd x))).toAdd =
        (action z (f (Multiplicative.ofAdd x))).toAdd at hh
      rw [z_action] at hh
      have ht := z_action (f (Multiplicative.ofAdd x)).toAdd
      change action z (f (Multiplicative.ofAdd x)) = _ at ht
      rw [ht] at hh
      exact hh
    let l : K ≃ₗ[F] K :=
      { a with
        map_smul' := by
          intro c x
          change a (c • x) = c • a x
          rcases b_cases c with rfl | rfl | rfl | rfl
          · simp only [zero_smul,map_zero]
          · simp only [one_smul]
          · exact hb x
          · simp only [add_smul,one_smul,map_add,hb] }
    exact ⟨l,rfl⟩
end Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
