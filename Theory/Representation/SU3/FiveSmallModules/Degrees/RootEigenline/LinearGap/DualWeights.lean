module

public import Theory.Representation.AbelianAllWeights
public import Mathlib.RepresentationTheory.Invariants

/-!
# Scalar orbits on root characters

Distinct field multipliers give distinct pullbacks of any nontrivial additive
character: equality makes the character vanish on `(a-b)F = F`. A conjugating
linear equivalence carries an occurring weight to its inverse pullback.
Independence of character spaces therefore bounds the scalar orbit by the degree.

The root application factors the action on the center-fixed space through the
surjective first-coordinate homomorphism. Only normality of the root center
inside the root group is used; the ambient group need not normalize it.

Source: the root-group argument for Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section

open scoped IsMulCommutative
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap

variable {F E V : Type*} [Field F] [Field E] [AddCommGroup V] [Module E V]

/-- Pull back an additive character by multiplication in the field. -/
def scalarPullback (χ : Multiplicative F →* Eˣ) (a : F) :
    Multiplicative F →* Eˣ :=
  χ.comp { toFun := fun x => Multiplicative.ofAdd (a * x.toAdd)
           map_one' := by simp
           map_mul' := by intro x y; simp [mul_add] }

/-- The dual orbit is free: equality at two distinct scalars forces the character trivial. -/
theorem scalarPullback_injective (χ : Multiplicative F →* Eˣ) (hχ : χ ≠ 1) :
    Function.Injective (scalarPullback χ) := by
  intro a b hab
  by_contra hne
  apply hχ
  apply MonoidHom.ext
  intro x
  have he (y : F) : χ (Multiplicative.ofAdd (a * y)) =
      χ (Multiplicative.ofAdd (b * y)) := DFunLike.congr_fun hab (Multiplicative.ofAdd y)
  have hz (y : F) : χ (Multiplicative.ofAdd ((a - b) * y)) = 1 := by
    rw [sub_mul]
    change χ (Multiplicative.ofAdd (a * y) / Multiplicative.ofAdd (b * y)) = 1
    rw [map_div, he, div_self']
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  simpa only [mul_div_cancel₀ _ hd, ofAdd_toAdd, MonoidHom.one_apply] using hz (x.toAdd / (a - b))

/-- Conjugation carries a nonzero weight to its inverse scalar pullback. -/
theorem scalarPullback_occurs (σ : Representation E (Multiplicative F) V)
    (χ : σ.CharacterWeight) (a : F) (T : V ≃ₗ[E] V)
    (hT : ∀ x v, σ x (T v) = T (σ (Multiplicative.ofAdd (a * x.toAdd)) v)) :
    σ.characterWeightSpace (scalarPullback χ.val a) ≠ ⊥ := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.property
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨T v, ?_, fun h => hn (T.injective (h.trans T.map_zero.symm))⟩
  simp only [Representation.characterWeightSpace, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff] at hv ⊢
  intro x
  change σ x (T v) = (χ.val (Multiplicative.ofAdd (a * x.toAdd)) : E) • T v
  rw [hT, hv, map_smul]

/-- A family of distinct scalar conjugacies bounds every nontrivial weight's degree. -/
theorem card_le_finrank_of_nontrivial_weight [FiniteDimensional E V]
    (σ : Representation E (Multiplicative F) V)
    (horder : (Nat.card (Multiplicative F) : E) ≠ 0)
    {ι : Type*} (a : ι → F) (ha : Function.Injective a)
    (T : ι → V ≃ₗ[E] V)
    (hT : ∀ i x v, σ x (T i v) = T i (σ (Multiplicative.ofAdd (a i * x.toAdd)) v))
    (χ : σ.CharacterWeight) (hχ : χ.val ≠ 1) :
    Nat.card ι ≤ Module.finrank E V := by
  let w : ι → σ.CharacterWeight := fun i =>
    ⟨scalarPullback χ.val (a i), scalarPullback_occurs σ χ (a i) (T i) (hT i)⟩
  have hw : Function.Injective w := by
    intro i j hij
    exact ha (scalarPullback_injective χ.val hχ (congrArg Subtype.val hij))
  obtain ⟨hfinite, hcard⟩ := σ.characterWeight_card_le horder
  let := hfinite
  exact (Nat.card_le_card_of_injective w hw).trans hcard

/-- Below the scalar-orbit length, a split additive representation is trivial. -/
theorem invariants_eq_top_of_scalar_conjugacies [FiniteDimensional E V] [IsAlgClosed E]
    (σ : Representation E (Multiplicative F) V)
    (horder : (Nat.card (Multiplicative F) : E) ≠ 0)
    {ι : Type*} (a : ι → F) (ha : Function.Injective a)
    (T : ι → V ≃ₗ[E] V)
    (hT : ∀ i x v, σ x (T i v) = T i (σ (Multiplicative.ofAdd (a i * x.toAdd)) v))
    (hdim : Module.finrank E V < Nat.card ι) : σ.invariants = ⊤ := by
  have hχ (χ : σ.CharacterWeight) : χ.val = 1 := by
    by_contra hn
    exact (not_le_of_gt hdim) (card_le_finrank_of_nontrivial_weight σ horder a ha T hT χ hn)
  apply top_unique
  rw [← σ.iSup_characterWeightSpace_eq_top horder]
  refine iSup_le fun χ v hv => ?_
  simp only [Representation.characterWeightSpace, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff] at hv
  intro x
  simpa only [hχ χ, MonoidHom.one_apply, Units.val_one, one_smul] using hv x

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap

namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap

variable {F E U R G : Type*} [Field F] [Field E] [IsAlgClosed E]
  [AddCommGroup U] [Module E U] [FiniteDimensional E U] [Group R] [Group G]

/-- The scalar orbit argument on the center-fixed space, with the literal root
map and inverse conjugation retained. No ambient normality is needed. -/
theorem root_invariants_eq_center_of_scalar_conjugacies
    (τ : Representation E G U) (u : R →* G)
    (f : R →* Multiplicative F) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center R)
    (horder : (Nat.card (Multiplicative F) : E) ≠ 0)
    {ι : Type*} (a : ι → F) (ha : Function.Injective a)
    (t : ι → G) (c : ι → MulAut R)
    (hc : ∀ i x, u (c i x) = (t i)⁻¹ * u x * t i)
    (hfconj : ∀ i x, f (c i x) = Multiplicative.ofAdd (a i * (f x).toAdd))
    (hdim : Module.finrank E (invariants ((τ.comp u).comp (Subgroup.center R).subtype)) <
      Nat.card ι) :
    invariants (τ.comp u) = invariants ((τ.comp u).comp (Subgroup.center R).subtype) := by
  let ρ : Representation E R U := τ.comp u
  let W := invariants (ρ.comp (Subgroup.center R).subtype)
  let ρW := ρ.toInvariants (Subgroup.center R)
  have hkill : f.ker ≤ ρW.asGroupHom.ker := by
    intro x hx
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact w.property ⟨x, hker hx⟩
  let β := f.liftOfSurjective hf ⟨ρW.asGroupHom, hkill⟩
  let σ : Representation E (Multiplicative F) W := (Units.coeHom _).comp β
  have hσ (x : R) (w : W) : (σ (f x) w : U) = τ (u x) w := by
    have he : β (f x) = ρW.asGroupHom x :=
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
    change ((β (f x)).val w : U) = _
    rw [he]
    rfl
  have hstable (i : ι) (v : U) (hv : v ∈ W) : τ (t i) v ∈ W := by
    intro z
    have hz := hv (Subgroup.centerCongr (c i) z)
    change τ (u (c i z.val)) v = v at hz
    change τ (u z.val) (τ (t i) v) = τ (t i) v
    have he : u z.val * t i = t i * u (c i z.val) := by rw [hc]; group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hz]
  let L (i : ι) : W →ₗ[E] W := (τ (t i)).restrict (hstable i)
  have hL (i : ι) : Function.Injective (L i) := by
    intro v w he
    apply Subtype.ext
    exact (Representation.apply_bijective τ (t i)).injective (congrArg Subtype.val he)
  let T (i : ι) : W ≃ₗ[E] W :=
    LinearEquiv.ofBijective (L i) ⟨hL i, LinearMap.surjective_of_injective (hL i)⟩
  have hT (i : ι) (y : Multiplicative F) (w : W) :
      σ y (T i w) = T i (σ (Multiplicative.ofAdd (a i * y.toAdd)) w) := by
    obtain ⟨x, rfl⟩ := hf y
    apply Subtype.ext
    rw [← hfconj, hσ]
    change τ (u x) (τ (t i) w) = τ (t i) (σ (f (c i x)) w : U)
    rw [hσ, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    rw [hc]
    group
  have htop := invariants_eq_top_of_scalar_conjugacies σ horder a ha T hT hdim
  apply le_antisymm
  · intro v hv z
    exact hv z.val
  · intro v hv x
    have he := (show (⟨v, hv⟩ : W) ∈ σ.invariants by rw [htop]; trivial) (f x)
    exact (hσ x ⟨v, hv⟩).symm.trans (congrArg Subtype.val he)

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap
