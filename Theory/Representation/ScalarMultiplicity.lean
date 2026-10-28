module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Scalar multiplicity actions and separated centralizers

Every block of a commuting operator on a finite family of equal modules lies
in the scalar commutant. A nonzero vector and a dual coordinate construct
its actual representation over that scalar field, allowing arbitrary mixing
among copies. For a pair of independently acted-on supports, the zero common
fixed space kills the off-support blocks. A faithful commuting action thus
embeds into the product of the two multiplicity general linear groups.

The coordinate transport theorem applies this to the original module and
its literal product action. The source application is the homogeneous
separated A₅ branch of Aschbacher--Smith D.3.9, printed pp.199--201.
-/

public noncomputable section
namespace Representation.ScalarMultiplicity
variable {k F D C E I : Type*} [Field k] [Field F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E]
  [Fintype I] [DecidableEq I]

omit [Nontrivial E] [Fintype I] in
private theorem block_scalar
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (T : Module.End k (I → E))
    (hc : ∀ d x, T (fun i => σ d (x i)) = fun i => σ d (T x i))
    (i j : I) : ∃ c : F, ∀ v, T (Pi.single j v) i = c • v := by
  let f := (LinearMap.proj i).comp (T.comp (LinearMap.single k (fun _ : I => E) j))
  apply hs f
  intro d v
  have hp : (fun l => σ d ((Pi.single j v : I → E) l)) = Pi.single j (σ d v) := by
    funext l
    by_cases h : j = l
    · subst l; simp
    · simp [Ne.symm h]
  have h := congrFun (hc d (Pi.single j v)) i
  rw [hp] at h
  exact h

/-- Scalar commutants over an extension field give the literal multiplicity
representation for arbitrary mixing of finitely many equal copies. -/
theorem exists_multiplicity
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation k C (I → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i)) :
    ∃ μ : Representation F C (I → F),
      ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v := by
  obtain ⟨z,hz⟩ := exists_ne (0 : E)
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one F hz
  let j : (I → F) →ₗ[F] (I → E) := {
    toFun c i := c i • z
    map_add' c d := by ext i; exact add_smul _ _ _
    map_smul' c d := by ext i; exact mul_smul _ _ _ }
  let r : (I → E) →ₗ[F] (I → F) := {
    toFun x i := l (x i)
    map_add' x y := by ext i; exact l.map_add _ _
    map_smul' c x := by ext i; exact l.map_smul _ _ }
  have hrj (c : I → F) : r (j c) = c := by
    ext i
    change l (c i • z) = c i
    rw [map_smul,hl,smul_eq_mul,mul_one]
  have hexp (x : I → E) : x = ∑ b : I, Pi.single b (x b) := by
    ext b
    simp
  have hsum (a : C) (x : I → E) (i : I) :
      ρ a x i = ∑ b : I, ρ a (Pi.single b (x b)) i := by
    conv_lhs => rw [hexp x]
    rw [map_sum, Finset.sum_apply]
  have hlin (a : C) (c : F) (x : I → E) : ρ a (c • x) = c • ρ a x := by
    funext i
    change ρ a (c • x) i = c • ρ a x i
    rw [hsum, hsum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    obtain ⟨t,ht⟩ := block_scalar σ hs (ρ a) (hc a) i b
    rw [ht, ht]
    exact smul_comm t c (x b)
  have he (a : C) (c : I → F) (v : E) :
      ρ a (fun i => c i • v) = fun i => r (ρ a (j c)) i • v := by
    funext i
    rw [hsum]
    change _ = l (ρ a (j c) i) • v
    rw [hsum, map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro b _
    obtain ⟨t,ht⟩ := block_scalar σ hs (ρ a) (hc a) i b
    rw [ht,ht]
    change t • (c b • v) = l (t • (c b • z)) • v
    rw [map_smul,map_smul,hl,smul_eq_mul,smul_eq_mul,mul_one,smul_smul]
  let T (a : C) : Module.End F (I → E) := {
    toFun := ρ a
    map_add' := (ρ a).map_add
    map_smul' := hlin a }
  let μ : Representation F C (I → F) := {
    toFun a := r.comp ((T a).comp j)
    map_one' := by
      apply LinearMap.ext
      intro c
      change r (ρ 1 (j c)) = c
      rw [map_one, Module.End.one_apply, hrj]
    map_mul' a b := by
      apply LinearMap.ext
      intro c
      change r (ρ (a*b) (j c)) = r (ρ a (j (r (ρ b (j c)))))
      rw [map_mul, Module.End.mul_apply]
      have h := he b c z
      exact congrArg (fun w => r (ρ a w)) h }
  exact ⟨μ, he⟩
end Representation.ScalarMultiplicity

namespace Representation.ScalarMultiplicity
variable {k F D C E I : Type*} [Field k] [Field F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E]
  [Fintype I] [DecidableEq I]

omit [Module F E] [Nontrivial E] [Fintype I] [DecidableEq I] in
/-- A commuting actor on a separated pair preserves both supports intrinsically.
No choice of irreducible copies is required to be invariant. -/
theorem exists_support_actions
    (σ : Representation k D E)
    (hz : ∀ v : E, (∀ d, σ d v = v) → v = 0)
    (ρ : Representation k C ((I → E) × (I → E)))
    (hc : ∀ a g h x y, ρ a (fun i => σ g (x i), fun i => σ h (y i)) =
      (fun i => σ g ((ρ a (x,y)).1 i), fun i => σ h ((ρ a (x,y)).2 i))) :
    ∃ ρ₀ ρ₁ : Representation k C (I → E),
      (∀ a x y, ρ a (x,y) = (ρ₀ a x, ρ₁ a y)) ∧
      (∀ a d x, ρ₀ a (fun i => σ d (x i)) = fun i => σ d (ρ₀ a x i)) ∧
      (∀ a d x, ρ₁ a (fun i => σ d (x i)) = fun i => σ d (ρ₁ a x i)) := by
  have hl (a : C) (x : I → E) : (ρ a (x,0)).2 = 0 := by
    funext i
    apply hz
    intro d
    have hh := congrFun (congrArg Prod.snd (hc a 1 d x 0)) i
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh.symm
  have hr (a : C) (y : I → E) : (ρ a (0,y)).1 = 0 := by
    funext i
    apply hz
    intro d
    have hh := congrFun (congrArg Prod.fst (hc a d 1 0 y)) i
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh.symm
  let T₀ (a : C) : Module.End k (I → E) :=
    (LinearMap.fst k (I → E) (I → E)).comp
      ((ρ a).comp (LinearMap.inl k (I → E) (I → E)))
  let T₁ (a : C) : Module.End k (I → E) :=
    (LinearMap.snd k (I → E) (I → E)).comp
      ((ρ a).comp (LinearMap.inr k (I → E) (I → E)))
  have hd (a : C) (x y : I → E) : ρ a (x,y) = (T₀ a x, T₁ a y) := by
    have hadd : ρ a (x,y) = ρ a (x,0) + ρ a (0,y) := by
      simpa using (ρ a).map_add (x,0) (0,y)
    apply Prod.ext
    · change (ρ a (x,y)).1 = (ρ a (x,0)).1
      rw [hadd]
      change (ρ a (x,0)).1 + (ρ a (0,y)).1 = _
      rw [hr, add_zero]
    · change (ρ a (x,y)).2 = (ρ a (0,y)).2
      rw [hadd]
      change (ρ a (x,0)).2 + (ρ a (0,y)).2 = _
      rw [hl, zero_add]
  let ρ₀ : Representation k C (I → E) := {
    toFun := T₀
    map_one' := by
      apply LinearMap.ext
      intro x
      change (ρ 1 (x,0)).1 = x
      simp only [map_one, Module.End.one_apply]
    map_mul' a b := by
      apply LinearMap.ext
      intro x
      change (ρ (a*b) (x,0)).1 = (ρ a ((ρ b (x,0)).1,0)).1
      rw [map_mul, Module.End.mul_apply, hd b x 0]
      simp only [map_zero] }
  let ρ₁ : Representation k C (I → E) := {
    toFun := T₁
    map_one' := by
      apply LinearMap.ext
      intro x
      change (ρ 1 (0,x)).2 = x
      simp only [map_one, Module.End.one_apply]
    map_mul' a b := by
      apply LinearMap.ext
      intro x
      change (ρ (a*b) (0,x)).2 = (ρ a (0,(ρ b (0,x)).2)).2
      rw [map_mul, Module.End.mul_apply, hd b 0 x]
      simp only [map_zero] }
  refine ⟨ρ₀,ρ₁,hd,?_,?_⟩
  · intro a d x
    change (ρ a (fun i => σ d (x i),0)).1 = fun i => σ d ((ρ a (x,0)).1 i)
    have hh := congrArg Prod.fst (hc a d 1 x 0)
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh
  · intro a d x
    change (ρ a (0,fun i => σ d (x i))).2 = fun i => σ d ((ρ a (0,x)).2 i)
    have hh := congrArg Prod.snd (hc a 1 d 0 x)
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh

omit [Nontrivial E] in
private theorem eq_of_multiplicity_eq
    (ρ : Representation k C (I → E)) (μ : Representation F C (I → F))
    (he : ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v)
    (a b : C) (hab : μ a = μ b) : ρ a = ρ b := by
  apply LinearMap.ext
  intro x
  have hexp : x = ∑ i : I, Pi.single i (x i) := by ext i; simp
  rw [hexp, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hsing (v : E) : (fun j => (Pi.single i (1 : F) : I → F) j • v) =
      Pi.single i v := by
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  rw [← hsing (x i), he, he, hab]

/-- A faithful centralizer of two independently acting homogeneous supports
embeds in the product of their full multiplicity general linear groups. -/
theorem exists_injective_unit_pair
    (σ : Representation k D E)
    (hz : ∀ v : E, (∀ d, σ d v = v) → v = 0)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation k C ((I → E) × (I → E)))
    (hfaith : Function.Injective ρ)
    (hc : ∀ a g h x y, ρ a (fun i => σ g (x i), fun i => σ h (y i)) =
      (fun i => σ g ((ρ a (x,y)).1 i), fun i => σ h ((ρ a (x,y)).2 i))) :
    ∃ f : C →* (Module.End F (I → F))ˣ × (Module.End F (I → F))ˣ,
      Function.Injective f := by
  obtain ⟨ρ₀,ρ₁,hd,h₀,h₁⟩ := exists_support_actions σ hz ρ hc
  obtain ⟨μ₀,he₀⟩ := exists_multiplicity σ hs ρ₀ h₀
  obtain ⟨μ₁,he₁⟩ := exists_multiplicity σ hs ρ₁ h₁
  refine ⟨μ₀.asGroupHom.prod μ₁.asGroupHom, ?_⟩
  intro a b hab
  apply hfaith
  apply LinearMap.ext
  rintro ⟨x,y⟩
  rw [hd,hd]
  have h₀ab : μ₀ a = μ₀ b := congrArg Units.val (congrArg Prod.fst hab)
  have h₁ab : μ₁ a = μ₁ b := congrArg Units.val (congrArg Prod.snd hab)
  rw [eq_of_multiplicity_eq ρ₀ μ₀ he₀ a b h₀ab,
    eq_of_multiplicity_eq ρ₁ μ₁ he₁ a b h₁ab]
end Representation.ScalarMultiplicity

namespace Representation.ScalarMultiplicity
variable {k F D C E I W : Type*} [Field k] [Field F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module k W]

/-- The intrinsic centralizer embedding transported along actual separated
coordinates, retaining the literal product marking on the original module. -/
theorem exists_injective_unit_pair_of_coordinates
    (σ : Representation k D E)
    (hz : ∀ v : E, (∀ d, σ d v = v) → v = 0)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (α : Representation k (D × D) W) (ρ : Representation k C W)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a d v, ρ a (α d v) = α d (ρ a v))
    (e : W ≃ₗ[k] ((I → E) × (I → E)))
    (he : ∀ d v, e (α d v) =
      (fun i => σ d.1 ((e v).1 i), fun i => σ d.2 ((e v).2 i))) :
    ∃ f : C →* (Module.End F (I → F))ˣ × (Module.End F (I → F))ˣ,
      Function.Injective f := by
  let τ : Representation k C ((I → E) × (I → E)) :=
    (e.conjAlgEquiv k).toAlgHom.toMonoidHom.comp ρ
  have hτ (a : C) (x) : τ a x = e (ρ a (e.symm x)) := rfl
  have hτfaith : Function.Injective τ := by
    intro a b hab
    apply hfaith
    apply LinearMap.ext
    intro v
    apply e.injective
    have hh := LinearMap.congr_fun hab (e v)
    simpa only [hτ,e.symm_apply_apply] using hh
  apply exists_injective_unit_pair σ hz hs τ hτfaith
  intro a g h x y
  rw [hτ,hτ]
  have hi : e.symm (fun i => σ g (x i), fun i => σ h (y i)) =
      α (g,h) (e.symm (x,y)) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  rw [hi,hcomm,he]
end Representation.ScalarMultiplicity
