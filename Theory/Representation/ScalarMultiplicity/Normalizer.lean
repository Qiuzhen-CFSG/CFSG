module
public import Theory.Representation.ScalarMultiplicity.Semilinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A normalizing operator on a scalar multiplicity space

An operator on equal constituents and a compatible operator on one constituent
have scalar block ratios. These ratios give an invertible base-field linear
map on the multiplicity coordinates with the same field automorphism.
The pure-tensor equation transfers conjugation of every commuting action.

This single-actor construction does not require a choice of constituent
implementers to form a representation. It is used for the original H-actors
in Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.ScalarMultiplicity
variable {k F D E I : Type*} [Field k] [Field F] [Algebra k F]
  [Group D] [AddCommGroup E] [Module F E] [Module k E]
  [IsScalarTower k F E] [Nontrivial E]
  [Fintype I] [DecidableEq I] [FiniteDimensional k F]

/-- A compatible normalizer on equal constituents induces a semilinear
bijection on their multiplicity space, retaining its field coefficient. -/
theorem exists_semilinear_multiplicity_equiv
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (α : MulAut D) (u : (I → E) ≃ₗ[k] (I → E)) (s : E ≃ₗ[k] E)
    (hu : ∀ d x, u (fun i => σ d (x i)) = fun i => σ (α d) (u x i))
    (hsα : ∀ d v, s (σ d v) = σ (α d) (s v))
    (τ : F ≃+* F) (hsemi : ∀ c v, s (c • v) = τ c • s v) :
    ∃ f : (I → F) ≃ₗ[k] (I → F),
      (∀ c v, u (fun i => c i • v) = fun i => f c i • s v) ∧
      (∀ c v, f (c • v) = τ c • f v) := by
  have hsinv (d : D) (v : E) :
      s.symm (σ (α d) v) = σ d (s.symm v) := by
    apply s.injective
    rw [s.apply_symm_apply,hsα,s.apply_symm_apply]
  have hblock (i j : I) : ∃ b : F, ∀ v,
      u (Pi.single j v) i = b • s v := by
    let l : E →ₗ[k] E := s.symm.toLinearMap.comp
      ((LinearMap.proj i).comp (u.toLinearMap.comp (LinearMap.single k (fun _ : I => E) j)))
    obtain ⟨b,hb⟩ := hs l (by
      intro d v
      have hp : (fun t => σ d ((Pi.single j v : I → E) t)) = Pi.single j (σ d v) := by
        ext t
        by_cases h : j = t
        · subst t; simp
        · simp [Ne.symm h]
      have hh := congrFun (hu d (Pi.single j v)) i
      rw [hp] at hh
      change s.symm (u (Pi.single j (σ d v)) i) = σ d (s.symm (u (Pi.single j v) i))
      rw [hh,hsinv])
    refine ⟨τ b,fun v => ?_⟩
    have hh := congrArg s (hb v)
    change s (s.symm (u (Pi.single j v) i)) = s (b • v) at hh
    rwa [s.apply_symm_apply,hsemi] at hh
  choose b hb using hblock
  have hsum (x : I → E) (i : I) :
      u x i = ∑ j : I, b i j • s (x j) := by
    have hx : x = ∑ j : I, Pi.single j (x j) := by ext j; simp
    conv_lhs => rw [hx]
    rw [map_sum,Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hb i j (x j))
  obtain ⟨z,hz⟩ := exists_ne (0 : E)
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one F hz
  let j : (I → F) →ₗ[k] (I → E) := {
    toFun c i := c i • s.symm z
    map_add' c d := by ext i; exact add_smul _ _ _
    map_smul' c d := by ext i; exact smul_assoc _ _ _ }
  let r : (I → E) →ₗ[k] (I → F) := {
    toFun x i := l (x i)
    map_add' x y := by ext i; exact l.map_add _ _
    map_smul' c x := by ext i; exact l.map_smul_of_tower c (x i) }
  let m : Module.End k (I → F) := r.comp (u.toLinearMap.comp j)
  have hm (c : I → F) (i : I) : m c i = ∑ t : I, b i t * τ (c t) := by
    change l (u (j c) i) = _
    rw [hsum,map_sum]
    apply Finset.sum_congr rfl
    intro t _
    change l (b i t • s (c t • s.symm z)) = _
    rw [hsemi,s.apply_symm_apply,map_smul,map_smul,hl]
    simp only [smul_eq_mul,mul_one]
  have he (c : I → F) (v : E) :
      u (fun i => c i • v) = fun i => m c i • s v := by
    ext i
    rw [hsum,hm,Finset.sum_smul]
    exact Finset.sum_congr rfl (fun t _ => by rw [hsemi,smul_smul])
  have hmi : Function.Injective m := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro c hc
    have hc0 : m c = 0 := hc
    have hh := he c z
    rw [hc0] at hh
    have hx : (fun i => c i • z) = 0 := by
      apply u.injective
      rw [map_zero]
      ext i
      simpa only [Pi.zero_apply,zero_smul] using congrFun hh i
    ext i
    exact (smul_eq_zero.mp (congrFun hx i)).resolve_right hz
  let f := LinearEquiv.ofBijective m ⟨hmi,(LinearMap.injective_iff_surjective).mp hmi⟩
  refine ⟨f,he,?_⟩
  intro c v
  ext i
  change m (c • v) i = τ c * m v i
  rw [hm,hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Pi.smul_apply,smul_eq_mul,map_mul]
  ring

omit [IsScalarTower k F E] [Fintype I] [DecidableEq I] [FiniteDimensional k F] in
/-- The same pure-tensor equation transports normalization of any commuting
multiplicity action; the normalizing operator need only be base-field linear. -/
theorem multiplicity_equiv_intertwines
    {C : Type*} [Group C]
    (ρ : Representation k C (I → E)) (μ : Representation F C (I → F))
    (hμ : ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v)
    (α : C → C) (u : (I → E) ≃ₗ[k] (I → E)) (s : E ≃ₗ[k] E)
    (f : (I → F) ≃ₗ[k] (I → F))
    (hf : ∀ c v, u (fun i => c i • v) = fun i => f c i • s v)
    (hu : ∀ a x, u (ρ a x) = ρ (α a) (u x)) :
    ∀ a c, f (μ a c) = μ (α a) (f c) := by
  obtain ⟨z,hz⟩ := exists_ne (0 : E)
  intro a c
  ext i
  apply smul_left_injective F hz
  have hh := congrFun (hu a (fun i => c i • s.symm z)) i
  simpa only [hμ,hf,s.apply_symm_apply] using hh
end Representation.ScalarMultiplicity
