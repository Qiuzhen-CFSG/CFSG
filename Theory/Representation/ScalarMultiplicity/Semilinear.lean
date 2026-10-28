module
public import Theory.Representation.ScalarMultiplicity

/-!
# Semilinear multiplicity from compatible normalizer actions

Compare the action on several equal constituents with a compatible action on
one constituent. Each block of their difference commutes with the component
and hence is scalar. Evaluation against a dual coordinate constructs the
coefficient representation, including its multiplication and field twist.
Its field action descends to the faithful coefficient image.

This is the multiplicity-centralizer construction used in Aschbacher--Smith
D.3.21, printed pp.206--207. The Chapter 10 seed-analysis consumer combines it
with the original odd-prime orbit-index bound and semilinear descent.
-/

public noncomputable section
namespace Representation.ScalarMultiplicity
variable {k F D C E I : Type*} [Field k] [Field F] [Algebra k F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [IsScalarTower k F E] [Nontrivial E]
  [Fintype I] [DecidableEq I]

/-- Compatible actions with scalar component commutant determine a genuine
semilinear representation on the multiplicity coordinates. -/
theorem exists_semilinear_multiplicity
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation k C (I → E)) (β : Representation k C E)
    (α : C → D → D)
    (hρ : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ (α a d) (ρ a x i))
    (hβ : ∀ a d v, β a (σ d v) = σ (α a d) (β a v))
    (τ : C →* (F ≃+* F))
    (hsemi : ∀ a c v, β a (c • v) = τ a c • β a v) :
    ∃ μ : Representation k C (I → F),
      (∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • β a v) ∧
      (∀ a c v, μ a (c • v) = τ a c • μ a v) := by
  have hbinv (a : C) (d : D) (v : E) :
      β a⁻¹ (σ (α a d) v) = σ d (β a⁻¹ v) := by
    have hh := congrArg (β a⁻¹) (hβ a d (β a⁻¹ v))
    rw [β.self_inv_apply, β.inv_self_apply] at hh
    exact hh.symm
  have hblock (a : C) (i j : I) : ∃ b : F, ∀ v,
      ρ a (Pi.single j v) i = b • β a v := by
    let f : E →ₗ[k] E := (β a⁻¹).comp
      ((LinearMap.proj i).comp ((ρ a).comp (LinearMap.single k (fun _ : I => E) j)))
    obtain ⟨b,hb⟩ := hs f (by
      intro d v
      have hp : (fun l => σ d ((Pi.single j v : I → E) l)) = Pi.single j (σ d v) := by
        ext l
        by_cases h : j = l
        · subst l; simp
        · simp [Ne.symm h]
      have hh := congrFun (hρ a d (Pi.single j v)) i
      rw [hp] at hh
      change β a⁻¹ (ρ a (Pi.single j (σ d v)) i) = σ d (β a⁻¹ (ρ a (Pi.single j v) i))
      rw [hh,hbinv])
    refine ⟨τ a b,fun v => ?_⟩
    have hh := congrArg (β a) (hb v)
    change β a (β a⁻¹ (ρ a (Pi.single j v) i)) = β a (b • v) at hh
    rwa [β.self_inv_apply,hsemi] at hh
  choose b hb using hblock
  have hsum (a : C) (x : I → E) (i : I) :
      ρ a x i = ∑ j : I, b a i j • β a (x j) := by
    have hx : x = ∑ j : I, Pi.single j (x j) := by ext j; simp
    conv_lhs => rw [hx]
    rw [map_sum,Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hb a i j (x j))
  obtain ⟨z,hz⟩ := exists_ne (0 : E)
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one F hz
  let j (a : C) : (I → F) →ₗ[k] (I → E) := {
    toFun c i := c i • β a⁻¹ z
    map_add' c d := by ext i; exact add_smul _ _ _
    map_smul' c d := by ext i; exact smul_assoc _ _ _ }
  let r : (I → E) →ₗ[k] (I → F) := {
    toFun x i := l (x i)
    map_add' x y := by ext i; exact l.map_add _ _
    map_smul' c x := by ext i; exact l.map_smul_of_tower c (x i) }
  let m (a : C) : Module.End k (I → F) := r.comp ((ρ a).comp (j a))
  have hm (a : C) (c : I → F) (i : I) :
      m a c i = ∑ t : I, b a i t * τ a (c t) := by
    change l (ρ a (j a c) i) = _
    rw [hsum,map_sum]
    apply Finset.sum_congr rfl
    intro t _
    change l (b a i t • β a (c t • β a⁻¹ z)) = _
    rw [hsemi,β.self_inv_apply,map_smul,map_smul,hl]
    simp only [smul_eq_mul,mul_one]
  have he (a : C) (c : I → F) (v : E) :
      ρ a (fun i => c i • v) = fun i => m a c i • β a v := by
    ext i
    rw [hsum,hm,Finset.sum_smul]
    exact Finset.sum_congr rfl (fun t _ => by rw [hsemi,smul_smul])
  have hmsemi (a : C) (c : F) (v : I → F) : m a (c • v) = τ a c • m a v := by
    ext i
    rw [hm]
    change _ = τ a c * m a v i
    rw [hm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.smul_apply,smul_eq_mul,map_mul]
    ring
  have hβz (a : C) : β a z ≠ 0 := by
    intro hh
    have h := congrArg (β a⁻¹) hh
    rw [β.inv_self_apply,map_zero] at h
    exact hz h
  let μ : Representation k C (I → F) := {
    toFun := m
    map_one' := by
      apply LinearMap.ext
      intro c
      ext i
      apply smul_left_injective F hz
      have hh := congrFun (he 1 c z) i
      simpa only [map_one,Module.End.one_apply] using hh.symm
    map_mul' a b := by
      apply LinearMap.ext
      intro c
      ext i
      apply smul_left_injective F (hβz (a*b))
      have hh := he (a*b) c z
      rw [map_mul,Module.End.mul_apply,he,he] at hh
      have hv := congrFun hh i
      simpa only [map_mul,Module.End.mul_apply] using hv.symm }
  exact ⟨μ,he,hmsemi⟩
end Representation.ScalarMultiplicity

namespace Representation.ScalarMultiplicity
variable {k F C V : Type*} [Field k] [Field F] [Group C]
  [AddCommGroup V] [Module k V] [Module F V] [Nontrivial V]

/-- An actor trivial on a nonzero semilinear space has trivial field twist. -/
theorem semilinear_ker_le_field_ker
    (μ : Representation k C V) (τ : C →* (F ≃+* F))
    (hsemi : ∀ a c v, μ a (c • v) = τ a c • μ a v) :
    μ.asGroupHom.ker ≤ τ.ker := by
  intro a ha
  have hm : μ a = 1 := congrArg Units.val (MonoidHom.mem_ker.mp ha)
  apply MonoidHom.mem_ker.mpr
  apply RingEquiv.ext
  intro c
  change τ a c = c
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  apply smul_left_injective F hv
  simpa only [hm,Module.End.one_apply] using (hsemi a c v).symm

/-- The field action descends to the literal faithful linear action image. -/
theorem exists_fieldAction_on_image
    (μ : Representation k C V) (τ : C →* (F ≃+* F))
    (hsemi : ∀ a c v, μ a (c • v) = τ a c • μ a v) :
    ∃ τ' : μ.asGroupHom.range →* (F ≃+* F),
      (∀ a, τ' (μ.asGroupHom.rangeRestrict a) = τ a) ∧
      (∀ (a : μ.asGroupHom.range) c v,
        a.val.val (c • v) = τ' a c • a.val.val v) := by
  let q := μ.asGroupHom.rangeRestrict
  have hk : q.ker ≤ τ.ker := by
    intro a ha
    apply semilinear_ker_le_field_ker μ τ hsemi
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))
  let τ' := q.liftOfSurjective μ.asGroupHom.rangeRestrict_surjective ⟨τ,hk⟩
  have ht (a : C) : τ' (q a) = τ a := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨τ',ht,?_⟩
  intro a c v
  obtain ⟨a,rfl⟩ := μ.asGroupHom.rangeRestrict_surjective a
  rw [ht]
  exact hsemi a c v
end Representation.ScalarMultiplicity
