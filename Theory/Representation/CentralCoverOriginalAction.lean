module

public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Original actors on central covering modules

A central G-cover of an L-generated module is already an L-cover when L is
normal in G. The universal L-cover then carries a unique lift of the original
G-action. This does not assert that its own central L-kernel is G-fixed.

The proofs use commutator generation, the actual quotient maps and the
cohomological universal-cover comparison. Source: Aschbacher--Smith,
Remark I.1.5 and Lemma I.2.3, printed pp.408 and 413.
-/

@[expose] public section
noncomputable section

namespace Representation.OneCohomology.CentralCoverOriginalAction

open Module

variable {k G L N U W : Type*} [Field k] [Group G] [Group L]
  [AddCommGroup N] [Module k N] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

/-- A map into a trivial module vanishes on every commutator. -/
theorem invariant_map_eq_zero (σ : Representation k L U)
    (hσ : Coinvariants.ker σ = ⊤) (d : U →ₗ[k] W)
    (hd : ∀ l u, d (σ l u) = d u) : d = 0 := by
  have hC : Coinvariants.ker σ ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, u⟩, rfl⟩
    change d (σ l u - u) = 0
    rw [map_sub, hd, sub_self]
  apply LinearMap.ext
  intro u
  exact hC (hσ ▸ Submodule.mem_top)

/-- Equivariant maps over the same central quotient agree on a generated source. -/
theorem lift_unique (σ : Representation k L U) (τ : Representation k L W)
    (hσ : Coinvariants.ker σ = ⊤) (p : W →ₗ[k] N)
    (hp : p.ker ≤ fixed τ) (f g : U →ₗ[k] W)
    (hf : ∀ l u, f (σ l u) = τ l (f u))
    (hg : ∀ l u, g (σ l u) = τ l (g u))
    (hover : ∀ u, p (f u) = p (g u)) : f = g := by
  apply sub_eq_zero.mp
  apply invariant_map_eq_zero σ hσ (f - g)
  intro l u
  have hk : f u - g u ∈ p.ker := by
    change p (f u - g u) = 0
    rw [map_sub, hover, sub_self]
  have he := hp hk l
  change f (σ l u) - g (σ l u) = f u - g u
  rw [hf, hg, ← map_sub]
  exact he

/-- Restriction of the original central G-cover to a normal L remains generated.
No hypothesis on G/L is needed. -/
theorem restrict_full (H : Subgroup G) [H.Normal]
    {ρ : Representation k G N} {τ : Representation k G W}
    (p : τ.IntertwiningMap ρ) (hp : IsCover p)
    (hN : Coinvariants.ker (ρ.comp H.subtype) = ⊤) :
    Coinvariants.ker (τ.comp H.subtype) = ⊤ := by
  let C := Coinvariants.ker (τ.comp H.subtype)
  let pH : Representation.IntertwiningMap (τ.comp H.subtype) (ρ.comp H.subtype) :=
    p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro h v
      exact LinearMap.congr_fun (p.isIntertwining' h) v)
  have hmap : C.map p.toLinearMap = ⊤ := by
    exact (map_coinvariants_of_surjective pH hp.1).trans hN
  have hC : Coinvariants.ker τ ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    have hw : p w ∈ C.map p.toLinearMap := hmap ▸ Submodule.mem_top
    obtain ⟨c, hc, hcw⟩ := hw
    change p c = p w at hcw
    have hk : w - c ∈ p.toLinearMap.ker := by
      change p (w - c) = 0
      rw [map_sub, hcw, sub_self]
    have hfix := hp.2.1 hk g
    have he : τ g w - w = τ g c - c := by
      rw [map_sub] at hfix
      apply sub_eq_sub_iff_add_eq_add.mpr
      exact (sub_eq_sub_iff_add_eq_add.mp hfix).trans (add_comm _ _)
    change τ g w - w ∈ C
    rw [he]
    exact C.sub_mem (Coinvariants.le_comap_ker τ H g hc) hc
  exact top_unique (hp.2.2 ▸ hC)

/-- The actual original projection, restricted to the normal subgroup. -/
def restrictProjection (H : Subgroup G)
    {ρ : Representation k G N} {τ : Representation k G W}
    (p : τ.IntertwiningMap ρ) :
    Representation.IntertwiningMap (τ.comp H.subtype) (ρ.comp H.subtype) :=
  p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro h v
    exact LinearMap.congr_fun (p.isIntertwining' h) v)

theorem restrict_isCover (H : Subgroup G) [H.Normal]
    {ρ : Representation k G N} {τ : Representation k G W}
    (p : τ.IntertwiningMap ρ) (hp : IsCover p)
    (hN : Coinvariants.ker (ρ.comp H.subtype) = ⊤) :
    IsCover (restrictProjection H p) :=
  ⟨hp.1, fun _ hw h => hp.2.1 hw h, restrict_full H p hp hN⟩

theorem fixed_comp_equiv {J : Type*} [Group J]
    (σ : Representation k L U) (a : J ≃* L) :
    fixed (σ.comp a.toMonoidHom) = fixed σ := by
  ext u
  constructor
  · intro hu l
    simpa using hu (a.symm l)
  · intro hu l
    exact hu (a l)

theorem commutator_comp_equiv {J : Type*} [Group J]
    (σ : Representation k L U) (a : J ≃* L) :
    Coinvariants.ker (σ.comp a.toMonoidHom) = Coinvariants.ker σ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, u⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (a l) u
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, u⟩, rfl⟩
    simpa using Coinvariants.sub_mem_ker (ρ := σ.comp a.toMonoidHom) (a.symm l) u

private theorem fixed_twist (σ : Representation k L U) (a : MulAut L) :
    fixed (σ.comp a.toMonoidHom) = fixed σ := fixed_comp_equiv σ a

private theorem commutator_twist (σ : Representation k L U) (a : MulAut L) :
    Coinvariants.ker (σ.comp a.toMonoidHom) = Coinvariants.ker σ :=
  commutator_comp_equiv σ a

/-- Every automorphism of the marked base action has a unique lift to the
universal L-cover, with the literal base projection retained. -/
theorem exists_lift [Finite L] [FiniteDimensional k N] [FiniteDimensional k U]
    {ρ : Representation k L N} {σ : Representation k L U}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hd : finrank k p.toLinearMap.ker = finrank k (H1 ρ.dual))
    (a : MulAut L) (e : N ≃ₗ[k] N)
    (he : ∀ l v, e (ρ l v) = ρ (a l) (e v)) :
    ∃ f : U ≃ₗ[k] U,
      (∀ l u, f (σ l u) = σ (a l) (f u)) ∧
      (∀ u, p (f u) = e (p u)) := by
  have hei (l : L) (v : N) : e.symm (ρ (a l) v) = ρ l (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let q : Representation.IntertwiningMap (σ.comp a.toMonoidHom) ρ :=
    (e.symm.toLinearMap.comp p.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro l u
      change e.symm (p (σ (a l) u)) = ρ l (e.symm (p u))
      rw [p.isIntertwining, hei])
  have hq : IsCover q := by
    refine ⟨e.symm.surjective.comp hp.1, ?_, ?_⟩
    · intro u hu
      rw [fixed_twist]
      apply hp.2.1
      change e.symm (p u) = 0 at hu
      exact e.symm.injective (hu.trans (map_zero _).symm)
    · rw [commutator_twist]
      exact hp.2.2
  obtain ⟨f, hf, hover⟩ := exists_quotient_of_finrank_ker_eq p hp hd q hq
  let E : U ≃ₗ[k] U := LinearEquiv.ofBijective f.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hf, hf⟩
  refine ⟨E, fun l u => LinearMap.congr_fun (f.isIntertwining' l) u, fun u => ?_⟩
  have h := congrArg e (hover u)
  exact (e.apply_symm_apply (p (f u))).symm.trans h

/-- A representation element as an actual linear equivalence. -/
def actorEquiv (η : Representation k G N) (g : G) : N ≃ₗ[k] N where
  toLinearMap := η g
  invFun := η g⁻¹
  left_inv v := by simp [← Module.End.mul_apply, ← map_mul]
  right_inv v := by simp [← Module.End.mul_apply, ← map_mul]

/-- Construct the original G-action on a universal L-cover from its marked
action on the quotient and actual conjugation on L. -/
theorem exists_action [Finite L] [FiniteDimensional k N] [FiniteDimensional k U]
    {ρ : Representation k L N} {σ : Representation k L U}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hd : finrank k p.toLinearMap.ker = finrank k (H1 ρ.dual))
    (a : G →* MulAut L) (η : Representation k G N)
    (ha : ∀ g l v, η g (ρ l v) = ρ (a g l) (η g v)) :
    ∃ ζ : Representation k G U,
      (∀ g l u, ζ g (σ l u) = σ (a g l) (ζ g u)) ∧
      (∀ g u, p (ζ g u) = η g (p u)) ∧
      (∀ (g : G) (l : L),
        (∀ x, a g x = l * x * l⁻¹) →
        (∀ v, η g v = ρ l v) → ∀ u, ζ g u = σ l u) := by
  choose f hf hpq using fun g => exists_lift p hp hd (a g) (actorEquiv η g) (ha g)
  have hone : (f 1).toLinearMap = LinearMap.id := by
    apply lift_unique σ σ hp.2.2 p.toLinearMap hp.2.1
    · intro l u
      simpa using hf 1 l u
    · intro l u
      rfl
    · intro u
      simpa [actorEquiv] using hpq 1 u
  have hmul (g h : G) : (f (g * h)).toLinearMap =
      (f g).toLinearMap.comp (f h).toLinearMap := by
    apply lift_unique σ (σ.comp (a (g * h)).toMonoidHom) hp.2.2 p.toLinearMap
      (by rw [fixed_twist]; exact hp.2.1)
    · exact hf (g * h)
    · intro l u
      change f g (f h (σ l u)) = σ (a (g * h) l) (f g (f h u))
      rw [hf, hf, map_mul]
      rfl
    · intro u
      change p (f (g * h) u) = p (f g (f h u))
      rw [hpq, hpq, hpq]
      exact LinearMap.congr_fun (η.map_mul g h) (p u)
  let ζ : Representation k G U :=
    { toFun g := (f g).toLinearMap
      map_one' := hone
      map_mul' := hmul }
  refine ⟨ζ, hf, hpq, fun g l ha' hη u => ?_⟩
  have he : (f g).toLinearMap = σ l := by
    apply lift_unique σ (σ.comp (a g).toMonoidHom) hp.2.2 p.toLinearMap
      (by rw [fixed_twist]; exact hp.2.1)
    · exact hf g
    · intro x v
      change σ l (σ x v) = σ (a g x) (σ l v)
      rw [ha']
      simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
    · intro v
      change p (f g v) = p (σ l v)
      rw [hpq, p.isIntertwining]
      exact hη (p v)
  exact LinearMap.congr_fun he u

/-- Conjugation by the original ambient group on its normal subgroup. -/
def normalConjugation (H : Subgroup G) [H.Normal] : G →* MulAut H :=
  H.normalizerMonoidHom.comp
    ((MonoidHom.id G).codRestrict (Subgroup.normalizer (H : Set G)) (fun g => by
      rw [Subgroup.normalizer_eq_top]
      trivial))

@[simp] theorem normalConjugation_val (H : Subgroup G) [H.Normal] (g : G) (h : H) :
    ((normalConjugation H g h : H) : G) = g * h * g⁻¹ := rfl

/-- The universal L-cover acquires the original G-action and restricts to its
original L-action, even when its L-fixed kernel moves under G. -/
theorem exists_original_action [Finite G] [FiniteDimensional k N] [FiniteDimensional k U]
    (H : Subgroup G) [H.Normal] (η : Representation k G N)
    {σ : Representation k H U} (p : σ.IntertwiningMap (η.comp H.subtype))
    (hp : IsCover p)
    (hd : finrank k p.toLinearMap.ker = finrank k (H1 (Representation.dual (η.comp H.subtype)))) :
    ∃ ζ : Representation k G U,
      (∀ h : H, ∀ u, ζ h u = σ h u) ∧
      (∀ g u, p (ζ g u) = η g (p u)) := by
  obtain ⟨ζ, _, hpq, hrestrict⟩ := exists_action p hp hd (normalConjugation H) η (by
    intro g h v
    change η g (η h v) = η (g * h * g⁻¹) (η g v)
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc])
  refine ⟨ζ, fun h => hrestrict h h (fun x => ?_) (fun _ => rfl), hpq⟩
  apply Subtype.ext
  rfl

/-- Every quotient from the universal L-cover to the original G-cover is
automatically equivariant for the lifted original actor. -/
theorem quotient_original_equivariant
    (H : Subgroup G) [H.Normal]
    {η : Representation k G N} {ζ : Representation k G U} {τ : Representation k G W}
    (p : U →ₗ[k] N) (q : W →ₗ[k] N) (f : U →ₗ[k] W)
    (hp : ∀ g u, p (ζ g u) = η g (p u))
    (hq : ∀ g w, q (τ g w) = η g (q w))
    (hkernel : q.ker ≤ fixed (τ.comp H.subtype))
    (hfull : Coinvariants.ker (ζ.comp H.subtype) = ⊤)
    (hf : ∀ h : H, ∀ u, f (ζ h u) = τ h (f u))
    (hover : ∀ u, q (f u) = p u) :
    ∀ g u, f (ζ g u) = τ g (f u) := by
  intro g
  have he : f.comp (ζ g) = (τ g).comp f := by
    apply lift_unique (ζ.comp H.subtype)
      ((τ.comp H.subtype).comp (normalConjugation H g).toMonoidHom) hfull q
      (fun w hw h => hkernel hw (normalConjugation H g h))
    · intro h u
      have hx : ζ g (ζ h u) = ζ ((normalConjugation H g h : H) : G) (ζ g u) := by
        simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
      change f (ζ g (ζ h u)) = τ _ (f (ζ g u))
      rw [hx, hf]
      rfl
    · intro h u
      change τ g (f (ζ h u)) = τ _ (τ g (f u))
      rw [hf]
      simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
    · intro u
      change q (f (ζ g u)) = q (τ g (f u))
      rw [hover, hp, hq, hover]
  exact fun u => LinearMap.congr_fun he u

end Representation.OneCohomology.CentralCoverOriginalAction
