module

public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Fixed points and centrality descending through the original cover

A stable section on which the covering projection is injective transfers
pointwise fixation from the natural quotient to its full inverse image,
because the actual covering kernel is fixed. A nonzero section stabilized by
a two-group contains a nonzero fixed vector. These are the two distinct uses
of the invariant singular complement in I.2.3(2), printed p.413.
-/

@[expose] public section
noncomputable section

namespace Representation.OneCohomology.CentralCoverOriginalAction

variable {k G N U W : Type*} [Field k] [Group G]
  [AddCommGroup N] [Module k N] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

/-- A stabilized injective section and fixed covering kernel transfer
centrality of the original quotient action to the full preimage. -/
theorem fixed_preimage_of_stable_section
    (η : Representation k G N) (ζ : Representation k G U) (τ : Representation k G W)
    (p : U →ₗ[k] N) (q : W →ₗ[k] N) (f : U →ₗ[k] W)
    (hp : ∀ g u, p (ζ g u) = η g (p u))
    (hf : ∀ g u, f (ζ g u) = τ g (f u))
    (hover : ∀ u, q (f u) = p u) (hk : q.ker ≤ fixed τ)
    (D : Submodule k U) (A : Submodule k N)
    (hD : ∀ u ∈ D, p u ∈ A)
    (hinj : ∀ u ∈ D, p u = 0 → u = 0)
    (hsurj : ∀ v ∈ A, ∃ u ∈ D, p u = v)
    (g : G) (hstable : ∀ u ∈ D, ζ g u ∈ D)
    (hfix : ∀ v ∈ A, η g v = v) :
    ∀ w, q w ∈ A → τ g w = w := by
  intro w hw
  obtain ⟨u, hu, hpu⟩ := hsurj (q w) hw
  have hzu : ζ g u = u := by
    apply sub_eq_zero.mp
    apply hinj _ (D.sub_mem (hstable u hu) hu)
    rw [map_sub, hp, hfix (p u) (hD u hu), sub_self]
  have hku : w - f u ∈ q.ker := by
    change q (w - f u) = 0
    rw [map_sub, hover, hpu, sub_self]
  have he := hk hku g
  rw [map_sub, ← hf, hzu] at he
  simpa only [sub_add_cancel] using congrArg (fun v => v + f u) he

/-- A nonzero injective section supplies a Sylow-fixed vector outside the
covering kernel, retaining the original covering projection. -/
theorem exists_fixed_above [Finite G]
    {N U W : Type*}
    [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ζ : Representation (ZMod 2) G U) (τ : Representation (ZMod 2) G W)
    (p : U →ₗ[ZMod 2] N) (q : W →ₗ[ZMod 2] N) (f : U →ₗ[ZMod 2] W)
    (hf : ∀ g u, f (ζ g u) = τ g (f u))
    (hover : ∀ u, q (f u) = p u)
    (D : Submodule (ZMod 2) U) (A : Submodule (ZMod 2) N)
    (hD : ∀ u ∈ D, p u ∈ A) (hne : D ≠ ⊥)
    (hinj : ∀ u ∈ D, p u = 0 → u = 0)
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hstable : ∀ t : T, ∀ u ∈ D, ζ t u ∈ D) :
    ∃ w : W, q w ∈ A ∧ q w ≠ 0 ∧ ∀ t : T, τ t w = w := by
  let D' : Subrepresentation (ζ.comp T.subtype) :=
    { toSubmodule := D
      apply_mem_toSubmodule := fun t u hu => hstable t u hu }
  let : Nontrivial D' := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨u, hu, hfixed⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by simpa only [ringChar.eq (ZMod 2) 2] using hT) D'.toRepresentation
  refine ⟨f u, ?_, ?_, fun t => ?_⟩
  · rw [hover]
    exact hD u u.property
  · rw [hover]
    intro hz
    exact hu (Subtype.ext (hinj u u.property hz))
  · rw [← hf]
    exact congrArg f (congrArg Subtype.val (hfixed t))

/-- If the natural module is faithful on L, an actor trivial on that quotient
also fixes any commutator-generated central L-cover. This handles the SL₂
second preimage, which is the whole natural plane and is not isotropic. -/
theorem fixed_cover_of_fixed_quotient
    (H : Subgroup G) [H.Normal]
    (η : Representation k G N) (τ : Representation k G W)
    (q : τ.IntertwiningMap η) (hq : IsCover q)
    (hfull : Coinvariants.ker (τ.comp H.subtype) = ⊤)
    (hfaith : Function.Injective (η.comp H.subtype))
    (g : G) (hg : ∀ v, η g v = v) : ∀ w, τ g w = w := by
  have hcomm (h : H) : g * (h : G) * g⁻¹ = h := by
    have he : normalConjugation H g h = h := by
      apply hfaith
      apply LinearMap.ext
      intro v
      change η (g * (h : G) * g⁻¹) v = η h v
      have hi : η g⁻¹ v = v := by
        have hh := hg (η g⁻¹ v)
        simpa [← Module.End.mul_apply, ← map_mul] using hh.symm
      simp only [map_mul, Module.End.mul_apply, hi, hg]
    exact congrArg Subtype.val he
  have he : τ g = LinearMap.id := by
    apply lift_unique (τ.comp H.subtype) (τ.comp H.subtype) hfull
      q.toLinearMap (fun w hw h => hq.2.1 hw h)
    · intro h w
      have hh : g * (h : G) = h * g := mul_inv_eq_iff_eq_mul.mp (hcomm h)
      change τ g (τ h w) = τ h (τ g w)
      simp only [← Module.End.mul_apply, ← map_mul, hh]
    · intro h w
      rfl
    · intro w
      change q (τ g w) = q w
      rw [q.isIntertwining, hg]
  exact fun w => LinearMap.congr_fun he w

end Representation.OneCohomology.CentralCoverOriginalAction
