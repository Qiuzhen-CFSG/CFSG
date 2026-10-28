module

public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.DualCommutator
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Covering modules and contragredient duality

A cover is an equivariant surjection with fixed kernel whose source is generated
by commutators. Annihilator duality exchanges these conditions with an injective
map having trivial quotient and fixed-point-free target. Dualizing the universal
dual cover constructed from crossed homomorphisms therefore produces
`U(G,V*)* → V` whenever `V = [V,G]`.

Every finite-dimensional cover is an equivariant quotient of this construction,
and the quotient map commutes with the projections to `V`. Its central kernel
has dimension `dim H¹(G,V*)`, since it is the annihilator of the principal
cocycles. The finite-group hypothesis ensures that the cocycle space is finite
dimensional; the duality statements themselves hold more generally.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Remark I.1.5, printed p.408 (PDF p.419).
The argument works over any field, in particular over F₂, without faithfulness.
-/

@[expose] public section

open Module
namespace Representation.OneCohomology
variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The elementary fixed-space definition agrees with Mathlib invariants. -/
lemma fixed_eq_invariants (ρ : Representation k G V) : fixed ρ = ρ.invariants := rfl

/-- The dual is fixed-point-free exactly when the original is commutator-generated. -/
lemma fixed_dual_eq_bot_iff (ρ : Representation k G V) :
    fixed ρ.dual = ⊥ ↔ Coinvariants.ker ρ = ⊤ := by
  rw [fixed_eq_invariants, ρ.invariants_dual_eq_commutator_annihilator,
    Submodule.dualAnnihilator_eq_bot_iff]

/-- The dual of a finite-dimensional fixed-point-free module is commutator-generated. -/
lemma commutator_dual_eq_top (ρ : Representation k G V) [FiniteDimensional k V]
    (h : fixed ρ = ⊥) : Coinvariants.ker ρ.dual = ⊤ := by
  have he := ρ.invariants_eq_dual_commutator_coannihilator
  rw [← fixed_eq_invariants, h] at he
  have hd := congrArg Submodule.dualAnnihilator he
  rw [Submodule.dualAnnihilator_bot, Subspace.dualCoannihilator_dualAnnihilator_eq] at hd
  exact hd.symm

variable {ρ : Representation k G V} {σ : Representation k G W}

/-- A cover is a surjection from a commutator-generated module with fixed kernel. -/
def IsCover (p : σ.IntertwiningMap ρ) : Prop :=
  Function.Surjective p ∧ p.toLinearMap.ker ≤ fixed σ ∧ Coinvariants.ker σ = ⊤

/-- The contragredient of an equivariant map. -/
def dualIntertwining (p : σ.IntertwiningMap ρ) : ρ.dual.IntertwiningMap σ.dual :=
  p.toLinearMap.dualMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g f
    ext w
    change f (ρ g⁻¹ (p w)) = f (p (σ g⁻¹ w))
    rw [p.isIntertwining])

/-- Dualizing a cover gives a dual covering of the dual module. -/
lemma cover_dual_isDualCover (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    IsDualCover (dualIntertwining p).range := by
  refine ⟨?_, (fixed_dual_eq_bot_iff σ).mpr hp.2.2⟩
  intro g f
  change σ.dual g f - f ∈ p.toLinearMap.dualMap.range
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  intro w hw
  change f (σ g⁻¹ w) - f w = 0
  rw [(hp.2.1 hw) g⁻¹, sub_self]

/-- A surjection is a cover exactly when its dual inclusion has dual-cover range. -/
lemma isCover_iff_dual_isDualCover (p : σ.IntertwiningMap ρ) :
    IsCover p ↔ Function.Surjective p ∧ IsDualCover (dualIntertwining p).range := by
  constructor
  · intro h
    exact ⟨h.1, cover_dual_isDualCover p h⟩
  · rintro ⟨hs, ht, hf⟩
    refine ⟨hs, ?_, (fixed_dual_eq_bot_iff σ).mp hf⟩
    intro w hw g
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro f
    obtain ⟨l, hl⟩ := ht g⁻¹ f
    have he := LinearMap.congr_fun hl w
    change l (p w) = f (σ ((g⁻¹)⁻¹) w) - f w at he
    change p w = 0 at hw
    rw [hw, map_zero, inv_inv] at he
    simpa only [map_sub] using he.symm

/-- Dualizing an injective dual covering in finite dimension gives a cover. -/
lemma dualCover_dual_isCover [FiniteDimensional k W]
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (h : IsDualCover i.range) : IsCover (dualIntertwining i) := by
  refine ⟨LinearMap.dualMap_surjective_of_injective hi, ?_,
    commutator_dual_eq_top σ h.2⟩
  intro f hf g
  ext w
  change f (σ g⁻¹ w) = f w
  have hz : f (σ g⁻¹ w - w) = 0 := by
    obtain ⟨v, hv⟩ := h.1 g⁻¹ w
    rw [← hv]
    exact LinearMap.congr_fun hf v
  exact sub_eq_zero.mp (by simpa using hz)

/-- The principal cocycle map intertwines the original and universal actions. -/
def principalIntertwining (ρ : Representation k G V) :
    ρ.IntertwiningMap (universalAction ρ) :=
  (principal ρ).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    exact (universalAction_principal ρ g v).symm)

/-- The principal inclusion realizes the universal dual cover. -/
lemma principalIntertwining_isDualCover (ρ : Representation k G V)
    (h : fixed ρ = ⊥) : IsDualCover (principalIntertwining ρ).range :=
  principalSubrepresentation_isDualCover h

/-- The dual of the universal dual cover, with its restriction map. -/
def universalDualProjection (ρ : Representation k G V) :
    (universalAction ρ).dual.IntertwiningMap ρ.dual :=
  dualIntertwining (principalIntertwining ρ)

/-- The dual of the universal dual cover covers the dual of the original module. -/
lemma universalDualProjection_isCover [Finite G] [FiniteDimensional k V]
    (ρ : Representation k G V) (h : fixed ρ = ⊥) :
    IsCover (universalDualProjection ρ) :=
  dualCover_dual_isCover (principalIntertwining ρ) (principal_injective h)
    (principalIntertwining_isDualCover ρ h)

/-- The kernel of restriction is dual to the first-cohomology quotient. -/
lemma finrank_ker_universalDualProjection [Finite G] [FiniteDimensional k V]
    (ρ : Representation k G V) :
    finrank k (universalDualProjection ρ).toLinearMap.ker = finrank k (H1 ρ) := by
  change finrank k (principal ρ).dualMap.ker = _
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  exact (Subspace.quotEquivAnnihilator (principal ρ).range).finrank_eq.symm

/-- An equivariant identification of coefficients intertwines the universal actions. -/
lemma cocyclesCongr_universalAction (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (g : G) (f : cocycles ρ) :
    cocyclesCongr ρ σ (MulEquiv.refl G) e he (universalAction ρ g f) =
      universalAction σ g (cocyclesCongr ρ σ (MulEquiv.refl G) e he f) := by
  ext t
  change e (f.val t + (ρ t (f.val g) - f.val g)) =
    e (f.val t) + (σ t (e (f.val g)) - e (f.val g))
  rw [map_add, map_sub, he]

/-- Every dual cover embeds in the cocycle construction compatibly with its base. -/
lemma exists_dualCoverEmbedding (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (h : IsDualCover i.range) :
    ∃ d : σ.IntertwiningMap (universalAction ρ), Function.Injective d ∧
      ∀ v, d (i v) = principal ρ v := by
  let e : V ≃ₗ[k] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  have he : ∀ g v, e.symm (i.range.toRepresentation g v) = ρ g (e.symm v) := by
    intro g v
    apply e.injective
    apply Subtype.ext
    change (e (e.symm (i.range.toRepresentation g v)) : W) = i (ρ g (e.symm v))
    rw [e.apply_symm_apply, i.isIntertwining]
    exact congrArg (σ g) (congrArg Subtype.val (e.apply_symm_apply v)).symm
  let t := cocyclesCongr i.range.toRepresentation ρ (MulEquiv.refl G) e.symm he
  let d := t.toLinearMap.comp (displacementCocycle i.range h.1)
  have hd : ∀ g w, d (σ g w) = universalAction ρ g (d w) := by
    intro g w
    dsimp only [d, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [displacementCocycle_equivariant]
    exact cocyclesCongr_universalAction e.symm he g _
  refine ⟨d.intertwiningMap_of_isIntertwiningMap _ _ hd,
    t.injective.comp (displacementCocycle_injective i.range h.1 h.2), ?_⟩
  intro v
  change t (displacementCocycle i.range h.1 (i v)) = principal ρ v
  have hv : displacementCocycle i.range h.1 (i v) =
      principal i.range.toRepresentation (e v) := rfl
  rw [hv]
  exact (cocyclesCongr_principal _ _ _ _ _ _).trans
    (congrArg (principal ρ) (e.symm_apply_apply v))

/-- Evaluation intertwines the double contragredient with the original action. -/
noncomputable def evaluationIntertwining (ρ : Representation k G V) [FiniteDimensional k V] :
    ρ.dual.dual.IntertwiningMap ρ :=
  (Module.evalEquiv k V).symm.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g f
    apply (Module.evalEquiv k V).injective
    ext l
    change (Module.evalEquiv k V) ((Module.evalEquiv k V).symm (ρ.dual.dual g f)) l =
      l (ρ g ((Module.evalEquiv k V).symm f))
    rw [LinearEquiv.apply_symm_apply]
    change f (ρ.dual g⁻¹ l) = _
    rw [← Module.apply_evalEquiv_symm_apply k V (ρ.dual g⁻¹ l) f]
    change l (ρ ((g⁻¹)⁻¹) ((Module.evalEquiv k V).symm f)) = _
    rw [inv_inv])

/-- The covering projection `U(G,V*)* → V`. -/
noncomputable def universalCoverProjection (ρ : Representation k G V) [FiniteDimensional k V] :
    (universalAction ρ.dual).dual.IntertwiningMap ρ :=
  (evaluationIntertwining ρ).comp (universalDualProjection ρ.dual)

/-- For `V = [V,G]`, the explicit projection `U(G,V*)* → V` is a cover. -/
lemma universalCoverProjection_isCover [Finite G] [FiniteDimensional k V]
    (ρ : Representation k G V) (h : Coinvariants.ker ρ = ⊤) :
    IsCover (universalCoverProjection ρ) := by
  have hu := universalDualProjection_isCover ρ.dual ((fixed_dual_eq_bot_iff ρ).mpr h)
  refine ⟨(Module.evalEquiv k V).symm.surjective.comp hu.1, ?_, hu.2.2⟩
  intro f hf
  apply hu.2.1
  change (Module.evalEquiv k V).symm (universalDualProjection ρ.dual f) = 0 at hf
  exact (Module.evalEquiv k V).symm.injective (hf.trans (map_zero _).symm)

/-- The central kernel of the universal cover has dimension `dim H¹(G,V*)`. -/
lemma finrank_ker_universalCoverProjection [Finite G] [FiniteDimensional k V]
    (ρ : Representation k G V) :
    finrank k (universalCoverProjection ρ).toLinearMap.ker = finrank k (H1 ρ.dual) := by
  have hk : (universalCoverProjection ρ).toLinearMap.ker =
      (universalDualProjection ρ.dual).toLinearMap.ker := by
    ext f
    change (Module.evalEquiv k V).symm (universalDualProjection ρ.dual f) = 0 ↔ _
    rw [map_eq_zero_iff _ (Module.evalEquiv k V).symm.injective]
    rfl
  rw [hk]
  exact finrank_ker_universalDualProjection ρ.dual

/-- Every finite-dimensional cover is an equivariant quotient of `U(G,V*)*`,
with the quotient map commuting with the given projections to `V`. -/
lemma exists_universalCover_quotient [FiniteDimensional k V] [FiniteDimensional k W]
    (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    ∃ q : (universalAction ρ.dual).dual.IntertwiningMap σ,
      Function.Surjective q ∧ ∀ u, p (q u) = universalCoverProjection ρ u := by
  obtain ⟨d, hd, hdp⟩ := exists_dualCoverEmbedding (dualIntertwining p)
    (LinearMap.dualMap_injective_of_surjective hp.1) (cover_dual_isDualCover p hp)
  let dd : (universalAction ρ.dual).dual.IntertwiningMap σ.dual.dual :=
    dualIntertwining (V := cocycles ρ.dual) (W := Module.Dual k W) d
  let q : (universalAction ρ.dual).dual.IntertwiningMap σ :=
    (evaluationIntertwining σ).comp dd
  have hs : Function.Surjective d.toLinearMap.dualMap :=
    LinearMap.dualMap_surjective_of_injective (K := k) (V₁ := Module.Dual k W)
      (V₂ := cocycles ρ.dual) (f := d.toLinearMap) hd
  refine ⟨q, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ := hs (Module.evalEquiv k W w)
    refine ⟨u, ?_⟩
    change (Module.evalEquiv k W).symm (d.toLinearMap.dualMap u) = w
    rw [hu, LinearEquiv.symm_apply_apply]
  · intro u
    apply (Module.evalEquiv k V).injective
    ext f
    change f (p ((Module.evalEquiv k W).symm (d.toLinearMap.dualMap u))) =
      (Module.evalEquiv k V) ((Module.evalEquiv k V).symm
        ((principal ρ.dual).dualMap u)) f
    rw [LinearEquiv.apply_symm_apply]
    change (dualIntertwining p f) ((Module.evalEquiv k W).symm
      (d.toLinearMap.dualMap u)) = u (principal ρ.dual f)
    rw [Module.apply_evalEquiv_symm_apply]
    change u (d (dualIntertwining p f)) = u (principal ρ.dual f)
    rw [hdp]
end Representation.OneCohomology
