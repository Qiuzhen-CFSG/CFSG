module

public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.Representation.SL2FourCentralCover.Coordinates
public import Theory.Representation.SL2FourCentralCover.OuterObstruction

/-!
# I.2.3: natural-module covers

The general quotient step takes a concrete cover attaining the dual-cohomology
bound and transports its root commutator and centrality calculations to every
cover, with the original projection retained. This is the step from the
universal model to arbitrary binary covers in the source proof.

For the natural SL₂(4) module the explicit three-dimensional field cover
already constructed in `SL2FourCentralCover` supplies those premises. We
identify it with the actual universal binary cover and prove all of (3) for
every cover of that marked natural module. This is the natural A₅ module,
not the other four-dimensional orthogonal A₅ module.

The full orthogonal realizations, the other field orders and families, and
the original ambient `G = LT` conclusions remain separate proof obligations.
In particular the general conditional quotient lemma is not asserted to be
the complete source theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma I.2.3,
printed p.413 (PDF p.424), using Remark I.1.5 and Lemma I.1.6, p.408.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterI.ModuleCovers
open Representation Representation.OneCohomology

section Descent
variable {k G N V W : Type*} [Field k] [Group G] [Finite G]
  [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {ρ : Representation k G N} {σ : Representation k G V} {τ : Representation k G W}

/-- The quotient step in I.2.3(3). The kernel dimension and the two root-space
identities are explicit model obligations, discharged in the concrete
application below; no structure theorem is inferred from dimension alone. -/
theorem root_geometry_of_maximal_cover
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hd : Module.finrank k p.toLinearMap.ker = Module.finrank k (H1 ρ.dual))
    (R : Subgroup G) (A : Submodule k N) (hA : fixed ρ ≤ A)
    (hcomm : A.comap p.toLinearMap = Coinvariants.ker (σ.comp R.subtype))
    (hfixed : A.comap p.toLinearMap ≤ fixed (σ.comp R.subtype))
    (q : τ.IntertwiningMap ρ) (hq : IsCover q) :
    fixed τ ≤ A.comap q.toLinearMap ∧
      A.comap q.toLinearMap = Coinvariants.ker (τ.comp R.subtype) ∧
      A.comap q.toLinearMap ≤ fixed (τ.comp R.subtype) := by
  obtain ⟨f, hf, hover⟩ := exists_quotient_of_finrank_ker_eq p hp hd q hq
  exact ⟨fixed_le_preimage q A hA,
    preimage_root_geometry_of_surjective p q f hf hover R A hcomm hfixed⟩
end Descent

namespace LinearTwoFour
open Representation.SL2FourNatural Representation.SL2FourCentralCover
open Matrix.SpecialLinearGroup

/-- The invariant F₄-line, regarded as an additive binary subspace. -/
def firstLine : Submodule (ZMod 2) V := (LinearMap.proj (1 : Fin 2)).ker

/-- Its literal inverse image in a binary cover. -/
def firstPreimage {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) : Submodule (ZMod 2) W :=
  firstLine.comap p.toLinearMap

private theorem projection_cover : IsCover projection := by
  exact isCover_restrictScalars (k := ZMod 2) fieldProjection fieldProjection_isCover

private theorem projection_kernel_dimension :
    Module.finrank (ZMod 2) projection.toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 naturalRepresentation.dual) := by
  have h := projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr projection_cover.1, finrank_top,
    finrank_vector, binary_finrank] at h
  rw [natural_dual_H1_finrank]
  omega

/-- A map-compatible identification of the actual universal binary cover with
the three-dimensional F₄ cover of the natural SL₂(4) module. -/
theorem universal_equiv :
    ∃ e : Module.Dual (ZMod 2) (cocycles naturalRepresentation.dual) ≃ₗ[ZMod 2] Space,
      (∀ g u, e ((universalAction naturalRepresentation.dual).dual g u) =
        binaryAction g (e u)) ∧
      ∀ u, projection (e u) = universalCoverProjection naturalRepresentation u :=
  exists_equiv_universalCover_of_finrank_ker_eq projection projection_cover
    projection_kernel_dimension

private theorem model_preimage_eq_commutator :
    firstPreimage projection = Coinvariants.ker (binaryAction.comp (upperUnipotent F).subtype) := by
  apply le_antisymm
  · intro w hw
    have hw' : (coordinates w).2 1 = 0 := hw
    obtain ⟨s, t, u, v, he⟩ := fixed_is_sum_of_upper_displacements w hw'
    have hgen (a : F) (x : Space) : binaryAction (upper a) x - x ∈
        Coinvariants.ker (binaryAction.comp (upperUnipotent F).subtype) := by
      exact Coinvariants.sub_mem_ker
        (ρ := binaryAction.comp (upperUnipotent F).subtype)
        ⟨upper a, (mem_upperUnipotent F _).mpr ⟨a, (upper_transvection a).symm⟩⟩ x
    rw [he]
    exact Submodule.add_mem _ (hgen s u) (hgen t v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F g.val).mp g.property
    have hg : g.val = upper t := ht.symm.trans (upper_transvection t).symm
    change projection (binaryAction g.val w - w) 1 = 0
    rw [hg]
    change (coordinates (binaryAction (upper t) w - w)).2 1 = 0
    rw [coordinates_upper_displacement]
    rfl

private theorem model_preimage_fixed :
    firstPreimage projection ≤ fixed (binaryAction.comp (upperUnipotent F).subtype) := by
  intro w hw g
  obtain ⟨t, ht⟩ := (mem_upperUnipotent F g.val).mp g.property
  have hg : g.val = upper t := ht.symm.trans (upper_transvection t).symm
  change binaryAction g.val w = w
  rw [hg]
  by_cases ht0 : t = 0
  · subst t
    rw [upper_transvection]
    simp
  · exact (upper_fixed_iff t ht0 w).mpr hw

/-- I.2.3(3) for every cover of the marked natural SL₂(4) module. The cover
has only a binary module structure; its kernel need not be an F₄-subspace. -/
theorem cover_root_geometry {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p) :
    fixed σ ≤ firstPreimage p ∧
      firstPreimage p = Coinvariants.ker (σ.comp (upperUnipotent F).subtype) ∧
      firstPreimage p ≤ fixed (σ.comp (upperUnipotent F).subtype) := by
  apply root_geometry_of_maximal_cover projection projection_cover projection_kernel_dimension
    (upperUnipotent F) firstLine _ model_preimage_eq_commutator model_preimage_fixed p hp
  intro v hv
  have hz : v = 0 := natural_fixed_eq_zero v hv
  rw [hz]
  exact firstLine.zero_mem

/-- The full universal L-cover cannot also be a central G-cover when a G-actor
induces the field involution with its actual root conjugation. This checks a
potentially invalid step in extending the L-module statement of I.2.3 to G;
it does not assume that L-covering and G-covering are interchangeable. -/
theorem not_ambient_central_cover_of_frobenius
    {G : Type*} [Group G] (ι : SL →* G)
    (σ : Representation (ZMod 2) G Space) (ρ : Representation (ZMod 2) G V)
    (p : σ.IntertwiningMap ρ)
    (hprojection : ∀ w, p w = projection w)
    (hrestrict : ∀ g w, σ (ι g) w = binaryAction g w)
    (s : G) (hfield : ∀ v i, ρ s v i = (v i) ^ 2)
    (hconj : ∀ t, s * ι (upper t) = ι (upper (t ^ 2)) * s) :
    ¬ IsCover p := by
  intro hp
  apply no_pointwise_central_frobenius_lift (σ s)
  · intro w i
    have he := LinearMap.congr_fun (p.isIntertwining' s) w
    change p (σ s w) = ρ s (p w) at he
    rw [hprojection, hprojection] at he
    exact (congrFun he i).trans (hfield (projection w) i)
  · intro t w
    rw [← hrestrict, ← hrestrict]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hconj]
  · intro w hw
    apply hp.2.1 (show p w = 0 by rw [hprojection, hw]) s

end LinearTwoFour
end CFSG.Quasithin.ChapterI.ModuleCovers
