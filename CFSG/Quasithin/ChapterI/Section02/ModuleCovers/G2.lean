module

public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.G2OrthogonalCover.RootGeometry
public import Theory.Representation.G2OrthogonalCover.Quotients

/-!
# I.2.3: the orthogonal universal L-cover for the natural G₂′ module

The actual trace-zero octonion seven-space, with the restricted norm and
literal projection onto its scalar-line quotient, realizes the universal
binary cover. The model group is the commutator subgroup of `Atlas.G2.Model F`,
including the genuine G₂(2)′. The construction proves the invariant form,
quadratic nondegeneracy, fixed and polar radical, and the map-compatible
universal comparison; no larger ambient G-action is inferred from it.

The Sylow-fixed and long-root calculations are assembled with this universal
comparison for every selected invariant flag of every actual derived Sylow.
Both singular complements and their literal natural-space preimages pass
through the same quotient map to an arbitrary binary cover. Its central
kernel is retained as a binary space. The original ambient G-action remains
a separate assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma I.2.3, printed p.413 / PDF p.424.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterI.ModuleCovers.G2
open Representation Representation.OneCohomology
open Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable (F : Type*) [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- The concrete orthogonal realization of the universal binary natural L-cover.
Every map and action here is the actual split-octonion one. -/
theorem orthogonal_universal_cover :
    Module.finrank F (TraceZero F) = 7 ∧
    (form F).Nondegenerate ∧
    (∀ g x, form F (OrthogonalCover.action F g x) = form F x) ∧
    (form F).polarBilin.ker = scalarLine F ∧
    fixed (OrthogonalCover.action F) = scalarLine F ∧
    Module.finrank F (scalarLine F) = 1 ∧
    IsCover (binaryProjection F) ∧
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural F).dual) ≃ₗ[ZMod 2] TraceZero F,
      (∀ g u, e ((universalAction (binaryNatural F).dual).dual g u) = binaryAction F g (e u)) ∧
      ∀ u, mk F (e u) = universalCoverProjection (binaryNatural F) u :=
  ⟨finrank_traceZero F, form_nondegenerate F, form_invariant F, polar_ker F,
    fixed_eq_scalarLine F, finrank_scalarLine F, binaryProjection_isCover F,
    universal_equiv F⟩

/-- The source quotient step retains the literal map to the natural six-space;
the target cover has only its original binary module structure. -/
theorem every_cover_is_orthogonal_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (commutator (Atlas.G2.Model F)) W}
    (p : σ.IntertwiningMap (binaryNatural F)) (hp : IsCover p) :
    ∃ f : (binaryAction F).IntertwiningMap σ, Function.Surjective f ∧
      ∀ w, p (f w) = mk F w :=
  OrthogonalCover.exists_quotient F p hp

omit [Finite F] [Algebra (ZMod 2) F] in
/-- The actual long-root plane calculation for the orthogonal model. The all-Sylow
placement and source-selected flag are assembled with universality in
`universal_cover_selected_flag` below. -/
theorem long_root_plane :
    Module.finrank F (Coinvariants.ker ((OrthogonalCover.action F).comp (longRoot F).subtype)) = 2 ∧
    (∀ x ∈ Coinvariants.ker ((OrthogonalCover.action F).comp (longRoot F).subtype), form F x = 0) ∧
    Disjoint (Coinvariants.ker ((OrthogonalCover.action F).comp (longRoot F).subtype)) (scalarLine F) ∧
    (naturalPlane F).comap (mk F) =
      Coinvariants.ker ((OrthogonalCover.action F).comp (longRoot F).subtype) ⊔ scalarLine F :=
  longRoot_geometry F

/-- Both the actual long-root commutator plane and the literal natural-plane
preimage transport along the same compatible quotient to an arbitrary cover. -/
theorem every_cover_root_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (commutator (Atlas.G2.Model F)) W}
    (p : σ.IntertwiningMap (binaryNatural F)) (hp : IsCover p) :
    ∃ f : (binaryAction F).IntertwiningMap σ, Function.Surjective f ∧
      (∀ w, p (f w) = mk F w) ∧
      ((singularPlane F).restrictScalars (ZMod 2)).map f.toLinearMap =
        Coinvariants.ker (σ.comp (longRoot F).subtype) ∧
      (((naturalPlane F).restrictScalars (ZMod 2)).comap
        (binaryProjection F).toLinearMap).map f.toLinearMap =
        ((naturalPlane F).restrictScalars (ZMod 2)).comap p.toLinearMap := by
  obtain ⟨f, hf, hover⟩ := OrthogonalCover.exists_quotient F p hp
  refine ⟨f, hf, hover, ?_, ?_⟩
  · let fR : Representation.IntertwiningMap ((binaryAction F).comp (longRoot F).subtype)
        (σ.comp (longRoot F).subtype) :=
      f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
        (fun g w => LinearMap.congr_fun (f.isIntertwining' g.val) w)
    have he : Coinvariants.ker ((binaryAction F).comp (longRoot F).subtype) =
        (singularPlane F).restrictScalars (ZMod 2) := by
      change Coinvariants.ker (restrictScalars (k := ZMod 2)
        ((OrthogonalCover.action F).comp (longRoot F).subtype)) = _
      rw [coinvariants_restrictScalars, longRoot_commutator]
    rw [← he]
    exact map_coinvariants_of_surjective fR hf
  · exact map_preimage_of_surjective (binaryProjection F) p f hf hover _

/-- The universal binary L-cover and every source-selected Sylow flag, in one
projection-compatible orthogonal realization. The first preimage has its
unique singular point, and the central long-root plane complements the radical
in the second preimage. This includes the genuine derived G₂(2) group. -/
theorem universal_cover_selected_flag
    (Q : Sylow 2 (commutator (Atlas.G2.Model F)))
    (V1 V2 : Submodule F (Space F))
    (h1 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V1 ≤ V1.comap (derivedAction F t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V2 ≤ V2.comap (derivedAction F t.val))
    (d2 : Module.finrank F V2 = 2) :
    Module.finrank F (TraceZero F) = 7 ∧
    (form F).Nondegenerate ∧
    (∀ g x, form F (OrthogonalCover.action F g x) = form F x) ∧
    (form F).polarBilin.ker = scalarLine F ∧
    fixed (OrthogonalCover.action F) = scalarLine F ∧
    Module.finrank F (scalarLine F) = 1 ∧
    IsCover (binaryProjection F) ∧
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural F).dual) ≃ₗ[ZMod 2] TraceZero F,
      (∀ g u, e ((universalAction (binaryNatural F).dual).dual g u) = binaryAction F g (e u)) ∧
      (∀ u, mk F (e u) = universalCoverProjection (binaryNatural F) u) ∧
    ∃ g : commutator (Atlas.G2.Model F),
      (Q : Subgroup (commutator (Atlas.G2.Model F))) = movedSylow F g ∧
      V1 = movedLine F g ∧ V2 = movedPlane F g ∧
      movedRoot F g ≤ (Subgroup.center (Q : Subgroup (commutator (Atlas.G2.Model F)))).map
        (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype ∧
      V1.comap (mk F) = fixed ((OrthogonalCover.action F).comp
        (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype) ∧
      V1.comap (mk F) = movedPoint F g ⊔ scalarLine F ∧
      Disjoint (movedPoint F g) (scalarLine F) ∧
      Module.finrank F (movedPoint F g) = 1 ∧
      (∀ x ∈ movedPoint F g, form F x = 0) ∧
      (∀ R : Submodule F (TraceZero F), R ≤ V1.comap (mk F) →
        Module.finrank F R = 1 → (∀ x ∈ R, form F x = 0) → R = movedPoint F g) ∧
      Module.finrank F (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) = 2 ∧
      (∀ x ∈ Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype), form F x = 0) ∧
      Disjoint (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) (scalarLine F) ∧
      V2.comap (mk F) =
        Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype) ⊔ scalarLine F := by
  refine ⟨finrank_traceZero F, form_nondegenerate F, form_invariant F, polar_ker F,
    fixed_eq_scalarLine F, finrank_scalarLine F, binaryProjection_isCover F, ?_⟩
  apply (OrthogonalCover.universal_equiv F).imp
  rintro e ⟨he, hep⟩
  exact ⟨he, hep, selected_flag_geometry F Q V1 V2 h1 d1 h2 d2⟩

/-- The source quotient step for every selected flag and every binary cover.
The same equivariant surjection transports the point, both literal preimages,
and the actual long-root commutator plane. The complement dimensions are
binary dimensions; the arbitrary central kernel need not be an F-subspace. -/
theorem every_cover_selected_flag
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (commutator (Atlas.G2.Model F)) W}
    (p : σ.IntertwiningMap (binaryNatural F)) (hp : IsCover p)
    (Q : Sylow 2 (commutator (Atlas.G2.Model F)))
    (V1 V2 : Submodule F (Space F))
    (h1 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V1 ≤ V1.comap (derivedAction F t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V2 ≤ V2.comap (derivedAction F t.val))
    (d2 : Module.finrank F V2 = 2) :
    ∃ (g : commutator (Atlas.G2.Model F)) (f : (binaryAction F).IntertwiningMap σ),
      (Q : Subgroup (commutator (Atlas.G2.Model F))) = movedSylow F g ∧
      V1 = movedLine F g ∧ V2 = movedPlane F g ∧
      movedRoot F g ≤ (Subgroup.center (Q : Subgroup (commutator (Atlas.G2.Model F)))).map
        (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype ∧
      Function.Surjective f ∧ (∀ w, p (f w) = mk F w) ∧
      fixed σ = p.toLinearMap.ker ∧
      fixed (σ.comp (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype) =
        (V1.restrictScalars (ZMod 2)).comap p.toLinearMap ∧
      (V1.restrictScalars (ZMod 2)).comap p.toLinearMap =
        ((movedPoint F g).restrictScalars (ZMod 2)).map f.toLinearMap ⊔ fixed σ ∧
      Disjoint (((movedPoint F g).restrictScalars (ZMod 2)).map f.toLinearMap) (fixed σ) ∧
      Module.finrank (ZMod 2) (((movedPoint F g).restrictScalars (ZMod 2)).map f.toLinearMap) =
        Module.finrank (ZMod 2) F ∧
      (((singularPlane F).map (OrthogonalCover.action F g)).restrictScalars (ZMod 2)).map
        f.toLinearMap = Coinvariants.ker (σ.comp (movedRoot F g).subtype) ∧
      (V2.restrictScalars (ZMod 2)).comap p.toLinearMap =
        Coinvariants.ker (σ.comp (movedRoot F g).subtype) ⊔ fixed σ ∧
      Disjoint (Coinvariants.ker (σ.comp (movedRoot F g).subtype)) (fixed σ) ∧
      Module.finrank (ZMod 2) (Coinvariants.ker (σ.comp (movedRoot F g).subtype)) =
        2 * Module.finrank (ZMod 2) F := by
  obtain ⟨g, hg⟩ := exists_marking F Q
  have e1 : V1 = movedLine F g := movedLine_unique F g V1 (hg ▸ h1) d1
  have e2 : V2 = movedPlane F g := movedPlane_unique F g V2 (hg ▸ h2) d2
  obtain ⟨f, hf, hover⟩ := OrthogonalCover.exists_quotient F p hp
  have hk := cover_fixed_eq_kernel F p hp
  have hr := movedRoot_geometry F g
  rw [movedRoot_commutator] at hr
  have hc := quotient_root_commutator F f hf g
  refine ⟨g, f, hg, e1, e2, ?_, hf, hover, hk, ?_, ?_, ?_, ?_, hc, ?_, ?_, ?_⟩
  · rw [hg]
    exact movedRoot_central F g
  · rw [hg, e1]
    exact quotient_sylow_fixed F p f hf hover g
  · rw [e1, hk]
    exact quotient_preimage_complement F p f hf hover _ _ (movedLine_preimage F g)
  · rw [hk]
    exact quotient_complement_disjoint F p f hover _ (movedPoint_disjoint F g)
  · rw [quotient_complement_finrank F p f hover _ (movedPoint_disjoint F g),
      movedPoint_finrank, mul_one]
  · rw [e2, hk, ← hc]
    exact quotient_preimage_complement F p f hf hover _ _ hr.2.2.2
  · rw [hk, ← hc]
    exact quotient_complement_disjoint F p f hover _ hr.2.2.1
  · rw [← hc, quotient_complement_finrank F p f hover _ hr.2.2.1, hr.1, mul_comm]

end CFSG.Quasithin.ChapterI.ModuleCovers.G2
