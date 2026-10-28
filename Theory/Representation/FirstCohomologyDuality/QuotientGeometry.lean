module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Geometry through a central module covering

A cover with the maximal central-kernel dimension is isomorphic to the
cohomological universal cover, over the original projection. Consequently it
maps onto every cover of the same module. Images preserve commutator spaces,
and inverse images of subspaces agree along these compatible surjections.
This transports a root-space calculation from a concrete universal model to
arbitrary covers, which need only be linear over the ground field.

Scalar restriction is handled separately: a commutator space is already
closed under the larger field, even though its definition uses the ground
field span. Thus restricting scalars preserves the covering property.

Source: Aschbacher--Smith, Remark I.1.5 and Lemma I.2.3, printed pp.408, 413
of the combined manuscript (1 March 2004).
-/

@[expose] public section

namespace Representation.OneCohomology

section ScalarRestriction
variable {k K G V W : Type*} [Field k] [Field K] [Algebra k K] [Group G]
  [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
  [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]

/-- Restricting scalars does not change the commutator space as a set. -/
theorem coinvariants_restrictScalars (ρ : Representation K G V) :
    Coinvariants.ker (restrictScalars (k := k) ρ) =
      (Coinvariants.ker ρ).restrictScalars k := by
  let C := Coinvariants.ker (restrictScalars (k := k) ρ)
  have hs (a : K) (v : V) (hv : v ∈ C) : a • v ∈ C := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g, w⟩, rfl⟩ := hv
      change a • (ρ g w - w) ∈ C
      rw [smul_sub, ← map_smul]
      exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g (a • w)
    | zero => simpa only [smul_zero] using C.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using C.add_mem hx hy
    | smul r x _ hx => simpa only [smul_comm a r] using C.smul_mem r hx
  let D : Submodule K V :=
    { carrier := C, zero_mem' := C.zero_mem, add_mem' := C.add_mem, smul_mem' := hs }
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker g v
  · have hD : Coinvariants.ker ρ ≤ D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g v
    exact hD

/-- The same equivariant map, with its coefficient field restricted. -/
def restrictCoverMap {ρ : Representation K G V} {σ : Representation K G W}
    (p : σ.IntertwiningMap ρ) :
    (restrictScalars (k := k) σ).IntertwiningMap (restrictScalars (k := k) ρ) :=
  (p.toLinearMap.restrictScalars k).intertwiningMap_of_isIntertwiningMap _ _
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v)

/-- Field-linear covers remain covers over the ground field. -/
theorem isCover_restrictScalars {ρ : Representation K G V} {σ : Representation K G W}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    IsCover (restrictCoverMap (k := k) p) := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [coinvariants_restrictScalars, hp.2.2]
  rfl
end ScalarRestriction

section Quotients
variable {k G N V W : Type*} [Field k] [Group G]
  [AddCommGroup N] [Module k N]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G N} {σ : Representation k G V} {τ : Representation k G W}

/-- An equivariant surjection maps the commutator space onto the commutator space. -/
theorem map_coinvariants_of_surjective (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) :
    (Coinvariants.ker σ).map f.toLinearMap = Coinvariants.ker τ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change f (σ g v - v) ∈ Coinvariants.ker τ
    rw [map_sub, f.isIntertwining]
    exact Coinvariants.sub_mem_ker g (f v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨σ g v - v, Coinvariants.sub_mem_ker g v, by
      change f (σ g v - v) = _
      rw [map_sub, f.isIntertwining]⟩

/-- The literal preimages of a subspace agree under compatible covering maps. -/
theorem map_preimage_of_surjective
    (p : σ.IntertwiningMap ρ) (q : τ.IntertwiningMap ρ)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f)
    (hover : ∀ v, q (f v) = p v) (A : Submodule k N) :
    (A.comap p.toLinearMap).map f.toLinearMap = A.comap q.toLinearMap := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change q (f v) ∈ A
    rw [hover]
    exact hv
  · intro hw
    obtain ⟨v, rfl⟩ := hf w
    refine ⟨v, ?_, rfl⟩
    change p v ∈ A
    rw [← hover]
    exact hw

/-- Root commutator and root-centrality calculations descend through the actual
quotient map. No larger coefficient-field structure on the target is required. -/
theorem preimage_root_geometry_of_surjective
    (p : σ.IntertwiningMap ρ) (q : τ.IntertwiningMap ρ)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f)
    (hover : ∀ v, q (f v) = p v) (R : Subgroup G) (A : Submodule k N)
    (hcomm : A.comap p.toLinearMap = Coinvariants.ker (σ.comp R.subtype))
    (hfixed : A.comap p.toLinearMap ≤ fixed (σ.comp R.subtype)) :
    A.comap q.toLinearMap = Coinvariants.ker (τ.comp R.subtype) ∧
      A.comap q.toLinearMap ≤ fixed (τ.comp R.subtype) := by
  let fR : Representation.IntertwiningMap (σ.comp R.subtype) (τ.comp R.subtype) :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g v => LinearMap.congr_fun (f.isIntertwining' g.val) v)
  have hm := map_preimage_of_surjective p q f hf hover A
  constructor
  · rw [← hm, hcomm]
    exact map_coinvariants_of_surjective fR hf
  · intro w hw g
    obtain ⟨v, hv, rfl⟩ := hm.symm ▸ hw
    change τ g.val (f v) = f v
    rw [← f.isIntertwining]
    exact congrArg f (hfixed hv g)

/-- Fixed points of a covering map lie over fixed points of the quotient. -/
theorem fixed_le_preimage (q : τ.IntertwiningMap ρ) (A : Submodule k N)
    (hA : fixed ρ ≤ A) : fixed τ ≤ A.comap q.toLinearMap := by
  intro w hw
  apply hA
  intro g
  change ρ g (q w) = q w
  rw [← q.isIntertwining, hw g]

variable [Finite G] [FiniteDimensional k N] [FiniteDimensional k V]

/-- A cover attaining the cohomological kernel bound is the universal cover,
with both equivariance and compatibility with the original projection. -/
theorem exists_equiv_universalCover_of_finrank_ker_eq
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hd : Module.finrank k p.toLinearMap.ker = Module.finrank k (H1 ρ.dual)) :
    ∃ e : Module.Dual k (cocycles ρ.dual) ≃ₗ[k] V,
      (∀ g u, e ((universalAction ρ.dual).dual g u) = σ g (e u)) ∧
      ∀ u, p (e u) = universalCoverProjection ρ u := by
  let : FiniteDimensional k (Module.Dual k (cocycles ρ.dual)) :=
    Subspace.instModuleDualFiniteDimensional (K := k) (V := cocycles ρ.dual)
  obtain ⟨f, hf, hfp⟩ := exists_universalCover_quotient p hp
  have hu : Function.Surjective (universalCoverProjection ρ) := by
    intro n
    obtain ⟨v, rfl⟩ := hp.1 n
    obtain ⟨u, rfl⟩ := hf v
    exact ⟨u, (hfp u).symm⟩
  have hU := (universalCoverProjection ρ).toLinearMap.finrank_range_add_finrank_ker
  have hV := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hu, finrank_top,
    finrank_ker_universalCoverProjection] at hU
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, hd] at hV
  let e := LinearEquiv.ofBijective f.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hU.symm.trans hV)).mpr hf, hf⟩
  exact ⟨e, fun g u => LinearMap.congr_fun (f.isIntertwining' g) u, hfp⟩

/-- Every cover is a quotient of a concrete cover attaining the cohomological
kernel bound. The resulting map commutes with the given projections. -/
theorem exists_quotient_of_finrank_ker_eq [FiniteDimensional k W]
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hd : Module.finrank k p.toLinearMap.ker = Module.finrank k (H1 ρ.dual))
    (q : τ.IntertwiningMap ρ) (hq : IsCover q) :
    ∃ f : σ.IntertwiningMap τ, Function.Surjective f ∧ ∀ v, q (f v) = p v := by
  obtain ⟨e, he, hep⟩ := exists_equiv_universalCover_of_finrank_ker_eq p hp hd
  obtain ⟨b, hb, hbq⟩ := exists_universalCover_quotient q hq
  have hei (g : G) (v : V) :
      e.symm (σ g v) = (universalAction ρ.dual).dual g (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let f : σ.IntertwiningMap τ :=
    (b.toLinearMap.comp e.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _
      (fun g v => by
        change b (e.symm (σ g v)) = τ g (b (e.symm v))
        rw [hei, b.isIntertwining])
  refine ⟨f, hb.comp e.symm.surjective, ?_⟩
  intro v
  change q (b (e.symm v)) = p v
  rw [hbq, ← hep, e.apply_symm_apply]

end Quotients
end Representation.OneCohomology
