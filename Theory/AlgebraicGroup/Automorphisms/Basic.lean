module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Borel.SemisimpleCenter
public import Theory.AlgebraicGroup.Simple.Basic
public import Theory.AlgebraicGroup.Tori.Maximal

universe u

/-! Infrastructure for GLS3, Theorem 1.15.2. -/

/-! Finite kernels of surjective endomorphisms. -/
namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem surjectiveEndomorphism_kernel_finite
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : Function.Surjective σ.onPoints) :
    Finite σ.kernel := by
  have himageDimension :
      Variety.dimension σ.imageClosedSubgroup.carrierVariety =
        Variety.dimension K := by
    apply (closedSubgroup_dimension_eq_iff_contains_identityComponent K σ.imageClosedSubgroup).2
    intro x hx
    change x ∈ σ.image
    exact hσ x
  have hdimension := morphism_dimension_eq_kernel_add_image σ
  rw [himageDimension] at hdimension
  have hkernelDimension :
      Variety.dimension σ.kernelClosedSubgroup.carrierVariety = 0 := by
    apply (Cardinal.add_right_inj_of_lt_aleph0
      (variety_dimension_lt_aleph0 K)).mp
    calc
      Variety.dimension σ.kernelClosedSubgroup.carrierVariety +
          Variety.dimension K = Variety.dimension K := hdimension.symm
      _ = 0 + Variety.dimension K := (zero_add _).symm
  have hkernelPoints :
      Finite (Variety.Point σ.kernelClosedSubgroup.carrierVariety) :=
    (dimension_zero_iff_finite_points σ.kernelClosedSubgroup.carrierVariety).1
      hkernelDimension
  have hkernelSubtype : Finite σ.kernelClosedSubgroup.toSubgroup :=
    (Equiv.finite_iff σ.kernelClosedSubgroup.pointEquiv).1 hkernelPoints
  let e : σ.kernelClosedSubgroup.toSubgroup ≃ σ.kernel :=
    Equiv.setCongr (AlgebraicGroup.Morphism.kernelClosedSubgroup_carrier σ)
  exact (Equiv.finite_iff e).1 hkernelSubtype

end

/-! Injectivity of semisimple endomorphisms. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma surjectiveSemisimpleEndomorphism_injective
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : IsSemisimpleAlgebraicGroup K)
    (hσ : Function.Surjective σ.onPoints) :
    Function.Injective σ.onPoints := by
  have hkernelFinite : Finite σ.kernel :=
    surjectiveEndomorphism_kernel_finite σ hσ
  have hIsogeny : IsIsogeny σ := ⟨hσ, hkernelFinite⟩
  have hkernelCenter := isogeny_kernel_le_center_of_connected σ hIsogeny hK.1
  have hcenterImage := isogeny_image_center_eq_center_of_connected σ hIsogeny hK.1
  let : Finite (Subgroup.center (Variety.Point K)) :=
    connectedSemisimple_center_finite hK
  let σZ : Subgroup.center (Variety.Point K) →
      Subgroup.center (Variety.Point K) := fun z =>
    ⟨σ.onPoints z, by
      have hzImage : σ.onPoints z ∈ σ.onPoints ''
          (Subgroup.center (Variety.Point K) : Set (Variety.Point K)) :=
        ⟨z, z.property, rfl⟩
      have hzCenter : σ.onPoints z ∈
          (Subgroup.center (Variety.Point K) : Set (Variety.Point K)) := by
        rw [← hcenterImage]
        exact hzImage
      exact hzCenter⟩
  have hσZsurjective : Function.Surjective σZ := by
    intro z
    have hz : z.1 ∈ σ.onPoints ''
        (Subgroup.center (Variety.Point K) : Set (Variety.Point K)) := by
      rw [hcenterImage]
      exact z.property
    obtain ⟨x, hx, hσx⟩ := hz
    exact ⟨⟨x, hx⟩, Subtype.ext hσx⟩
  have hσZinjective : Function.Injective σZ :=
    (Finite.injective_iff_surjective).2 hσZsurjective
  have hkernelTrivial : ∀ x, x ∈ σ.kernel → x = 1 := by
    intro x hx
    have hxCenter : x ∈ Subgroup.center (Variety.Point K) :=
      hkernelCenter x hx
    let xZ : Subgroup.center (Variety.Point K) := ⟨x, hxCenter⟩
    have hσZone : σZ xZ = σZ 1 := by
      apply Subtype.ext
      change σ.onPoints x = σ.onPoints 1
      rw [show σ.onPoints x = 1 from hx, map_one]
    have hxZone : xZ = 1 := hσZinjective hσZone
    exact congrArg Subtype.val hxZone
  intro x y hxy
  have hxyKernel : x * y⁻¹ ∈ σ.kernel := by
    change σ.onPoints (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hxyOne := hkernelTrivial (x * y⁻¹) hxyKernel
  calc
    x = (x * y⁻¹) * y := by group
    _ = 1 * y := congrArg (fun z => z * y) hxyOne
    _ = y := one_mul y

end

/-! Automorphism consequences for root data. -/
section
variable {k : Type u} [Field k]

public abbrev AlgebraicEndomorphism (K : Variety k) [AlgebraicGroup K] :=
  AlgebraicGroup.Morphism K K

/-- The automorphisms of `K` as an algebraic group. -/
public abbrev AlgebraicAutomorphism (K : Variety k) [AlgebraicGroup K] :=
  AlgebraicGroup.Iso K K

/-- The automorphisms of the abstract point group of `K`. -/
public abbrev AbstractAutomorphism (K : Variety k) [AlgebraicGroup K] :=
  Variety.Point K ≃* Variety.Point K

/-- `Aut₀(K)`, embedded in the abstract automorphism group. -/
@[expose]
public def AutZero (K : Variety k) [AlgebraicGroup K] :
    Subgroup (AbstractAutomorphism K) where
  carrier := Set.range AlgebraicGroup.Iso.toMulEquiv
  mul_mem' := by
    rintro _ _ ⟨e, rfl⟩ ⟨d, rfl⟩
    refine ⟨e.comp d, ?_⟩
    ext x
    rfl
  one_mem' := by
    refine ⟨AlgebraicGroup.Iso.id K, ?_⟩
    ext x
    rfl
  inv_mem' := by
    rintro _ ⟨e, rfl⟩
    refine ⟨⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩, ?_⟩
    ext x
    rfl

/-- `Aut(K)`, the full abstract automorphism group. -/
public abbrev Aut (K : Variety k) [AlgebraicGroup K] := AbstractAutomorphism K

@[expose]
public def IsAlgebraicRealization
    {K : Variety k} [AlgebraicGroup K]
    (σ : Aut K) (f : AlgebraicEndomorphism K) : Prop :=
  ∀ x, σ x = f.onPoints x

/-- `Aut₁(K)` as a set. Its subgroup property is Theorem 1.15.7(a). -/
@[expose]
public def AutOneSet (K : Variety k) [AlgebraicGroup K] : Set (Aut K) :=
  {σ | (∃ f : AlgebraicEndomorphism K, IsAlgebraicRealization σ f) ∨
    ∃ f : AlgebraicEndomorphism K, IsAlgebraicRealization σ.symm f}

/-- The canonical inner-conjugation map of the abstract point group. -/
@[expose]
public def innerConjugationMap (K : Variety k) [AlgebraicGroup K] :
    Variety.Point K →* Aut K :=
  MulAut.conj

/-- `Inn(K)`, the image of the canonical inner-conjugation map. -/
public def Inn (K : Variety k) [AlgebraicGroup K] : Subgroup (Aut K) :=
  (innerConjugationMap K).range

end

section

variable {k : Type u} [Field k]

/-- If an abstract automorphism commutes with conjugation by `t`, then its
displacement `t⁻¹ * σ t` is central. -/
private lemma central_delta_mem_of_commutes_inner
    {K : Variety k} [AlgebraicGroup K]
    (σ : Aut K) (t : Variety.Point K)
    (hcomm : σ * innerConjugationMap K t =
      innerConjugationMap K t * σ) :
    t⁻¹ * σ t ∈ Subgroup.center (Variety.Point K) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := σ.surjective y
  have h := DFunLike.congr_fun hcomm x
  simp only [MulAut.mul_apply, innerConjugationMap, MulAut.conj_apply,
    map_mul, map_inv] at h
  calc
    σ x * (t⁻¹ * σ t) = t⁻¹ * (t * σ x * t⁻¹) * σ t := by group
    _ = t⁻¹ * (σ t * σ x * (σ t)⁻¹) * σ t := by rw [← h]
    _ = (t⁻¹ * σ t) * σ x := by group

end

section

variable {k : Type u} [Field k]

private lemma AlgebraicIso_toMulEquiv_mem_AutZero
    {K : Variety k} [AlgebraicGroup K]
    (e : AlgebraicGroup.Iso K K) :
    e.toMulEquiv ∈ AutZero K := by
  apply Subgroup.mem_carrier.mpr
  exact ⟨e, rfl⟩

end

section

variable {k : Type u} [Field k]

/-- The inverse abstract automorphism induced by an algebraic isomorphism
belongs to `AutZero`. -/
public lemma AlgebraicIso_toMulEquiv_symm_mem_AutZero
    {K : Variety k} [AlgebraicGroup K]
    (e : AlgebraicGroup.Iso K K) :
    e.toMulEquiv.symm ∈ AutZero K :=
  (AutZero K).inv_mem (AlgebraicIso_toMulEquiv_mem_AutZero e)

end

section

variable {k : Type u} [Field k]

/-- The abstract point automorphism of a composite algebraic isomorphism is
pointwise the composite of the induced automorphisms. -/
public lemma AlgebraicIso_comp_toMulEquiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (e d : AlgebraicGroup.Iso K K) (x : Variety.Point K) :
    (e.comp d).toMulEquiv x = e.toMulEquiv (d.toMulEquiv x) := by
  rfl

end

section

variable {k : Type u} [Field k]

/-- The inverse abstract automorphism of a composite algebraic isomorphism is
pointwise the composite of the inverse algebraic morphisms in reverse order. -/
public lemma AlgebraicIso_comp_toMulEquiv_symm_apply
    {K : Variety k} [AlgebraicGroup K]
    (e d : AlgebraicGroup.Iso K K) (x : Variety.Point K) :
    (e.comp d).toMulEquiv.symm x = d.inv.onPoints (e.inv.onPoints x) := by
  rfl

end

section

variable {k : Type u} [Field k]

/-- Composite algebraic isomorphisms induce products in `AutZero`. -/
public lemma AlgebraicIso_comp_toMulEquiv_mem_AutZero
    {K : Variety k} [AlgebraicGroup K]
    (e d : AlgebraicGroup.Iso K K) :
    (e.comp d).toMulEquiv ∈ AutZero K := by
  have hcomp : (e.comp d).toMulEquiv = e.toMulEquiv * d.toMulEquiv := by
    ext x
    rfl
  rw [hcomp]
  exact (AutZero K).mul_mem
    (AlgebraicIso_toMulEquiv_mem_AutZero e)
    (AlgebraicIso_toMulEquiv_mem_AutZero d)

end

section

variable {k : Type u} [Field k]

/-- A direct realization by the hom of an algebraic isomorphism transports to
a symmetric realization by its inverse algebraic morphism. -/
public lemma IsAlgebraicRealization_of_realization_of_iso
    {K : Variety k} [AlgebraicGroup K]
    {σ : Aut K} (e : AlgebraicGroup.Iso K K)
    (hσ : IsAlgebraicRealization σ e.hom) :
    IsAlgebraicRealization σ.symm e.inv := by
  intro x
  apply e.toMulEquiv.injective
  change e.hom.onPoints (σ.symm x) = e.hom.onPoints (e.inv.onPoints x)
  calc
    e.hom.onPoints (σ.symm x) = σ (σ.symm x) := by rw [hσ]
    _ = x := by simp
    _ = e.hom.onPoints (e.inv.onPoints x) := (e.inv_hom_id x).symm

end

section

variable {k : Type u} [Field k]

/-- A symmetric realization by the hom of an algebraic isomorphism transports
to a direct realization by its algebraic inverse. -/
public lemma IsAlgebraicRealization_of_symm_realization_of_iso
    {K : Variety k} [AlgebraicGroup K]
    {τ : Aut K} {g : AlgebraicEndomorphism K}
    (hτ : IsAlgebraicRealization τ.symm g)
    (e : AlgebraicGroup.Iso K K) (he : e.hom = g) :
    IsAlgebraicRealization τ e.inv := by
  intro x
  apply e.toMulEquiv.injective
  change e.hom.onPoints (τ x) = e.hom.onPoints (e.inv.onPoints x)
  calc
    e.hom.onPoints (τ x) = g.onPoints (τ x) := by rw [he]
    _ = x := by simpa using (hτ (τ x)).symm
    _ = e.hom.onPoints (e.inv.onPoints x) := (e.inv_hom_id x).symm

end

section

variable {k : Type u} [Field k]

/-- Inner conjugations induced by two points of a maximal torus commute. -/
private lemma innerConjugationMap_commute_of_mem_maximalTorus
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hT : IsMaximalTorus T) {s t : Variety.Point K}
    (hs : s ∈ T) (ht : t ∈ T) :
    innerConjugationMap K s * innerConjugationMap K t =
      innerConjugationMap K t * innerConjugationMap K s := by
  have hscentral := maximalTorus_le_centralizer hT hs
  change s ∈ Subgroup.centralizer (T.toSubgroup : Set (Variety.Point K)) at hscentral
  rw [Subgroup.mem_centralizer_iff] at hscentral
  have hst : s * t = t * s := (hscentral t ht).symm
  simpa only [map_mul] using congrArg (innerConjugationMap K) hst

end

/-! GLS3, Chapter 1, Proposition 1.15.3. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem existsUnique_algebraicAutomorphism_realizing_surjective_endomorphism
    {K : Variety k} [AlgebraicGroup K] (σ : AlgebraicEndomorphism K)
    (hK : IsSemisimpleAlgebraicGroup K)
    (hσ : Function.Surjective σ.onPoints) :
    ∃! a : Aut K, IsAlgebraicRealization a σ := by
  have hσinjective := surjectiveSemisimpleEndomorphism_injective σ hK hσ
  let a : Aut K := MulEquiv.ofBijective σ.onPoints ⟨hσinjective, hσ⟩
  refine ⟨a, ?_, ?_⟩
  · intro x
    rfl
  · intro b hb
    ext x
    exact hb x

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An algebraically realized automorphism of a simple algebraic group that
centralizes the inner action of a maximal torus fixes that torus pointwise. -/
private lemma fixes_maximalTorus_of_realization_of_commutes_inner
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hK : IsSimpleAlgebraicGroup K) (hT : IsMaximalTorus T)
    (σ : Aut K) (f : AlgebraicEndomorphism K)
    (hf : IsAlgebraicRealization σ f)
    (hcomm : ∀ t, t ∈ T → σ * innerConjugationMap K t =
      innerConjugationMap K t * σ) :
    ∀ t, t ∈ T → σ t = t := by
  let δ : Variety.Morphism T.carrierVariety K :=
    (AlgebraicGroup.mulMorphism K).comp
      (((AlgebraicGroup.invMorphism K).comp T.inclusion.toVariety).pair
        (f.toVariety.comp T.inclusion.toVariety))
  have hδ_apply (x : Variety.Point T.carrierVariety) :
      δ.toFun x = (T.inclusion.onPoints x)⁻¹ *
        f.onPoints (T.inclusion.onPoints x) := by
    simp [δ, AlgebraicGroup.mulMorphism, AlgebraicGroup.invMorphism,
      Variety.Morphism.comp, Variety.Morphism.pair,
      AlgebraicGroup.Morphism.onPoints]
  let : Finite (Subgroup.center (Variety.Point K)) := simple_center_finite hK
  have hδfinite : (Set.range δ.toFun).Finite := by
    apply Set.Finite.subset
      (Set.toFinite (Subgroup.center (Variety.Point K) : Set (Variety.Point K)))
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hxT : T.inclusion.onPoints x ∈ T := (T.pointEquiv x).property
    have hcenter := central_delta_mem_of_commutes_inner σ
      (T.inclusion.onPoints x) (hcomm _ hxT)
    rw [hδ_apply, ← hf]
    exact hcenter
  have hδsub := connected_finite_morphism_range_subsingleton δ
    (IsSubtorus.isConnected hT.1) hδfinite
  intro t ht
  let x : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  have hδ := hδsub ⟨x, rfl⟩ ⟨1, rfl⟩
  have hxinclusion : T.inclusion.onPoints x = t := by
    change (T.pointEquiv x).val = t
    simp [x]
  have hdelta : t⁻¹ * f.onPoints t = 1 := by
    rw [hδ_apply, hδ_apply, hxinclusion] at hδ
    simpa using hδ
  rw [← hf] at hdelta
  exact (inv_mul_eq_one.mp hdelta).symm

end

section

variable {k : Type u} [Field k]

/-- Every inner conjugation induced by a point of a maximal torus lies in the
right-hand side set of Theorem 1.15.8. -/
public lemma maximalTorus_innerConjugations_mem_autOneCentralizer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hT : IsMaximalTorus T) :
    innerConjugationMap K '' (T : Set (Variety.Point K)) ⊆
      {σ | σ ∈ AutOneSet K ∧ ∀ t, t ∈ T →
        σ * innerConjugationMap K t = innerConjugationMap K t * σ} := by
  rintro σ ⟨t, ht, rfl⟩
  constructor
  · let f : AlgebraicEndomorphism K :=
      { toVariety := AlgebraicGroup.conjugationByMorphism K t
        map_one := by
          rw [AlgebraicGroup.conjugationByMorphism_apply]
          group
        map_mul := by
          intro x y
          rw [AlgebraicGroup.conjugationByMorphism_apply,
            AlgebraicGroup.conjugationByMorphism_apply,
            AlgebraicGroup.conjugationByMorphism_apply]
          group }
    refine Or.inl ⟨f, ?_⟩
    intro x
    simp only [innerConjugationMap, MulAut.conj_apply]
    simpa [f, AlgebraicGroup.Morphism.onPoints] using
      (AlgebraicGroup.conjugationByMorphism_apply K t x).symm
  · intro s hs
    exact innerConjugationMap_commute_of_mem_maximalTorus hT ht hs

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every element of `AutOneSet` that centralizes the inner action of a
maximal torus fixes that torus pointwise.  The inverse-realization branch is
reduced to the direct branch by taking the inverse automorphism. -/
public theorem fixes_maximalTorus_of_mem_autOneSet_of_commutes_inner
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hK : IsSimpleAlgebraicGroup K) (hT : IsMaximalTorus T)
    (σ : Aut K) (hσ : σ ∈ AutOneSet K)
    (hcomm : ∀ t, t ∈ T → σ * innerConjugationMap K t =
      innerConjugationMap K t * σ) :
    ∀ t, t ∈ T → σ t = t := by
  rcases hσ with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact fixes_maximalTorus_of_realization_of_commutes_inner
      hK hT σ f hf hcomm
  · have hinvcomm : ∀ t, t ∈ T → σ⁻¹ * innerConjugationMap K t =
        innerConjugationMap K t * σ⁻¹ := by
      intro t ht
      exact (show Commute σ (innerConjugationMap K t) from hcomm t ht).inv_left.eq
    have hfixinv := fixes_maximalTorus_of_realization_of_commutes_inner
      hK hT σ⁻¹ f hf hinvcomm
    intro t ht
    have h := congrArg σ (hfixinv t ht)
    simpa using h.symm

end

end Theory.AlgebraicGroup
