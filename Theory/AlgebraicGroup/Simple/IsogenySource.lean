module

public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Simple.Basic

/-!
Simplicity of a semisimple source of an isogeny onto a simple algebraic group.

This is the invariance implicit in the GLS3 definitions of simple algebraic
groups and isogenies (Definition 1.7.1 and Definition 1.10.2). Surjectivity
transfers a trivial derived subgroup to the target. For a proper closed normal
source subgroup, its closed image is normal in the simple target. A proper
image is zero-dimensional, and the kernel-image dimension formula applies
because the restricted kernel lies in the finite isogeny kernel. If the image
is the whole target, the restriction is another isogeny; equality of source
and subgroup dimensions then contradicts connectedness and properness.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma dimension_eq_of_isogeny
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hf : IsIsogeny f) :
    Variety.dimension G = Variety.dimension H := by
  have hkernelPoints :
      Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety) := by
    apply (Equiv.finite_iff f.kernelClosedSubgroup.pointEquiv).mpr
    change Finite f.kernel
    exact hf.2
  have hkernelDimension :
      Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points f.kernelClosedSubgroup.carrierVariety).2
      hkernelPoints
  have himageDimension :
      Variety.dimension f.imageClosedSubgroup.carrierVariety =
        Variety.dimension H := by
    apply (closedSubgroup_dimension_eq_iff_contains_identityComponent
      H f.imageClosedSubgroup).2
    intro y _
    change y ∈ f.image
    exact hf.1 y
  have hdimension := morphism_dimension_eq_kernel_add_image f
  simpa only [hkernelDimension, himageDimension, zero_add] using hdimension

/-- A semisimple source of an isogeny onto a simple algebraic group is simple. -/
public theorem simple_source_of_isogeny
    {U K : Variety k} [AlgebraicGroup U] [AlgebraicGroup K]
    (phi : AlgebraicGroup.Morphism U K)
    (hU : IsSemisimpleAlgebraicGroup U)
    (hK : IsSimpleAlgebraicGroup K)
    (hphi : IsIsogeny phi) :
    IsSimpleAlgebraicGroup U := by
  refine ⟨hU.1, ?_, ?_⟩
  · change commutator (Variety.Point U) ≠ ⊥
    intro hderived
    apply hK.2.1
    change commutator (Variety.Point K) = ⊥
    calc
      commutator (Variety.Point K) =
          (commutator (Variety.Point U)).map phi.onPoints := by
        symm
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hphi.1,
          commutator_def]
      _ = ⊥ := by rw [hderived, Subgroup.map_bot phi.onPoints]
  · intro N hNnormal hNproper
    let q := phi.comp N.inclusion
    let Q := q.imageClosedSubgroup
    have hQmap : Q.toSubgroup = N.toSubgroup.map phi.onPoints := by
      ext y
      constructor
      · intro hy
        change y ∈ q.image at hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨N.inclusion.onPoints x, (N.pointEquiv x).property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        change phi.onPoints x ∈ q.image
        let xN : Variety.Point N.carrierVariety :=
          N.pointEquiv.symm ⟨x, hx⟩
        refine ⟨xN, ?_⟩
        change phi.onPoints (N.inclusion.onPoints xN) = phi.onPoints x
        apply congrArg phi.onPoints
        change (N.pointEquiv xN).val = x
        simp [xN]
    have hQnormal : Q.toSubgroup.Normal := by
      rw [hQmap]
      exact Subgroup.Normal.map hNnormal phi.onPoints hphi.1
    let embed : q.kernel → phi.kernel := fun z =>
      ⟨N.inclusion.onPoints z.1, by
        change phi.onPoints (N.inclusion.onPoints z.1) = 1
        exact MonoidHom.mem_ker.mp z.2⟩
    have hembed : Function.Injective embed := by
      intro x y hxy
      apply Subtype.ext
      apply N.inclusion_injective
      exact congrArg (fun z : phi.kernel => z.1) hxy
    let _ : Finite phi.kernel := hphi.2
    have hqfinite : Finite q.kernel := Finite.of_injective embed hembed
    have hqkernelPoints :
        Finite (Variety.Point q.kernelClosedSubgroup.carrierVariety) := by
      apply (Equiv.finite_iff q.kernelClosedSubgroup.pointEquiv).mpr
      change Finite q.kernel
      exact hqfinite
    have hqkernelDimension :
        Variety.dimension q.kernelClosedSubgroup.carrierVariety = 0 :=
      (dimension_zero_iff_finite_points q.kernelClosedSubgroup.carrierVariety).2
        hqkernelPoints
    by_cases hQproper : Q.toSubgroup ≠ ⊤
    · have hQdimension : Variety.dimension Q.carrierVariety = 0 :=
        hK.2.2 Q hQnormal hQproper
      have hdimension := morphism_dimension_eq_kernel_add_image q
      simpa only [hqkernelDimension, hQdimension, zero_add] using hdimension
    · have hQtop : Q.toSubgroup = ⊤ := not_ne_iff.mp hQproper
      have hqsurjective : Function.Surjective q.onPoints := by
        intro y
        have hy : y ∈ Q.toSubgroup := by rw [hQtop]; trivial
        change y ∈ q.image at hy
        exact hy
      have hNdimension : Variety.dimension N.carrierVariety =
          Variety.dimension U :=
        (dimension_eq_of_isogeny q ⟨hqsurjective, hqfinite⟩).trans
          (dimension_eq_of_isogeny phi hphi).symm
      have hcontains :=
        (closedSubgroup_dimension_eq_iff_contains_identityComponent U N).1
          hNdimension
      have hidentity : AlgebraicGroup.identityComponent U = Set.univ :=
        (identityComponent_eq_univ_iff_isConnected U).2 hU.1
      have hNtop : N.toSubgroup = ⊤ := by
        apply le_antisymm le_top
        intro x _
        apply hcontains
        rw [hidentity]
        trivial
      exact False.elim (hNproper hNtop)

end Theory.AlgebraicGroup
