module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Reductive.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Jordan.Morphism
public import Theory.AlgebraicGroup.Tori.Semisimple

/-!
# Normalizer invariance under reductive endomorphisms

A surjective endomorphism of a connected reductive algebraic group preserves
exactly the normalizer of every invariant closed unipotent subgroup. No
injectivity on the whole point group is needed; kernels on tori may be nontrivial.

The finite kernel is central, and the center maps onto itself. The induced
surjection on the finite component group of the center is injective, so the
kernel lies in the connected center, which is a torus. Jordan uniqueness then
shows that the endomorphism is injective on unipotent points. This lets us lift
normalizer membership through the surjective point map.

This supplies the normalizer step in the proof of GLS3, Theorem 3.1.3
(`refs/KGroup/GLS3/chapter3.tex`), using the Jordan and isogeny facts in
Proposition 1.2.2 and Proposition 1.10.3, and reductivity as in Theorem 1.7.2.
The Steinberg specialization uses exactly Definition 1.15.1(b), as in §2.1.
-/

universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma normalizerEquivariance_kernel_mem_identityComponent
    {G : Variety k} [AlgebraicGroup G]
    (f : AlgebraicGroup.Morphism G G) (hf : Function.Surjective f.onPoints)
    (x : Variety.Point G) (hx : f.onPoints x = 1) :
    x ∈ AlgebraicGroup.identityComponent G := by
  let N := AlgebraicGroup.identityComponentSubgroup G
  let : N.Normal := by
    simpa [N, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  let : Finite (Variety.Point G ⧸ N) := finite_quotient_identityComponentSubgroup G
  have hN : N ≤ N.comap f.onPoints := by
    intro z hz
    exact f.image_identityComponent_subset ⟨z, hz, rfl⟩
  let q := QuotientGroup.map N N f.onPoints hN
  have hqsurj : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective N N f.onPoints
      ((QuotientGroup.mk'_surjective N).comp hf) hN
  have hqinj : Function.Injective q := (Finite.injective_iff_surjective).mpr hqsurj
  have heq : (QuotientGroup.mk' N) x = 1 := hqinj (by
    change (QuotientGroup.mk' N) (f.onPoints x) = q 1
    rw [hx, map_one, map_one])
  exact (QuotientGroup.eq_one_iff x).mp heq

/-- Every point in the kernel of a surjective reductive endomorphism is
semisimple: it lies in the toral identity component of the center. -/
public theorem surjectiveReductiveEndomorphism_kernel_semisimple
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (f : AlgebraicGroup.Morphism G G) (hf : Function.Surjective f.onPoints)
    (x : Variety.Point G) (hx : x ∈ f.kernel) :
    IsSemisimpleElement G x := by
  have hisog : IsIsogeny f := ⟨hf, surjectiveEndomorphism_kernel_finite f hf⟩
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  have hZ : Z.toSubgroup = Subgroup.center (Variety.Point G) := by
    change Subgroup.centralizer (Set.univ : Set (Variety.Point G)) = _
    exact Subgroup.centralizer_univ
  have hcenter := isogeny_image_center_eq_center_of_connected f hisog hG.1
  have hmem (z : Variety.Point Z.carrierVariety) :
      (f.comp Z.inclusion).onPoints z ∈ Z.toSubgroup := by
    change f.onPoints (Z.inclusion.onPoints z) ∈ Z.toSubgroup
    rw [hZ]
    change f.onPoints (Z.inclusion.onPoints z) ∈
      (Subgroup.center (Variety.Point G) : Set (Variety.Point G))
    rw [← hcenter]
    exact ⟨Z.inclusion.onPoints z, hZ ▸ (Z.pointEquiv z).property, rfl⟩
  let fZ := (f.comp Z.inclusion).codRestrictClosedSubgroup Z hmem
  have hfZ (z : Variety.Point Z.carrierVariety) :
      Z.inclusion.onPoints (fZ.onPoints z) = f.onPoints (Z.inclusion.onPoints z) :=
    AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hfZsurj : Function.Surjective fZ.onPoints := by
    intro z
    have hz : Z.inclusion.onPoints z ∈ f.onPoints ''
        (Subgroup.center (Variety.Point G) : Set (Variety.Point G)) := by
      rw [hcenter]
      exact hZ ▸ (Z.pointEquiv z).property
    obtain ⟨y, hy, hyz⟩ := hz
    let yZ : Variety.Point Z.carrierVariety := Z.pointEquiv.symm ⟨y, hZ.symm ▸ hy⟩
    refine ⟨yZ, Z.inclusion_injective ?_⟩
    rw [hfZ]
    exact hyz
  have hxZ : x ∈ Z.toSubgroup := hZ.symm ▸
    isogeny_kernel_le_center_of_connected f hisog hG.1 x hx
  let xZ : Variety.Point Z.carrierVariety := Z.pointEquiv.symm ⟨x, hxZ⟩
  have hxZker : fZ.onPoints xZ = 1 := by
    apply Z.inclusion_injective
    rw [hfZ, map_one]
    exact hx
  have hxZconn := normalizerEquivariance_kernel_mem_identityComponent fZ hfZsurj xZ hxZker
  have hxT : x ∈ Z.identityComponentAmbient :=
    (Z.mem_identityComponentAmbient_iff x).mpr ⟨xZ, hxZconn, rfl⟩
  let T := Z.identityComponentAmbient
  let xT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hxT⟩
  exact morphism_preserves_semisimpleElement T.inclusion xT
    ((center_identityComponent_isSubtorus_of_reductive hG).all_semisimple xT)

/-- A surjective reductive endomorphism separates unipotent points, even when
its point map is not injective on the ambient group. -/
public theorem surjectiveReductiveEndomorphism_injective_on_unipotent
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (f : AlgebraicGroup.Morphism G G) (hf : Function.Surjective f.onPoints)
    {x y : Variety.Point G} (hx : IsUnipotentElement G x)
    (hy : IsUnipotentElement G y) (hxy : f.onPoints x = f.onPoints y) : x = y := by
  have hker : x * y⁻¹ ∈ f.kernel := by
    change f.onPoints (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hcentral := isogeny_kernel_le_center_of_connected f
    ⟨hf, surjectiveEndomorphism_kernel_finite f hf⟩ hG.1 _ hker
  let d : JordanDecomposition x :=
    { semisimplePart := x * y⁻¹
      unipotentPart := y
      eq_mul := by group
      commute := (Subgroup.mem_center_iff.mp hcentral y).symm
      semisimple := surjectiveReductiveEndomorphism_kernel_semisimple hG f hf _ hker
      unipotent := hy }
  let e : JordanDecomposition x :=
    { semisimplePart := 1
      unipotentPart := x
      eq_mul := (one_mul x).symm
      commute := Commute.one_left x
      semisimple := one_isSemisimpleElement G
      unipotent := hx }
  exact (congrArg JordanDecomposition.unipotentPart (d.unique e)).symm

private lemma normalizerEquivariance_conjugate_unipotent
    {G : Variety k} [AlgebraicGroup G]
    (g x : Variety.Point G) (hx : IsUnipotentElement G x) :
    IsUnipotentElement G (g * x * g⁻¹) := by
  let c : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro a b
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  exact morphism_preserves_unipotentElement c x hx

/-- A surjective reductive endomorphism maps the normalizer of an invariant
closed unipotent subgroup onto itself. -/
public theorem surjectiveReductiveEndomorphism_image_normalizer_eq
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (f : AlgebraicGroup.Morphism G G) (hf : Function.Surjective f.onPoints)
    (X : ClosedSubgroup G) (hXuni : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hX : f.onPoints '' (X : Set (Variety.Point G)) = X) :
    f.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer := by
  have hmap : X.toSubgroup.map f.onPoints = X.toSubgroup := SetLike.coe_injective hX
  have huni (x : Variety.Point G) (hx : x ∈ X) : IsUnipotentElement G x := by
    let xX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨x, hx⟩
    exact morphism_preserves_unipotentElement X.inclusion xX (hXuni xX)
  have hreflect {x : Variety.Point G} (hx : IsUnipotentElement G x)
      (hfx : f.onPoints x ∈ X) : x ∈ X := by
    change f.onPoints x ∈ (X : Set (Variety.Point G)) at hfx
    rw [← hX] at hfx
    obtain ⟨y, hy, hxy⟩ := hfx
    exact (surjectiveReductiveEndomorphism_injective_on_unipotent hG f hf hx
      (huni y hy) hxy.symm) ▸ hy
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hm := Subgroup.le_normalizer_map (H := X.toSubgroup) f.onPoints
      (Subgroup.mem_map_of_mem f.onPoints hx)
    rwa [hmap] at hm
  · intro y hy
    obtain ⟨g, rfl⟩ := hf y
    have hlift (a : Variety.Point G) (ha : f.onPoints a ∈ X.normalizer)
        (x : Variety.Point G) (hx : x ∈ X) : a * x * a⁻¹ ∈ X := by
      apply hreflect (normalizerEquivariance_conjugate_unipotent a x (huni x hx))
      rw [map_mul, map_mul, map_inv]
      apply (Subgroup.mem_normalizer_iff.mp ha (f.onPoints x)).mp
      change f.onPoints x ∈ (X : Set (Variety.Point G))
      rw [← hX]
      exact ⟨x, hx, rfl⟩
    refine ⟨g, ?_, rfl⟩
    change g ∈ Subgroup.normalizer X.toSubgroup
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hlift g hy x
    · intro hx
      have hginv : f.onPoints g⁻¹ ∈ X.normalizer := by
        rw [map_inv]
        exact X.normalizer.inv_mem hy
      have h := hlift g⁻¹ hginv (g * x * g⁻¹) hx
      change x ∈ X
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- Exact normalizer invariance for the general reductive Steinberg case in
GLS3, Theorem 3.1.3. Unipotence is required, but point injectivity is not. -/
public theorem steinbergReductiveEndomorphism_image_normalizer_eq
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (X : ClosedSubgroup G) (hXuni : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    sigma.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer :=
  surjectiveReductiveEndomorphism_image_normalizer_eq hG sigma hsigma.1 X hXuni hX

end Theory.AlgebraicGroup
