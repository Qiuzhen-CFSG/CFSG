module

public import Theory.AlgebraicGroup.Bor1.IdentitySmoothness
public import Theory.AlgebraicGroup.Irreducible.Product
public import Theory.AlgebraicGroup.Product
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Tangent spanning implies density of a subgroup product

For two closed subgroups of a connected affine algebraic group, spanning of
the ambient identity tangent space by the two inclusion differentials implies
Zariski density of their pointwise product.

The regular multiplication map need not be a group homomorphism. We construct
its identity differential as a pointed variety map, and use the two factor
inclusions to prove surjectivity. Smoothness of the source and target groups
then gives smoothness at the identity. A nonempty smooth principal localization
is flat and nonzero; since the connected target has an integral coordinate
ring, this makes pullback injective and hence the image dense.

This is the geometric density step used for Steinberg (6.2)(c),
`refs/KGroup/GLS3/Chapter2St2.tex`. The general criterion is kept in this
extension to avoid changing shared foundations while constructing the Spin
big cell.
-/

open Theory.AlgebraicGroup
universe u
namespace Theory.AlgebraicGroup.Bor1
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

private noncomputable def pointedTangentMap
    (f : Variety.Morphism G Q) (h1 : f.toFun 1 = 1) :
    IdentityPointDerivation G →ₗ[k] IdentityPointDerivation Q where
  toFun D := {
    toLinearMap := D.toLinearMap.comp f.pullbackAlgHom.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' := by
      intro p q
      change D (f.pullbackAlgHom (p * q)) =
        p • D (f.pullbackAlgHom q) + q • D (f.pullbackAlgHom p)
      rw [map_mul, Derivation.leibniz]
      change p (f.toFun 1) * D (f.pullbackAlgHom q) +
          q (f.toFun 1) * D (f.pullbackAlgHom p) =
        p 1 * D (f.pullbackAlgHom q) + q 1 * D (f.pullbackAlgHom p)
      rw [h1] }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private noncomputable def pointedCotangentMap
    (f : Variety.Morphism G Q) (h1 : f.toFun 1 = 1) :
    (Q.pointPrime 1).asIdeal.Cotangent →ₗ[k] (G.pointPrime 1).asIdeal.Cotangent :=
  Ideal.mapCotangent _ _ f.pullbackAlgHom (by
    intro a ha
    change a (f.toFun 1) = 0
    rw [h1]
    exact ha)

omit [IsAlgClosed k] in
private theorem pointedCotangentMap_injective
    (f : Variety.Morphism G Q) (h1 : f.toFun 1 = 1)
    (hd : Function.Surjective (pointedTangentMap f h1)) :
    Function.Injective (pointedCotangentMap f h1) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    apply (Module.forall_dual_apply_eq_zero_iff k z).mp
    intro l
    obtain ⟨D, hD⟩ := hd ((identityPointDerivationEquivCotangentDual Q).symm l)
    have hnat : identityPointDerivationEquivCotangentDual Q
          (pointedTangentMap f h1 D) =
        (identityPointDerivationEquivCotangentDual G D).comp
          (pointedCotangentMap f h1) := by
      ext x
      obtain ⟨a, rfl⟩ := (Q.pointPrime 1).asIdeal.toCotangent_surjective x
      rfl
    rw [hD, LinearEquiv.apply_symm_apply] at hnat
    rw [hnat, LinearMap.comp_apply, hz, map_zero]
  · exact bot_le

set_option linter.style.haveILetI false in
private theorem pointed_isSmoothAt_of_tangent_surjective
    (f : Variety.Morphism G Q) (h1 : f.toFun 1 = 1)
    (hd : Function.Surjective (pointedTangentMap f h1)) :
    letI : Algebra (Variety.PolynomialFunction Q) (Variety.PolynomialFunction G) :=
      f.pullbackAlgHom.toRingHom.toAlgebra
    Algebra.IsSmoothAt (Variety.PolynomialFunction Q) (G.pointPrime 1).asIdeal := by
  let A := Variety.PolynomialFunction Q
  let B := Variety.PolynomialFunction G
  let F := f.pullbackAlgHom
  letI : Algebra A B := F.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r => (F.commutes r).symm
  letI : Algebra.Smooth k A := polynomialFunction_smooth_of_algebraicGroup Q
  letI : Algebra.Smooth k B := polynomialFunction_smooth_of_algebraicGroup G
  let eA : A →ₐ[k] k := polynomialFunctionPointAlgHom Q 1
  let eB : B →ₐ[k] k := polynomialFunctionPointAlgHom G 1
  letI : (RingHom.ker eB).IsMaximal := RingHom.ker_isMaximal_of_surjective eB
    (polynomialFunctionPointAlgHom_surjective G 1)
  have hc : eB.comp (IsScalarTower.toAlgHom k A B) = eA := by
    ext a
    change a (f.toFun 1) = a 1
    rw [h1]
  exact smoothAt_of_augmentedCotangentMap_injective eA eB
    (polynomialFunctionPointAlgHom_surjective Q 1)
    (polynomialFunctionPointAlgHom_surjective G 1) hc
    (pointedCotangentMap_injective f h1 hd)

set_option linter.style.haveILetI false in
private theorem algebraMap_injective_of_smoothAt {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] [IsDomain A]
    (p : Ideal B) [p.IsPrime] [Algebra.IsSmoothAt A p] :
    Function.Injective (algebraMap A B) := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  letI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth A p
  let C := Localization.Away f
  letI : Algebra.Smooth A C := hs
  letI : Nontrivial C :=
    (IsLocalization.toLocalizationMap (Submonoid.powers f) C).nontrivial (by
      rintro ⟨n, hn⟩
      apply hf
      apply (inferInstance : p.IsPrime).mem_of_pow_mem n
      change f ^ n = 0 at hn
      rw [hn]
      exact p.zero_mem)
  have hinj : Function.Injective (algebraMap A C) :=
    FaithfulSMul.algebraMap_injective A C
  intro a b hab
  apply hinj
  rw [IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply A B C, hab]


omit [IsAlgClosed k] in
private theorem dense_range_of_pullback_injective
    {V W : Variety k} (f : Variety.Morphism V W)
    (hf : Function.Injective f.pullbackAlgHom) : Dense (Set.range f.toFun) := by
  rw [dense_iff_closure_eq]
  by_contra hne
  have hproper : closure (Set.range f.toFun) ⊂
      (Set.univ : Set (Variety.Point W)) :=
    ⟨Set.subset_univ _, fun h => hne (Set.eq_univ_of_univ_subset h)⟩
  have hideal : vanishingIdeal (Set.univ : Set (Variety.Point W)) <
      vanishingIdeal (closure (Set.range f.toFun)) :=
    vanishingIdeal_strict_antitone
      (Variety.isClosed_iff_isZariskiClosed.mp isClosed_univ)
      (Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure) hproper
  obtain ⟨p, hpclosure, hpuniv⟩ := SetLike.exists_of_lt hideal
  let q := Variety.PolynomialFunction.ofPolynomial W p
  have hpullzero : f.pullbackAlgHom q = 0 := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (f.toFun x).val p = 0
    exact hpclosure (f.toFun x) (subset_closure ⟨x, rfl⟩)
  have hqzero : q = 0 := hf hpullzero
  apply hpuniv
  intro x _
  exact congrArg (fun r : Variety.PolynomialFunction W => r x) hqzero

set_option linter.style.haveILetI false in
private theorem pointed_dense_of_tangent_surjective
    (f : Variety.Morphism G Q) (h1 : f.toFun 1 = 1)
    (hd : Function.Surjective (pointedTangentMap f h1))
    (hQ : Variety.IsConnected Q) : Dense (Set.range f.toFun) := by
  let A := Variety.PolynomialFunction Q
  let B := Variety.PolynomialFunction G
  letI : Algebra A B := f.pullbackAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r =>
    (f.pullbackAlgHom.commutes r).symm
  letI : Algebra.FiniteType k A := polynomialFunction_finiteType Q
  letI : Algebra.FiniteType k B := polynomialFunction_finiteType G
  letI : IsDomain A := (coordinateRingAlgEquivPolynomialFunction Q).toRingEquiv.isDomain_iff.mp
    (connectedAlgebraicGroup_coordinateRing_domain Q hQ)
  letI : Algebra.IsSmoothAt A (G.pointPrime 1).asIdeal :=
    pointed_isSmoothAt_of_tangent_surjective f h1 hd
  exact dense_range_of_pullback_injective f
    (algebraMap_injective_of_smoothAt (k := k) (G.pointPrime 1).asIdeal)

open scoped Pointwise
local instance subgroupAlgebraicGroup (H : ClosedSubgroup G) :
    AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup

/-- Closed subgroups whose inclusion tangent images span the tangent space
of a connected algebraic group have Zariski-dense pointwise product. No
homomorphism property of the multiplication map is assumed. -/
public theorem closedSubgroup_product_dense_of_tangent_span
    (B C : ClosedSubgroup G) (hG : Variety.IsConnected G)
    (hspan : LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊔
      LinearMap.range (identityTangentMorphismLinearMap C.inclusion) = ⊤) :
    Dense ((B.toSubgroup : Set (Variety.Point G)) *
      (C.toSubgroup : Set (Variety.Point G))) := by
  let : AlgebraicGroup (Variety.prod B.carrierVariety C.carrierVariety) :=
    AlgebraicGroup.prod B.carrierVariety C.carrierVariety
  let left := B.inclusion.comp (Morphism.fst B.carrierVariety C.carrierVariety)
  let right := C.inclusion.comp (Morphism.snd B.carrierVariety C.carrierVariety)
  let pair := Morphism.prod left right
  let m := (AlgebraicGroup.mulMorphism G).comp pair.toVariety
  have h1 : m.toFun 1 = 1 := by
    change left.onPoints 1 * right.onPoints 1 = 1
    rw [map_one, map_one, mul_one]
  let iB := Morphism.inl B.carrierVariety C.carrierVariety
  let iC := Morphism.inr B.carrierVariety C.carrierVariety
  have hB (D : IdentityPointDerivation B.carrierVariety) :
      pointedTangentMap m h1 (identityTangentMorphismLinearMap iB D) =
        identityTangentMorphismLinearMap B.inclusion D := by
    apply Derivation.ext
    intro a
    change D (iB.toVariety.pullbackAlgHom (m.pullbackAlgHom a)) =
      D (B.inclusion.toVariety.pullbackAlgHom a)
    congr 1
    apply Variety.PolynomialFunction.ext
    intro x
    change a (B.inclusion.onPoints x * C.inclusion.onPoints 1) = a (B.inclusion.onPoints x)
    rw [map_one, mul_one]
  have hC (D : IdentityPointDerivation C.carrierVariety) :
      pointedTangentMap m h1 (identityTangentMorphismLinearMap iC D) =
        identityTangentMorphismLinearMap C.inclusion D := by
    apply Derivation.ext
    intro a
    change D (iC.toVariety.pullbackAlgHom (m.pullbackAlgHom a)) =
      D (C.inclusion.toVariety.pullbackAlgHom a)
    congr 1
    apply Variety.PolynomialFunction.ext
    intro x
    change a (B.inclusion.onPoints 1 * C.inclusion.onPoints x) = a (C.inclusion.onPoints x)
    rw [map_one, one_mul]
  have hd : Function.Surjective (pointedTangentMap m h1) := by
    intro v
    have hv : v ∈ LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊔
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
      rw [hspan]
      trivial
    obtain ⟨b, ⟨b', rfl⟩, c, ⟨c', rfl⟩, hbc⟩ := Submodule.mem_sup.mp hv
    refine ⟨identityTangentMorphismLinearMap iB b' +
      identityTangentMorphismLinearMap iC c', ?_⟩
    rw [map_add, hB, hC]
    exact hbc
  apply (pointed_dense_of_tangent_surjective m h1 hd hG).mono
  rintro _ ⟨z, rfl⟩
  exact Set.mem_mul.mpr ⟨left.onPoints z,
    (B.pointEquiv ((Morphism.fst B.carrierVariety C.carrierVariety).onPoints z)).property,
    right.onPoints z,
    (C.pointEquiv ((Morphism.snd B.carrierVariety C.carrierVariety).onPoints z)).property,
    rfl⟩

end Theory.AlgebraicGroup.Bor1
