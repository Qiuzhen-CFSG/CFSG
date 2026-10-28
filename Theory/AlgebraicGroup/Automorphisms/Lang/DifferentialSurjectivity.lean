module

public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFiberDominance
public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Product
public import Theory.AlgebraicGroup.Borel.Defs

/-!
# Differential of the Lang--Borel factor map

For a regular morphism fixing the identity, this module defines its pullback
on identity-point derivations and proves functoriality under composition.  It
then constructs the regular map
`(x,b) ↦ x * b * σ(x)⁻¹` on `K × B` and identifies its restriction along the
first-factor inclusion with the Lang morphism.  Consequently, surjectivity of
the Lang differential implies surjectivity of the differential of the
Lang--Borel map.  The remaining implication from finite fixed points to Lang
differential surjectivity is intentionally left as a separate Steinberg
fixed-locus theorem.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup

namespace Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Pullback of identity-point derivations along a regular map fixing the identity. -/
@[expose]
public noncomputable def identityPointDerivationMorphismLinearMap
    {H K : Variety k}
    [AlgebraicGroup H] [AlgebraicGroup K]
    (f : Variety.Morphism H K) (hf : f.toFun 1 = 1) :
    IdentityPointDerivation H →ₗ[k] IdentityPointDerivation K where
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
      rw [hf]
    }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] public theorem identityPointDerivationMorphismLinearMap_apply
    {H K : Variety k}
    [AlgebraicGroup H] [AlgebraicGroup K]
    (f : Variety.Morphism H K) (hf : f.toFun 1 = 1)
    (D : IdentityPointDerivation H)
    (a : Variety.PolynomialFunction K) :
    identityPointDerivationMorphismLinearMap f hf D a =
      D (f.pullbackAlgHom a) := rfl

public theorem identityPointDerivationMorphismLinearMap_comp
    {H K L : Variety k}
    [AlgebraicGroup H] [AlgebraicGroup K] [AlgebraicGroup L]
    (f : Variety.Morphism H K) (g : Variety.Morphism K L)
    (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) :
    identityPointDerivationMorphismLinearMap (g.comp f)
        (by simp [Variety.Morphism.comp, hf, hg]) =
      (identityPointDerivationMorphismLinearMap g hg).comp
        (identityPointDerivationMorphismLinearMap f hf) := by
  ext D a
  rfl

/-- The regular Lang--Borel factor map on the product `K × B`. -/
public noncomputable def twistedBorelMorphism
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    Variety.Morphism (Variety.prod K B.carrierVariety) K := by
  letI := B.carrierAlgebraicGroup
  let x : Variety.Morphism (Variety.prod K B.carrierVariety) K :=
    Variety.Morphism.fst K B.carrierVariety
  let b : Variety.Morphism (Variety.prod K B.carrierVariety) K :=
    B.inclusion.toVariety.comp (Variety.Morphism.snd K B.carrierVariety)
  let sxinv : Variety.Morphism (Variety.prod K B.carrierVariety) K :=
    (AlgebraicGroup.invMorphism K).comp (σ.toVariety.comp x)
  let xb : Variety.Morphism (Variety.prod K B.carrierVariety) K :=
    (AlgebraicGroup.mulMorphism K).comp (x.pair b)
  exact (AlgebraicGroup.mulMorphism K).comp (xb.pair sxinv)

public theorem twistedBorelMorphism_apply
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K)
    (x : Variety.Point K) (b : Variety.Point B.carrierVariety) :
    (twistedBorelMorphism σ B).toFun
        ((Variety.prodPointEquiv K B.carrierVariety).symm (x, b)) =
      x * B.inclusion.onPoints b * (σ.onPoints x)⁻¹ := by
  apply Variety.Point.ext
  funext i
  rfl

public theorem twistedBorelMorphism_identity
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
    letI : AlgebraicGroup (Variety.prod K B.carrierVariety) :=
      AlgebraicGroup.prod K B.carrierVariety
    (twistedBorelMorphism σ B).toFun 1 = 1 := by
  let _ := B.carrierAlgebraicGroup
  let _ : AlgebraicGroup (Variety.prod K B.carrierVariety) :=
    AlgebraicGroup.prod K B.carrierVariety
  rw [show (1 : Variety.Point (Variety.prod K B.carrierVariety)) =
      (Variety.prodPointEquiv K B.carrierVariety).symm (1, 1) by rfl]
  rw [twistedBorelMorphism_apply]
  simp

public theorem twistedBorelMorphism_comp_inl_eq_langMorphism
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
    letI : AlgebraicGroup (Variety.prod K B.carrierVariety) :=
      AlgebraicGroup.prod K B.carrierVariety
    (twistedBorelMorphism σ B).comp
        (AlgebraicGroup.Morphism.inl K B.carrierVariety).toVariety =
      langMorphism σ := by
  apply Variety.Morphism.ext
  funext x
  change (twistedBorelMorphism σ B).toFun
      ((Variety.prodPointEquiv K B.carrierVariety).symm (x, 1)) =
    (langMorphism σ).toFun x
  rw [twistedBorelMorphism_apply]
  rw [langMorphism_apply]
  simp

public theorem langMorphism_identity
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) :
    (langMorphism σ).toFun 1 = 1 := by
  rw [langMorphism_apply]
  simp

/-- Surjectivity of the Lang differential transfers to the Lang--Borel map.

The hypothesis is explicit because finite fixed points alone give no
differential statement without the separate Steinberg fixed-locus argument.
-/
public theorem twistedBorelMorphism_identity_differential_surjective
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K)
    (hLang : Function.Surjective
      (identityPointDerivationMorphismLinearMap (langMorphism σ)
        (langMorphism_identity σ))) :
    letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
    letI : AlgebraicGroup (Variety.prod K B.carrierVariety) :=
      AlgebraicGroup.prod K B.carrierVariety
    Function.Surjective
      (identityPointDerivationMorphismLinearMap
        (twistedBorelMorphism σ B) (twistedBorelMorphism_identity σ B)) := by
  let _ := B.carrierAlgebraicGroup
  let _ : AlgebraicGroup (Variety.prod K B.carrierVariety) :=
    AlgebraicGroup.prod K B.carrierVariety
  let i := AlgebraicGroup.Morphism.inl K B.carrierVariety
  let hi : i.toVariety.toFun 1 = 1 := i.map_one
  have hcomp := identityPointDerivationMorphismLinearMap_comp
    i.toVariety (twistedBorelMorphism σ B) hi
    (twistedBorelMorphism_identity σ B)
  have heq : (twistedBorelMorphism σ B).comp i.toVariety = langMorphism σ :=
    twistedBorelMorphism_comp_inl_eq_langMorphism σ B
  intro D
  obtain ⟨E, hE⟩ := hLang D
  refine ⟨identityTangentMorphismLinearMap i E, ?_⟩
  have hcomp' := congrArg (fun q => q E) hcomp
  have hiDeriv :
      identityPointDerivationMorphismLinearMap i.toVariety hi =
        identityTangentMorphismLinearMap i := by
    ext D a
    rfl
  have hcompPoint :
      ((twistedBorelMorphism σ B).comp i.toVariety).toFun 1 = 1 := by
    rw [heq]
    exact langMorphism_identity σ
  have hcomp'' :
      identityPointDerivationMorphismLinearMap
          (twistedBorelMorphism σ B) (twistedBorelMorphism_identity σ B)
          (identityTangentMorphismLinearMap i E) =
        identityPointDerivationMorphismLinearMap
          (langMorphism σ) (langMorphism_identity σ) E := by
    calc
      identityPointDerivationMorphismLinearMap
          (twistedBorelMorphism σ B) (twistedBorelMorphism_identity σ B)
          (identityTangentMorphismLinearMap i E) =
          identityPointDerivationMorphismLinearMap
            ((twistedBorelMorphism σ B).comp i.toVariety) hcompPoint E := by
              rw [hiDeriv] at hcomp'
              simpa only [LinearMap.comp_apply] using hcomp'.symm
      _ = identityPointDerivationMorphismLinearMap
            (langMorphism σ) (langMorphism_identity σ) E := by
              ext a
              change E (((twistedBorelMorphism σ B).comp i.toVariety).pullbackAlgHom a) =
                E ((langMorphism σ).pullbackAlgHom a)
              rw [heq]
  exact hcomp''.trans hE

end Bor1

end Theory.AlgebraicGroup
