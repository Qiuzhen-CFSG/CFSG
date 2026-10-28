module
public import Theory.Representation.SL2.HermitianHomogeneous
public import Theory.Representation.OrthogonalFourMinusRankOne.NormalizerRank
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# Marked Hermitian quotient actions on the faithful image

A Hermitian constituent detects the marked component quotient, since its
model action is faithful. Compatibility with conjugation then shows that
the ambient representation kernel centralizes that quotient. Its original
automorphism action therefore descends to the literal action image, allowing
elementary image actors without assuming an elementary lift.

Source: Aschbacher--Smith D.3.9 and D.3.21, pp.199--207.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2Hermitian
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.RankOne
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The marked Hermitian constituent detects the component quotient modulo the ambient action kernel. -/
theorem hermitian_constituent_detects_component_kernel
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (q : K →* SL(2,Field s))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v)) :
    ((actionHom ρ).comp K.subtype).ker ≤ q.ker := by
  intro k hk
  apply (hermitian_injective s)
  apply LinearMap.ext
  intro v
  rw [map_one,Module.End.one_apply]
  apply E.injective
  change E (SL2.BinarySmall.hermitian s (q k) v) = E v
  rw [hE]
  apply Subtype.ext
  exact (actionHom_eq_one_iff ρ (k : G)).mp hk (E v)

/-- The ambient action kernel centralizes the same marked component quotient. -/
theorem hermitian_constituent_detects_automorphism_kernel
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,Field s)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,Field s)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v)) :
    (actionHom ρ).ker ≤ α.ker := by
  intro a ha
  have hk := hermitian_constituent_detects_component_kernel s ρ K q I E hE
  have hc (k : K) : q (MulAut.conjNormal a k) = q k := by
    have hmem : (MulAut.conjNormal a k) * k⁻¹ ∈ ((actionHom ρ).comp K.subtype).ker := by
      change actionHom ρ (a * (k : G) * a⁻¹ * (k : G)⁻¹) = 1
      simp only [map_mul,map_inv,show actionHom ρ a = 1 from ha,inv_one,one_mul,mul_one,mul_inv_cancel]
    have hh : q ((MulAut.conjNormal a k) * k⁻¹) = 1 := hk hmem
    simpa only [map_mul,map_inv,mul_inv_eq_one] using hh
  apply DFunLike.ext
  intro g
  obtain ⟨k,rfl⟩ := hq g
  exact (hα a k).symm.trans (hc k)

/-- The marked component automorphism action descends to the literal ambient action image. -/
@[expose] def hermitianImageQuotientAction
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,Field s)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,Field s)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v)) :
    actionImage ρ →* MulAut (SL(2,Field s)) :=
  (actionHom ρ).liftOfSurjective ρ.asGroupHom.rangeRestrict_surjective
    ⟨α,hermitian_constituent_detects_automorphism_kernel s ρ K q hq α hα I E hE⟩

/-- The descended quotient action agrees with the original compatible automorphisms. -/
theorem hermitianImageQuotientAction_apply
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,Field s)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,Field s)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v)) (g : G) :
    hermitianImageQuotientAction s ρ K q hq α hα I E hE (actionHom ρ g) = α g :=
  (actionHom ρ).liftOfRightInverse_comp_apply _ _ _ g

end Representation.SL2Hermitian
