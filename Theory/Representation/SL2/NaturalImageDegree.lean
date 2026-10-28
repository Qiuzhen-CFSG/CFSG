module
public import Theory.Representation.SL2.NaturalDegreeBound

/-!
# Natural multiplicity bounds on the faithful ambient image

A natural constituent detects the kernel of the marked component quotient.
Its conjugates then show that the ambient representation kernel also acts
trivially on that quotient. Thus the compatible automorphism action descends
to the faithful ambient image, with the original component marking intact.
The faithful-actor degree bound can consequently be applied to an elementary
actor of this image, without lifting it to an elementary ambient subgroup.

Source: Aschbacher--Smith D.3.9(1) and the passage to M_L⁺ in D.3.21(3),
printed pp.199--200 and 205--206.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The marked natural constituent detects the component quotient modulo the ambient action kernel. -/
theorem natural_constituent_detects_component_kernel
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (q : K →* SL(2,F))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v)) :
    ((actionHom ρ).comp K.subtype).ker ≤ q.ker := by
  intro k hk
  apply (SL2NaturalOffenders.natural_injective (F := F))
  apply LinearMap.ext
  intro v
  rw [map_one,Module.End.one_apply]
  apply E.injective
  change E ((q k).val.mulVec v) = E v
  rw [hE]
  apply Subtype.ext
  exact (actionHom_eq_one_iff ρ (k : G)).mp hk (E v)

/-- The ambient action kernel centralizes the same marked component quotient. -/
theorem natural_constituent_detects_automorphism_kernel
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v)) :
    (actionHom ρ).ker ≤ α.ker := by
  intro a ha
  have hk := natural_constituent_detects_component_kernel ρ K q I E hE
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
@[expose] def naturalImageQuotientAction
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v)) :
    actionImage ρ →* MulAut (SL(2,F)) :=
  (actionHom ρ).liftOfSurjective ρ.asGroupHom.rangeRestrict_surjective
    ⟨α,natural_constituent_detects_automorphism_kernel ρ K q hq α hα I E hE⟩

/-- The descended quotient action agrees with the original compatible automorphisms. -/
theorem naturalImageQuotientAction_apply
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v)) (g : G) :
    naturalImageQuotientAction ρ K q hq α hα I E hE (actionHom ρ g) = α g :=
  (actionHom ρ).liftOfRightInverse_comp_apply _ _ _ g

variable [Finite F] [Finite G] [Finite V]

/-- The two-copy bound uses the literal faithful image actor and its unchanged module. -/
theorem degree_le_two_of_faithful_image_actor
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup (actionImage ρ)) (hA : IsElementaryTwo A)
    (hf : Function.Injective ((naturalImageQuotientAction ρ K q hq α hα I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation ρ) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) (Fin 2 → F) := by
  let σ := imageRepresentation ρ
  let f0 := (actionHom ρ).comp K.subtype
  let B := f0.range
  have hB : B = K.map (actionHom ρ) := by
    change ((actionHom ρ).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let : B.Normal := hB ▸ Subgroup.Normal.map inferInstance (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  let f : K →* B := f0.rangeRestrict
  have hf0 : Function.Surjective f := f0.rangeRestrict_surjective
  have hk : f.ker ≤ q.ker := by
    intro k hk
    apply natural_constituent_detects_component_kernel ρ K q I E hE
    exact congrArg (fun b : B => (b : actionImage ρ)) hk
  let qb : B →* SL(2,F) := f.liftOfSurjective hf0 ⟨q,hk⟩
  have hqb (k : K) : qb (f k) = q k := f.liftOfRightInverse_comp_apply _ _ _ k
  have hqb_surj : Function.Surjective qb := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact ⟨f k,hqb k⟩
  let αb := naturalImageQuotientAction ρ K q hq α hα I E hE
  have hαb (a : actionImage ρ) (b : B) :
      qb (MulAut.conjNormal a b) = αb a (qb b) := by
    obtain ⟨g,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective a
    obtain ⟨k,rfl⟩ := hf0 b
    have hc : MulAut.conjNormal (actionHom ρ g) (f k) = f (MulAut.conjNormal g k) := by
      apply Subtype.ext
      change actionHom ρ g * actionHom ρ (k : G) * (actionHom ρ g)⁻¹ =
        actionHom ρ (g * (k : G) * g⁻¹)
      simp only [map_mul,map_inv]
    change qb (MulAut.conjNormal (actionHom ρ g) (f k)) = αb (actionHom ρ g) (qb (f k))
    rw [hc,hqb,hqb]
    exact (hα g k).trans (congrArg (fun z : MulAut (SL(2,F)) => z (q k))
      (naturalImageQuotientAction_apply ρ K q hq α hα I E hE g).symm)
  let J : Subrepresentation (σ.comp B.subtype) := {
    toSubmodule := I.toSubmodule
    apply_mem_toSubmodule b v hv := by
      obtain ⟨k,rfl⟩ := hf0 b
      exact I.apply_mem_toSubmodule k hv }
  have hJ : J.toRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff f hf0 J.toRepresentation).mp hI
  let E' : (Fin 2 → F) ≃ₗ[ZMod 2] J.toSubmodule := E
  have hE' (b : B) v : E' ((qb b).val.mulVec v) = J.toRepresentation b (E' v) := by
    obtain ⟨k,rfl⟩ := hf0 b
    rw [hqb]
    exact hE k v
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp (inferInstance : ρ.IsIrreducible)
  exact degree_le_two_of_faithful_actor σ B qb hqb_surj αb hαb J hJ E' hE' hF A hA hf hb

end Representation.SL2AutomorphismNatural
