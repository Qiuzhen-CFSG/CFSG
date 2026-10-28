module
public import Theory.Representation.SL2.NaturalImageDegree

/-!
# The literal natural component image and its centralizer

A natural constituent detects the marked component quotient. When the quotient
kernel fixes the whole ambient module, its marking is an isomorphism on the
component image. Compatibility with ambient conjugation then identifies the
kernel of the induced SL₂ automorphism action with the literal centralizer of
that image. No irreducibility, multiplicity bound or ambient two-group quotient
is assumed.

Source application: Aschbacher--Smith D.3.9(2) and D.3.21(3),
printed pp.200--201 and205--206.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- Identify both the actual component image and the kernel of its marked
quotient action, using the same natural constituent and quotient map. -/
theorem natural_image_component_and_centralizer
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (hk : q.ker ≤ ((actionHom ρ).comp K.subtype).ker) :
    Nonempty (((actionHom ρ).comp K.subtype).range ≃* SL(2,F)) ∧
      (naturalImageQuotientAction ρ K q hq α hα I E hE).ker =
        centralizer (((actionHom ρ).comp K.subtype).range : Set (actionImage ρ)) := by
  let f0 := (actionHom ρ).comp K.subtype
  let B := f0.range
  have hB : B = K.map (actionHom ρ) := by
    change ((actionHom ρ).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let : B.Normal := hB ▸ Subgroup.Normal.map inferInstance (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  let f : K →* B := f0.rangeRestrict
  have hf : Function.Surjective f := f0.rangeRestrict_surjective
  have hker : f.ker ≤ q.ker := by
    intro k hh
    apply natural_constituent_detects_component_kernel ρ K q I E hE
    exact congrArg (fun b : B => (b : actionImage ρ)) hh
  let qb : B →* SL(2,F) := f.liftOfSurjective hf ⟨q,hker⟩
  have hqb (k : K) : qb (f k) = q k := f.liftOfRightInverse_comp_apply _ _ _ k
  have hsurj : Function.Surjective qb := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact ⟨f k,hqb k⟩
  have hinj : Function.Injective qb := by
    apply (injective_iff_map_eq_one qb).mpr
    intro b hb
    obtain ⟨k,rfl⟩ := hf b
    apply Subtype.ext
    exact hk (show q k = 1 from (hqb k).symm.trans hb)
  let αb := naturalImageQuotientAction ρ K q hq α hα I E hE
  have hconj (a : actionImage ρ) (b : B) :
      qb (MulAut.conjNormal a b) = αb a (qb b) := by
    obtain ⟨g,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective a
    obtain ⟨k,rfl⟩ := hf b
    have hc : MulAut.conjNormal (actionHom ρ g) (f k) = f (MulAut.conjNormal g k) := by
      apply Subtype.ext
      change actionHom ρ g * actionHom ρ (k : G) * (actionHom ρ g)⁻¹ =
        actionHom ρ (g * (k : G) * g⁻¹)
      simp only [map_mul,map_inv]
    change qb (MulAut.conjNormal (actionHom ρ g) (f k)) = αb (actionHom ρ g) (qb (f k))
    rw [hc,hqb,hqb]
    exact (hα g k).trans (congrArg (fun z : MulAut (SL(2,F)) => z (q k))
      (naturalImageQuotientAction_apply ρ K q hq α hα I E hE g).symm)
  refine ⟨⟨MulEquiv.ofBijective qb ⟨hinj,hsurj⟩⟩,?_⟩
  ext a
  change αb a = 1 ↔ a ∈ centralizer (B : Set (actionImage ρ))
  constructor
  · intro ha
    rw [mem_centralizer_iff]
    intro b hb
    have he : MulAut.conjNormal a (⟨b,hb⟩ : B) = ⟨b,hb⟩ := by
      apply hinj
      rw [hconj,ha]
      rfl
    have he' := congrArg (fun b : B => (b : actionImage ρ)) he
    change a * b * a⁻¹ = b at he'
    have hh := congrArg (fun z => z * a) he'
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
  · intro ha
    apply DFunLike.ext
    intro y
    obtain ⟨b,rfl⟩ := hsurj y
    change αb a (qb b) = qb b
    rw [←hconj]
    apply congrArg qb
    apply Subtype.ext
    change a * (b : actionImage ρ) * a⁻¹ = b
    rw [←mem_centralizer_iff.mp ha b b.property,mul_inv_cancel_right]
end Representation.SL2AutomorphismNatural
