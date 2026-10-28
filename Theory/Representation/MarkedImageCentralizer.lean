module
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# Centralizers of a marked component in the faithful action image

A surjective component marking with the same kernel as its representation
identifies the literal component image. A compatible action on that marking
has kernel exactly the centralizer of the component image. Both conclusions
use the same marking, so they can be used together in prime-index arguments.
Source: the first isomorphism theorem and compatibility with conjugation.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {G S V : Type*} [Group G] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The image marking and the centralizer identity retain the same quotient kernel. -/
theorem marked_image_component_and_centralizer
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* S) (hq : Function.Surjective q)
    (αb : actionImage ρ →* MulAut S)
    (hα : ∀ (g : G) (k : K),
      q (MulAut.conjNormal g k) = αb (actionHom ρ g) (q k))
    (hk : ((actionHom ρ).comp K.subtype).ker = q.ker) :
    Nonempty (((actionHom ρ).comp K.subtype).range ≃* S) ∧
      αb.ker = centralizer (((actionHom ρ).comp K.subtype).range : Set (actionImage ρ)) := by
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
    apply hk.le
    exact congrArg (fun b : B => (b : actionImage ρ)) hh
  let qb : B →* S := f.liftOfSurjective hf ⟨q,hker⟩
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
    exact hk.ge (show q k = 1 from (hqb k).symm.trans hb)
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
    exact hα g k

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
end Representation
