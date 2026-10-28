module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.EndpointAdjustment

/-!
# Endpoint alignment with prescribed fixed actors

An ambient adjustment has one pair of quadratic and principal parameters.
Consequently endpoint alignment and fixing any prescribed actors must hold
for the same parameters. Actors may lie outside the endpoint.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Subgroup

/-- The exact simultaneous criterion for aligning an endpoint and fixing
prescribed actors in the original extension. The actor set can in particular
be a finite set of named source lifts. -/
theorem original_endpoint_alignment_fixing_iff {D H : Type*} [Group D] [Group H]
    (q : D →* A6) (hq : Function.Surjective q)
    (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (ι τ : H →* D) (hmark : ∀ h, q (τ h) = q (ι h))
    (actors : Set D) :
    (∃ α : MulAut D,
      (∀ g, q (α g) = q g) ∧
      (∀ a : q.ker, α a = (a : D)) ∧
      (∀ h, α (ι h) = τ h) ∧
      (∀ P : Subgroup D, q.ker ≤ P → P.map α.toMonoidHom = P) ∧
      (∀ a ∈ actors, α a = a)) ↔
    ∃ (b : ZMod 2) (v : NaturalModule),
      (∀ h, (k ⟨τ h * (ι h)⁻¹, by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, hmark, mul_inv_cancel]⟩).toAdd =
        b • quadratic (q (ι h)) + (polarAction (q (ι h)).val v - v)) ∧
      (∀ a ∈ actors,
        b • quadratic (q a) + (polarAction (q a).val v - v) = 0) := by
  constructor
  · rintro ⟨α,hαq,hαk,hα,hpres,hfix⟩
    obtain ⟨b,v,hv⟩ := (original_endpoint_alignment_iff q hq k hk
      (MonoidHom.id D) α.toMonoidHom hαq).mp
        ⟨α,hαq,hαk,fun _ => rfl,hpres⟩
    refine ⟨b,v,fun h => ?_,fun a ha => ?_⟩
    · have he := hv (ι h)
      change (k ⟨α (ι h) * (ι h)⁻¹, _⟩).toAdd = _ at he
      simpa only [hα, MonoidHom.id_apply] using he
    · have he := hv a
      change (k ⟨α a * a⁻¹, _⟩).toAdd = _ at he
      have hz : (⟨1, by simp⟩ : q.ker) = 1 := rfl
      simpa only [hfix a ha, MonoidHom.id_apply,
        mul_inv_cancel, hz, map_one, toAdd_one] using he.symm
  · rintro ⟨b,v,hv,hactors⟩
    let f : A6 → NaturalModule := fun g =>
      b • quadratic g + (polarAction g.val v - v)
    obtain ⟨δ,hδ,hr⟩ := (restriction_extends_iff (MonoidHom.id A6) f).mpr
      ⟨b,v,fun _ => rfl⟩
    obtain ⟨α,hαq,hαk,hα,_,hfix,hpres⟩ :=
      exists_original_cocycle_automorphism q k hk δ hδ
    refine ⟨α,hαq,hαk,fun h => ?_,hpres,fun a ha => ?_⟩
    · have he : δ (q (ι h)) =
          (k ⟨τ h * (ι h)⁻¹, by
            simp only [MonoidHom.mem_ker, map_mul, map_inv, hmark,
              mul_inv_cancel]⟩).toAdd := (hr (q (ι h))).trans (hv h).symm
      rw [hα,he]
      have heq : (k.symm (Multiplicative.ofAdd
          (k ⟨τ h * (ι h)⁻¹, by
            simp only [MonoidHom.mem_ker, map_mul, map_inv, hmark,
              mul_inv_cancel]⟩).toAdd) : D) = τ h * (ι h)⁻¹ :=
        congrArg Subtype.val (k.symm_apply_apply _)
      rw [heq,inv_mul_cancel_right]
    · exact (hfix a).mpr ((hr (q a)).trans (hactors a ha))

end Theory.SpecificGroups.SymmetricSix.PolarAffine
