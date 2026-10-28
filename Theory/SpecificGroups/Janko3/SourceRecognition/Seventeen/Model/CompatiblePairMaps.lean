module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairAutomorphismExtension

/-!
# Pointwise simultaneous markings across the full pair intersection

Once two local model maps identify their full common subgroup setwise,
the extension theorem for the sixteen-field pair adjusts the first map
to any prescribed identification of the two model pairs. The adjusted
maps then agree pointwise on every original intersection element.
-/

public noncomputable section
open Subgroup
open Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

/-- Correct the sixteen-field marking to any prescribed full-pair marking
of the other local group, preserving the original common subgroup. -/
theorem compatible_pair_maps
    {G K : Type*} [Group G] [Group K] (A B : Subgroup G) (R : Subgroup K)
    (eA : A ≃* Model) (eB : B ≃* K)
    (hA : ((A ⊓ B).subgroupOf A).map eA.toMonoidHom = pair)
    (hB : ((A ⊓ B).subgroupOf B).map eB.toMonoidHom = R)
    (ε : pair ≃* R) :
    ∃ f : A ≃* Model,
      ((A ⊓ B).subgroupOf A).map f.toMonoidHom = pair ∧
      ∀ x : (A ⊓ B : Subgroup G), ∃ z : pair,
        f ⟨x,x.property.1⟩ = (z : Model) ∧ eB ⟨x,x.property.2⟩ = (ε z : K) := by
  let a : (A ⊓ B : Subgroup G) ≃* pair :=
    (subgroupOfEquivOfLe inf_le_left).symm.trans
      ((eA.subgroupMap ((A ⊓ B).subgroupOf A)).trans (MulEquiv.subgroupCongr hA))
  let b : (A ⊓ B : Subgroup G) ≃* R :=
    (subgroupOfEquivOfLe inf_le_right).symm.trans
      ((eB.subgroupMap ((A ⊓ B).subgroupOf B)).trans (MulEquiv.subgroupCongr hB))
  let φ : MulAut pair := a.symm.trans (b.trans ε.symm)
  obtain ⟨Φ,hΦ⟩ := pair_automorphism_extends φ
  let f := eA.trans Φ
  have hpair : pair.map Φ.toMonoidHom = pair := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hΦ ⟨x,hx⟩).symm ▸ (φ ⟨x,hx⟩).property
    · intro x hx
      obtain ⟨z,hz⟩ := φ.surjective ⟨x,hx⟩
      refine ⟨z,z.property,?_⟩
      exact (hΦ z).trans (congrArg Subtype.val hz)
  refine ⟨f,?_,?_⟩
  · change ((A ⊓ B).subgroupOf A).map (Φ.toMonoidHom.comp eA.toMonoidHom) = _
    rw [←map_map,hA,hpair]
  · intro x
    refine ⟨φ (a x),?_,?_⟩
    · exact hΦ (a x)
    · have he : ε (φ (a x)) = b x := by
        change ε (ε.symm (b (a.symm (a x)))) = b x
        rw [a.symm_apply_apply,ε.apply_symm_apply]
      exact (congrArg Subtype.val he).symm

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
