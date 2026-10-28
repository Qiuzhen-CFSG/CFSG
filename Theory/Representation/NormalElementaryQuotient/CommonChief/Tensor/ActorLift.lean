module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.OtherFactor
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoJoin

/-!
# Lifting a natural tensor actor to the original simple factor

The natural constituent realizes every actor element by an element of K
on the same chief section. A faithful restriction to K forces the section
kernel to centralize K. Triviality of this centralizer in KR therefore
identifies the elements themselves, so A lies in K in the original group.

Source: Aschbacher--Smith 13.1.9, printed p.871. This lifts the section
marking without assuming that the whole moved module has already split.
-/

public noncomputable section
open Subgroup
open Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {d : c.NaturalTensor hc}

theorem Data.NaturalTensor.OtherNatural.actor_le
    [K.Normal] [IsSimpleGroup K] (n : d.OtherNatural)
    (R : Subgroup Q) (hAR : A ≤ R)
    (hcent : (K ⊔ R) ⊓ centralizer (K : Set Q) = ⊥) : A ≤ K := by
  let F := actorGroup S K A
  let σ := sectionRepresentation (ρ.comp F.subtype) c.lower c.upper
  have hK : K ≤ F := le_sup_left.trans le_sup_right
  have hA : A ≤ F := le_sup_right.trans le_sup_right
  have hf := simple_normal_inclusion_actor_faithful K F (K ⊔ R)
    hK σ c.second_moves hcent
  intro a ha
  obtain ⟨k,he⟩ := n.realizes_section ⟨a,mem_sup_right ha⟩
  let aF : F := ⟨a,hA ha⟩
  let kF : F := ⟨k,hK k.property⟩
  have he' : σ aF = σ kF := he
  have hh := (MonoidHom.eq_iff σ).mp he'
  have hm : kF⁻¹ * aF ∈ (K ⊔ R).subgroupOf F :=
    mul_mem (inv_mem (mem_sup_left k.property)) (mem_sup_right (hAR ha))
  have hz := hf (kF⁻¹ * aF) hm (fun v => LinearMap.congr_fun hh v)
  have hek : a = k := (congrArg Subtype.val (inv_mul_eq_one.mp hz)).symm
  exact hek.symm ▸ k.property
end Representation.CommonChief
