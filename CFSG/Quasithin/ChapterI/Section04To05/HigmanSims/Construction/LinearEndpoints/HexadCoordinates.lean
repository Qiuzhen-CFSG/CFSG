module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup

/-!
# The retained polar action on the original hexad kernel

The literal even-preimage quotient and original binary coordinates identify
its whole kernel with the four-dimensional polar module, preserving every
conjugation operator. This supplies the actual input to an independent
natural-module extension calculation; no splitting is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

/-- The literal hexad quotient has the original natural polar kernel,
with every quotient value and every conjugation action retained. -/
theorem NaturalEndpointData.hexad_kernel_coordinates (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom=Point) :
    ∃ hDN : d.hexad_overgroup≤normalizer (A:Set G),
      ∃ π : d.hexad_overgroup→*A6, Function.Surjective π ∧
        ∃ hπker : π.ker=A.subgroupOf d.hexad_overgroup,
        (∀ g : d.hexad_overgroup, (π g:S6)=d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ k : π.ker≃*Multiplicative Vec,
          (∀ a : π.ker, (k a).toAdd=d.binary_coordinates
            (Additive.ofMul ⟨((a: d.hexad_overgroup):G),
              by exact (show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup
                from hπker ▸ a.property)⟩)) ∧
          ∀ (g : d.hexad_overgroup) (a : π.ker),
            k (MulAut.conjNormal g a)=Multiplicative.ofAdd
              (Theory.SpecificGroups.SymmetricSix.polarAction (π g).val (k a).toAdd) := by
  obtain ⟨hDN,hAD,_,_,_,π,hπs,hπker,hπmark,_⟩ :=
    d.hexad_overgroup_structure L hPL e hmark
  let b : A≃*Multiplicative Vec := d.binary_coordinates.toAddEquiv.toMultiplicative
  let j : π.ker≃*A := (MulEquiv.subgroupCongr hπker).trans (subgroupOfEquivOfLe hAD)
  let k := j.trans b
  have hj (a : π.ker) : (j a:G)=((a:d.hexad_overgroup):G) := rfl
  have hk (a : π.ker) : (k a).toAdd=d.binary_coordinates (Additive.ofMul (j a)) := rfl
  refine ⟨hDN,π,hπs,hπker,hπmark,k,?_,?_⟩
  · intro a
    rfl
  · intro g a
    apply Multiplicative.toAdd.injective
    rw [hk,hk]
    have hjact : j (MulAut.conjNormal g a)=
        A.normalizerMonoidHom (inclusion hDN g) (j a) := by
      apply Subtype.ext
      rfl
    rw [hjact]
    have hh := d.symplectic_action (inclusion hDN g) (j a)
    have hq : Theory.SpecificGroups.SymmetricSix.polarRepresentation (π g).val=
        d.symplectic_quotient (QuotientGroup.mk (inclusion hDN g)) := by
      rw [←Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply,hπmark]
      exact Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply _
    rw [←hq,Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply] at hh
    exact hh.symm

end CFSG.Quasithin.HigmanSims
