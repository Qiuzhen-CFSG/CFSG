module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.ElementaryAbelian.Quotient

/-!
# The marked central four-group of the dihedral base

The two coordinate central involutions give a normal elementary four-group
in the Sylow. Its image is exactly ⟨t,z⟩ and contains every commutator of
the dihedral base. These facts supply the derived and closure fields of the
original marked source configuration.

Source: Aschbacher–Smith 13.9.2 and 13.9.7, printed pp.969–971 (PDF pp.986–988).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup
open scoped commutatorElement
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

def axis (b : Bool) : D8 := if b then DihedralGroup.r 2 else 1

def axisHom : C2×C2→*P where
  toFun a := pair (axis (decide (a.1≠1)),axis (decide (a.2≠1)))
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem axisHom_injective : Function.Injective axisHom := by decide +kernel

def axesInP : Subgroup P := axisHom.range

theorem card_axesInP : Nat.card axesInP=4 := by
  rw [axesInP,←Nat.card_congr (MonoidHom.ofInjective axisHom_injective).toEquiv,Nat.card_eq_fintype_card]
  decide +kernel

private theorem axis_membership : ∀a b : D8, pair (a,b)∈axesInP ↔
    (a=1 ∨ a=DihedralGroup.r 2) ∧ (b=1 ∨ b=DihedralGroup.r 2) := by
  change ∀a b:D8,(∃i:C2×C2,axisHom i=pair (a,b)) ↔ _
  decide +kernel

private theorem axes_span : axesInP=zpowers (pair (DihedralGroup.r 2,1))⊔zpowers centralInP := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    have h : ∀a:C2×C2,axisHom a=1 ∨ axisHom a=pair (DihedralGroup.r 2,1) ∨
        axisHom a=centralInP ∨ axisHom a=pair (DihedralGroup.r 2,1)*centralInP := by decide +kernel
    rcases h a with he|he|he|he
    · rw [he];exact one_mem _
    · rw [he];exact mem_sup_left (mem_zpowers _)
    · rw [he];exact mem_sup_right (mem_zpowers _)
    · rw [he];exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  · apply sup_le <;> apply zpowers_le.mpr
    · exact (axis_membership _ _).mpr ⟨Or.inr rfl,Or.inl rfl⟩
    · exact (axis_membership _ _).mpr ⟨Or.inr rfl,Or.inr rfl⟩

theorem axes_image : axesInP.map sylowEmbedding=zpowers t⊔zpowers z := by
  rw [axes_span,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,sylowEmbedding_axis,sylowEmbedding_centralInP]

instance axesInP_elementary : IsElementaryAbelian 2 axesInP := by
  let : IsElementaryAbelian 2 (C2×C2) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
  exact IsElementaryAbelian.of_surjective axisHom.rangeRestrict axisHom.rangeRestrict_surjective

instance axesInP_normal : axesInP.Normal where
  conj_mem x hx g := by
    obtain ⟨a,rfl⟩ := hx
    have h : ∀g:P,∀a:C2×C2,∃b:C2×C2,g*axisHom a*g⁻¹=axisHom b := by decide +kernel
    obtain ⟨b,hb⟩ := h g a
    exact ⟨b,hb.symm⟩

theorem marked_four_elementary : IsElementaryAbelian 2 (zpowers t⊔zpowers z : Subgroup W) := by
  rw [←axes_image]
  exact IsElementaryAbelian.map _

theorem card_marked_four : Nat.card (zpowers t⊔zpowers z : Subgroup W)=4 := by
  rw [←axes_image,card_map_of_injective sylowEmbedding_injective,card_axesInP]

theorem standardSylow_normalizes_marked_four :
    (standardSylow:Subgroup W)≤normalizer ((zpowers t⊔zpowers z : Subgroup W) : Set W) := by
  have h := axesInP.le_normalizer_map sylowEmbedding
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,←standardSylow_coe,axes_image] using h

private theorem dihedral_commutator : ∀a b:D8,⁅a,b⁆=1 ∨ ⁅a,b⁆=DihedralGroup.r 2 := by decide +kernel

theorem derived_J_le : ⁅J,J⁆≤zpowers t⊔zpowers z := by
  apply commutator_le.mpr
  rintro _ ⟨_,⟨a,rfl⟩,rfl⟩ _ ⟨_,⟨b,rfl⟩,rfl⟩
  rw [←axes_image,←map_commutatorElement]
  apply mem_map_of_mem
  have he : ⁅pair a,pair b⁆=pair (⁅a.1,b.1⁆,⁅a.2,b.2⁆) := by
    rw [←map_commutatorElement]
    rfl
  rw [he]
  exact (axis_membership _ _).mpr ⟨dihedral_commutator _ _,dihedral_commutator _ _⟩
end SymmetricFourWreath
