module

public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.CoreProduct

/-!
# Group commutators in the source second Steinberg preimage

Equivariance identifies [R₂,S] with linear displacements, so it lies in
the literal preimage S₂. The original six-space coordinates also give
[Q,Q]≤U. These are the two inputs used with T=R₂Q to place Q₀ inside S₂.

Source: Aschbacher–Smith, J.4.3(2), printed p.441.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- Actual group commutators map to their defining Steinberg displacements. -/
theorem Plane.commutator_R₂_S_le_S₂ : ⁅p.R₂,d.toTypeRuSetup.S⁆ ≤ p.S₂ := by
  apply Subgroup.commutator_le.mpr
  intro a ha s hs
  let l : d.L := ⟨a,d.T_le_L (p.R₂_le_T ha)⟩
  let x : d.toTypeRuSetup.S := ⟨s,hs⟩
  let y : d.toTypeRuSetup.S := ⟨a*s*a⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) s).mp hs⟩
  have hc : (↑(y*x⁻¹) : G) = ⁅a,s⁆ := rfl
  rw [← hc]
  apply (p.mem_S₂ (y*x⁻¹)).mpr
  rw [p.steinbergCommutator_eq,map_mul,map_inv]
  change (d.ru1.steinberg.coordinates y).toAdd +
    -(d.ru1.steinberg.coordinates x).toAdd ∈
      subspaceCommutator (BinaryLinearThree.S.comp d.ru1.quotientMap) ⊤
        (p.R₂.subgroupOf d.L)
  rw [d.ru1.steinberg.equivariant l x]
  have hm : (BinaryLinearThree.S.comp d.ru1.quotientMap) l
      (d.ru1.steinberg.coordinates x).toAdd - (d.ru1.steinberg.coordinates x).toAdd ∈
      subspaceCommutator (BinaryLinearThree.S.comp d.ru1.quotientMap) ⊤
        (p.R₂.subgroupOf d.L) :=
    Submodule.subset_span ⟨l,ha,(d.ru1.steinberg.coordinates x).toAdd,
      Submodule.mem_top,rfl⟩
  exact (sub_eq_add_neg
    ((BinaryLinearThree.S.comp d.ru1.quotientMap) l (d.ru1.steinberg.coordinates x).toAdd)
    (d.ru1.steinberg.coordinates x).toAdd) ▸ hm

/-- The actual Q/U section is abelian, so all Q commutators lie in U. -/
theorem commutator_Q_Q_le_U : ⁅d.toTypeRuSetup.Q,d.toTypeRuSetup.Q⁆ ≤ d.toTypeRuSetup.U := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  let a : d.toTypeRuSetup.Q := ⟨x,hx⟩
  let b : d.toTypeRuSetup.Q := ⟨y,hy⟩
  apply (d.ru2.six.coordinates_eq_one_iff ⁅a,b⁆).mp
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end CFSG.Quasithin.ChapterJ.RuSubgroup
