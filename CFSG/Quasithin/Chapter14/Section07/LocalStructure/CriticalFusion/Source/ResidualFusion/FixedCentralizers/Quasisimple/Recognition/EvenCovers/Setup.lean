module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.Setup
public import Theory.GroupAction.PerfectCentralQuotientSylow

/-!
# The original action in the exceptional two-cover branch

Relative normality restricts the supplied Sylow of G_u to a Sylow of J.
Its ambient image is exactly L_u ∩ C_T(u), and conjugation by z fixes it
pointwise. The same action is a nonidentity involution because z has order
two and L_u escapes H = C_G(z).

The fixed subgroup cannot be a two-group: its ambient image contains the
original nonsolvable C-component K. We reuse the literal inclusion and
fixed-subgroup comparison from the sibling Sporadic.Setup; neither sporadic
recognition nor any model-centralizer premise is used.

Case retains the original source hypotheses and the center and inner-action
clauses of 1.1.5(3)(b). The two quotient models are supplied separately.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed p.1071 (PDF p.1088); 1.1.5(3)(b), pp.501–503.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
  (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
  (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
    ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹)

include ha

theorem fixedComponentAction_sq : α ^ 2 = 1 := by
  have hz : d.z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one d.z
    rwa [d.fixedElement_order ⟨d.z, d.U₀_le_U d.z_mem_U₀⟩ d.z_ne_one] at h
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((α (α x) : d.fixedCentralizer u) : G) = (x : G)
  rw [ha, ha]
  calc
    _ = d.z ^ 2 * (x : G) * (d.z ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = (x : G) := by rw [hz]; simp

theorem fixedComponentAction_ne_one (hLu : Lu ≤ d.fixedCentralizer u)
    (hout : ¬ Lu ≤ F.H) : α ≠ 1 := by
  intro he
  apply hout
  intro x hx
  rw [d.centralizer_eq, mem_centralizer_singleton_iff]
  let y : Lu.subgroupOf (d.fixedCentralizer u) := ⟨⟨x, hLu hx⟩, hx⟩
  have hy := ha y
  rw [he] at hy
  exact (mul_inv_eq_iff_eq_mul.mp hy.symm).symm

theorem fixedComponentAction_exists_sylow
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal) :
    ∃ P : Sylow 2 (Lu.subgroupOf (d.fixedCentralizer u)),
      (P : Subgroup (Lu.subgroupOf (d.fixedCentralizer u))).map
        (d.fixedComponentInclusion u Lu) = Lu ⊓ d.fixedSylow u ∧
      ∀ x ∈ P, α x = x := by
  let := hn
  obtain ⟨S, hS⟩ := hsyl
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal
    (Lu.subgroupOf (d.fixedCentralizer u))
  have hm : (P : Subgroup (Lu.subgroupOf (d.fixedCentralizer u))).map
      (d.fixedComponentInclusion u Lu) = Lu ⊓ d.fixedSylow u := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rw [← hS]
      exact mem_map_of_mem _ (show y.val ∈ (S : Subgroup (d.fixedCentralizer u)) by
        change y ∈ (P : Subgroup _) at hy
        rw [hP] at hy
        exact hy)
    · rintro ⟨hxLu, hxS⟩
      rw [← hS] at hxS
      obtain ⟨y, hy, rfl⟩ := hxS
      refine ⟨⟨y, hxLu⟩, ?_, rfl⟩
      change (⟨y, hxLu⟩ : Lu.subgroupOf (d.fixedCentralizer u)) ∈ (P : Subgroup _)
      rw [hP]
      exact hy
  refine ⟨P, hm, ?_⟩
  intro x hx
  have hxT : (x : G) ∈ (T : Subgroup G) :=
    (show (x : G) ∈ Lu ⊓ d.fixedSylow u by
      rw [← hm]; exact mem_map_of_mem _ hx).2.1
  have hc := mem_centralizer_singleton_iff.mp
    (d.centralizer_eq ▸ (show (x : G) ∈ F.H from F.invariant 1 hxT))
  apply Subtype.ext
  apply Subtype.ext
  rw [ha, ← hc, mul_inv_cancel_right]

end Data

namespace EvenCoverSieve

structure Case (d : Data T L V F W) (u : F.U) (Lu : Subgroup G)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) : Prop where
  member : (u : G) ∈ d.U₀
  nontrivial : (u : G) ≠ 1
  fixed : d.FixedModuloPoint u
  normalizer_eq : normalizer (K F : Set G) = F.H
  maximal : IsMaximalTwoLocal F.H
  sylow : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)
  le_centralizer : Lu ≤ d.fixedCentralizer u
  component : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent
  normal : (Lu.subgroupOf (d.fixedCentralizer u)).Normal
  contains : K F < Lu
  escapes : ¬ Lu ≤ F.H
  quasisimple : IsQuasisimple Lu
  generation : F.U = ⁅F.U, K F⁆
  conjugation : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
    ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹
  center_nontrivial : center (Lu.subgroupOf (d.fixedCentralizer u)) ≠ ⊥
  center_eq : center (Lu.subgroupOf (d.fixedCentralizer u)) =
    pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))
  inner : α ∈ (MulAut.conj (G := Lu.subgroupOf (d.fixedCentralizer u))).range

theorem Case.fixed_not_isTwoGroup {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} (c : Case d u Lu α) :
    ¬ IsPGroup 2 α.fixedSubgroup := by
  intro hp
  have hK : IsPGroup 2 (K F) := (hp.map (d.fixedComponentInclusion u Lu)).to_le (by
    rw [d.fixedComponent_fixedSubgroup_image u c.le_centralizer α c.conjugation,
      ← d.centralizer_eq]
    exact le_inf c.contains.le (K_le_H F))
  have hpK := hK.of_equiv (subgroupOfEquivOfLe (K_le_H F)).symm
  let := hpK.isNilpotent
  exact d.component.not_isSolvable inferInstance

end EvenCoverSieve
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
