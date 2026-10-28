module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Preparation
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Component placement and the vanishing centralizer residual in 14.7.67

Every C-component B of J(DR₁) is perfect, so it lies in D: the quotient
DR₁/D is a two-group. Since C_DR₁(E) is a two-group, B acts nontrivially
on the original E. Relative normality of J in DR₁ transports B to a
C-component of DR₁, and subnormal Sylow restriction supplies the actual
Sylow subgroup B ∩ R₁.

The original point has centralizer H. Thus C_B(V₁) lies in D ∩ H ≤ T,
and its two-residual is trivial. The later module calculation must prove
that this SAME residual is nontrivial. Nothing here asserts component
exclusion or solvability before that calculation is discharged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070, PDF p.1087.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)

omit [Finite G] in
/-- A C-component of the literal Thompson subgroup is perfect in ambient coordinates. -/
theorem residual_component_perfect {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) : Group.IsPerfect B := by
  let := hB.2.perfect
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hB.1).toMonoidHom)
    (subgroupOfEquivOfLe hB.1).surjective

/-- The two-group quotient DR₁/D kills the image of every perfect component. -/
theorem residual_component_le_D {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) : B ≤ D F := by
  let Y₁ := Y L F
  let DN := (D F).subgroupOf Y₁
  let : DN.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (D F).le_normalizer residual_R_normalizes_D)
  have hgen : DN ⊔ (F.Ri L 1).subgroupOf Y₁ = ⊤ := by
    apply map_injective Y₁.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D F ≤ Y₁ from le_sup_left),
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ Y₁ from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hquot : IsPGroup 2 (Y₁ ⧸ DN) := isPGroup_quotient_of_sup_eq_top DN _
    (T.isPGroup'.to_le residual_R_le_sylow).comap_subtype hgen
  let := hquot.isNilpotent
  have hBY : B ≤ Y₁ := hB.1.trans J_le_Y
  let := residual_component_perfect hB
  let : Group.IsPerfect (B.subgroupOf Y₁) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hBY).symm.toMonoidHom)
      (subgroupOfEquivOfLe hBY).symm.surjective
  have hBD := le_of_isPerfect_of_solvable_quotient (B.subgroupOf Y₁) DN
  exact fun b hb => hBD (show (⟨b, hBY hb⟩ : Y₁) ∈ B.subgroupOf Y₁ from hb)

include d in
/-- The two-group kernel of the E-action cannot contain a C-component. -/
theorem residual_component_not_centralizes {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    ¬ B ≤ centralizer (E F : Set G) := by
  intro hc
  have hp := (d.residualSpan_centralizer_isPGroup).to_le
    (le_inf (hB.1.trans J_le_Y) hc)
  let := hp.isNilpotent
  exact hB.2.not_isSolvable
    (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hB.1).toMonoidHom) (subgroupOfEquivOfLe hB.1).injective)

include d in
/-- The actual marked point centralizer lies in D ∩ H and hence in T. -/
theorem residual_component_point_centralizer_le_sylow {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ⊓ centralizer (F.Vi 1 : Set G) ≤ (T : Subgroup G) := by
  have he : centralizer (F.Vi 1 : Set G) = F.H := by
    rw [d.point, zpowers_eq_closure, centralizer_closure, d.centralizer_eq]
  rw [he]
  exact (inf_le_inf_right _ (residual_component_le_D hB)).trans d.D_inf_H_le_sylow

include d in
/-- The final contradiction needs nontriviality of this two-residual, not of a two-core. -/
theorem residual_component_point_centralizer_residual_eq_bot {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    pResidual 2 (B ⊓ centralizer (F.Vi 1 : Set G) : Subgroup G) = ⊥ := by
  apply bot_unique
  apply sInf_le
  refine ⟨inferInstance, ?_⟩
  exact (T.isPGroup'.to_le (d.residual_component_point_centralizer_le_sylow hB)).of_surjective
    (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)

omit [Finite G] in
/-- Relative normality of J in Y lifts its components to components of Y. -/
theorem residual_component_in_Y {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ∈ Chapter1.cComponentsIn (Y L F) := by
  let A := J L F
  let Y₁ := Y L F
  have hAY : A ≤ Y₁ := J_le_Y
  have hn : (A.subgroupOf Y₁).Normal := normal_subgroupOf_of_le_normalizer Y_normalizes_J
  have he : (B.subgroupOf A).map (inclusion hAY) = B.subgroupOf Y₁ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hB.1 hx⟩, hx, rfl⟩
  have hc := (hB.2.map_equiv (subgroupOfEquivOfLe hAY).symm).map_subtype hn.isSubnormal
  have hf : (A.subgroupOf Y₁).subtype.comp (subgroupOfEquivOfLe hAY).symm.toMonoidHom =
      inclusion hAY := by ext; rfl
  rw [map_map, hf] at hc
  change ((B.subgroupOf A).map (inclusion hAY)).IsCComponent at hc
  exact ⟨hB.1.trans hAY, he ▸ hc⟩

/-- The supplied R₁ meets the subnormal component in an actual Sylow subgroup. -/
theorem residual_component_sylow {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    ∃ P : Sylow 2 B, (P : Subgroup B) = (F.Ri L 1).subgroupOf B := by
  obtain ⟨S, hS⟩ := hSylow
  have hBY := (residual_component_in_Y hB).1
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal (B.subgroupOf (Y L F))
    (residual_component_in_Y hB).2.subnormal
  let e := subgroupOfEquivOfLe hBY
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hS ▸ mem_map_of_mem (Y L F).subtype ha
  · intro hb
    have hm : (b : G) ∈ (S : Subgroup (Y L F)).map (Y L F).subtype := hS.symm ▸ hb
    obtain ⟨a, ha, hab⟩ := hm
    change (a : G) = (b : G) at hab
    have haB : (a : G) ∈ B := hab.symm ▸ b.property
    exact ⟨⟨a, haB⟩, ha, Subtype.ext hab⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
