module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Native
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic

/-!
# Source coordinates for the ordinary M₂₂ branch

We keep the quotient of K by its own two-core, its canonical comparison
with K* in H/O₂(H), and the specified M₂₂ equivalence. Centerlessness
identifies the literal O₂,Z(K) with O₂(K). The Sylow arrangement puts the
kernel of the star map inside T, making later lifting of subgroup
containments legitimate. Relative normality of L₁ follows from the
order-three definition of theta.

The standing inputs below are earlier source facts, not a parabolic
placement certificate. Placement of K∩M in the marked native geometry is
not asserted by this module.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956; A.3.17–18,
13.7.3(9), and 13.8.13 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement

variable {G : Type*} [Group G] [Finite G]

/-- The explicitly used standing and earlier group-theoretic inputs.
`solvable_overgroups` is exactly 13.8.13, restricted to G₁. -/
structure Setup (H K L₁ T G₁ M : Subgroup G) where
  mem_Hz : H ∈ Source.Hz L₁ T G₁ M
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  component_normal : (K.subgroupOf H).Normal
  sylow_le_M : T ≤ M
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H) = T.subgroupOf H
  generated : H = K ⊔ L₁ ⊔ T
  seed_le_component : L₁ ≤ K
  theta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  solvable : Group.IsSolvable L₁
  model : (K ⧸ pCore 2 K) ≃* M22
  solvable_overgroups : ∀ X : Subgroup G, X ≤ G₁ → L₁ ⊔ T ≤ X →
    Group.IsSolvable X → X ≤ M

/-- The intrinsic component map, before any subgroup choices or conjugations. -/
noncomputable def componentMap (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22) :
    K →* M22 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

omit [Finite G] in
theorem componentMap_surjective (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22) :
    Function.Surjective (componentMap K e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem componentMap_ker (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22) :
    (componentMap K e).ker = pCore 2 K := by
  ext k
  change e (QuotientGroup.mk' (pCore 2 K) k) = 1 ↔ k ∈ pCore 2 K
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff k

/-- The coordinates on K* are obtained through the canonical component map. -/
noncomputable def starCoordinates (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (e : (K ⧸ pCore 2 K) ≃* M22) :
    Source.starImage H K ≃* M22 :=
  (Components.componentStarEquiv H K hKH hK).symm.trans e

/-- Compatibility retains both quotient maps and their actual representatives. -/
theorem starCoordinates_component (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (e : (K ⧸ pCore 2 K) ≃* M22) (k : K) :
    starCoordinates H K hKH hK e
      (Components.componentStarEquiv H K hKH hK (QuotientGroup.mk' (pCore 2 K) k)) =
      componentMap K e k := by
  simp [starCoordinates, componentMap]

omit [Finite G] in
/-- In this branch the literal central preimage has no extra odd center. -/
theorem centralPreimage_eq_twoCore (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) : centralPreimage (pCore 2 K) = pCore 2 K := by
  apply le_antisymm _ (le_centralPreimage _)
  intro k hk
  apply (QuotientGroup.eq_one_iff k).mp
  apply e.injective
  rw [map_one]
  have hc : e (QuotientGroup.mk' (pCore 2 K) k) ∈ center M22 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (e.map_mul _ _).symm.trans
      ((congrArg e (mem_center_iff.mp hk x)).trans (e.map_mul _ _))
  change e (QuotientGroup.mk' (pCore 2 K) k) = 1
  simpa only [m22_center_eq_bot, mem_bot] using hc

omit [Finite G] in
/-- The ambient version of the literal denominator equality. -/
theorem centralPreimageIn_eq_twoCoreIn (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) :
    (centralPreimage (pCore 2 K)).map K.subtype = K.pCoreIn 2 := by
  rw [centralPreimage_eq_twoCore K e]
  rfl

namespace Setup
omit [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : Setup H K L₁ T G₁ M)
include s

theorem seed_join_sylow_le : L₁ ⊔ T ≤ H := s.mem_Hz.1.2

theorem eq_component_join_sylow : H = K ⊔ T := by
  rw [s.generated, sup_eq_left.mpr s.seed_le_component]

theorem seed_le_overlap : L₁ ≤ K ⊓ M := by
  refine le_inf s.seed_le_component ?_
  rw [s.theta]
  exact ((closure_le _).mpr fun _ hx => hx.1).trans inf_le_right

/-- Normality is in J = K∩M, not in the ambient simple group. -/
theorem seed_normal_in_overlap : (L₁.subgroupOf (K ⊓ M)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [s.theta]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨⟨H.mul_mem (H.mul_mem (s.component_le hg.1) hx.1.1)
    (H.inv_mem (s.component_le hg.1)), M.mul_mem (M.mul_mem hg.2 hx.1.2)
      (M.inv_mem hg.2)⟩, (MulAut.conj g).orderOf_eq x |>.trans hx.2⟩

/-- The actual star kernel lies in the specified source Sylow subgroup. -/
theorem star_kernel_le_sylow :
    (QuotientGroup.mk' (pCore 2 H)).ker ≤ T.subgroupOf H := by
  rw [QuotientGroup.ker_mk', ← s.sylow_eq]
  exact pCore_isPGroup.le_sylow_of_normal s.sylow

/-- Thus any inclusion of images in L₁T lifts through the actual star map. -/
theorem radical_le_seed_join_of_star_image (K₁ : Subgroup G)
    (himage : (((K₁ ⊔ T).subgroupOf H).pCoreIn 2).map
        (QuotientGroup.mk' (pCore 2 H)) ≤ Source.starImage H (L₁ ⊔ T)) :
    ((K₁ ⊔ T).subgroupOf H).pCoreIn 2 ≤ (L₁ ⊔ T).subgroupOf H := by
  apply core_le_of_image_le (QuotientGroup.mk' (pCore 2 H))
    ((L₁ ⊔ T).subgroupOf H) ((K₁ ⊔ T).subgroupOf H)
  · exact s.star_kernel_le_sylow.trans (comap_mono le_sup_right)
  · exact himage

/-- The source quantifier is used only on actual solvable overgroups of L₁T. -/
theorem solvable_overgroup_in_H_le_overlap (X : Subgroup G) (hXH : X ≤ H)
    (hseed : L₁ ⊔ T ≤ X) (hsol : Group.IsSolvable X) : X ≤ H ⊓ M :=
  le_inf hXH (s.solvable_overgroups X (hXH.trans s.mem_Hz.2.1) hseed hsol)

end Setup
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
