module
public import Theory.GroupTheory.GeneralizedFitting.SylowLayerNormalizer
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Descent of components through a local normalizer replacement

A perfect subgroup normalizing a quasisimple component and fixing its
Sylow two-subgroup centralizes the component: the actual simple-quotient
Sylow fixer is solvable under two-Schreier, while the action is perfect.

Now let D be a normal component and X contain C_G(D) and a Sylow two-subgroup
of D. If D∩X is solvable, every component of X centralizes that normal
intersection, hence its Sylow subgroup and then D. Restriction to the normal
subgroup C_G(D) promotes it to a component of G. All subgroups retain their
literal embeddings; no component-list equality is assumed.

Source: Aschbacher--Smith 2.5.3(4), printed pp.552--553, the component-removal
step, using the Sylow-fixer form of Schreier proved in GLS II B.5.16.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Perfect Sylow pointwise fixers centralize the normalized component. -/
theorem perfect_centralizes_component_of_fixed_sylow
    (hS : HasTwoSchreier G) {D : Subgroup G} (hD : IsComponent G D)
    (P : Sylow 2 D) (A : Subgroup G) [Group.IsPerfect A]
    (hAN : A ≤ normalizer (D : Set G))
    (hAP : A ≤ centralizer ((P : Subgroup D).map D.subtype : Set G)) :
    A ≤ centralizer (D : Set G) := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : MulDistribMulAction A D := conjMulDistribMulActionOfLeNormalizer A D hAN
  let ρ := MulDistribMulAction.toMulAut A D
  let Q := P.mapSurjective (f := QuotientGroup.mk' (center D)) (QuotientGroup.mk'_surjective _)
  let F := fixingSubgroup (MulAut (D ⧸ center D)) (Q : Set (D ⧸ center D))
  let : Group.IsSolvable F := hS D (D ⧸ center D) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) Q
  let f : A →* F := ((quotientAut (center D)).comp ρ).codRestrict F (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    rintro y ⟨t, ht, rfl⟩
    change quotientAut (center D) (ρ a) (QuotientGroup.mk' (center D) t) = _
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    change (a : G) * (t : G) * (a : G)⁻¹ = t
    rw [← hAP a.property (t : G) (mem_map_of_mem D.subtype ht), mul_inv_cancel_right])
  have hr : solvableResidual A ≤ f.ker := by
    have hh := map_solvableResidual_le f
    rwa [solvableResidual_eq_bot (G := F), map_le_iff_le_comap, MonoidHom.comap_bot] at hh
  rw [solvableResidual_eq_top] at hr
  intro a ha d hd
  have hq : quotientAut (center D) (ρ ⟨a, ha⟩) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp (hr (mem_top _)))
  have hρ : ρ ⟨a, ha⟩ = 1 := MulAut.quotient_center_injective
    (hq.trans (map_one (quotientAut (center D))).symm)
  have hf := congrArg (fun α : MulAut D => (α ⟨d, hd⟩ : G)) hρ
  change a * d * a⁻¹ = d at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf).symm

/-- Components in the replacement are actual components of the original group. -/
theorem component_descends_of_normal_component_solvable_intersection
    (hS : HasTwoSchreier G) {D : Subgroup G} [D.Normal] (hD : IsComponent G D)
    (P : Sylow 2 D) (X : Subgroup G)
    (hCX : centralizer (D : Set G) ≤ X)
    (hPX : (P : Subgroup D).map D.subtype ≤ X)
    (hsolv : Group.IsSolvable (D.subgroupOf X))
    (K : Subgroup X) (hK : IsComponent X K) :
    IsComponent G (K.map X.subtype) ∧ K.map X.subtype ≤ centralizer (D : Set G) := by
  let A := K.map X.subtype
  let C := centralizer (D : Set G)
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect A := Group.IsPerfect.map X.subtype
  let : Group.IsSolvable (D.subgroupOf X) := hsolv
  have hKD := hK.le_centralizer_normal_solvable (D.subgroupOf X)
  have hAP : A ≤ centralizer ((P : Subgroup D).map D.subtype : Set G) := by
    rintro a ⟨k, hk, rfl⟩ p ⟨d, hd, rfl⟩
    exact congrArg Subtype.val
      (hKD hk ⟨d, hPX (mem_map_of_mem D.subtype hd)⟩ d.property)
  have hAC : A ≤ C := perfect_centralizes_component_of_fixed_sylow hS hD P A
    le_normalizer_of_normal hAP
  have hrel : IsComponentIn A X := by
    refine ⟨map_subtype_le _, ?_⟩
    change IsComponent X ((K.map X.subtype).comap X.subtype)
    rwa [comap_map_eq_self_of_injective X.subtype_injective]
  have hCrel := hrel.restrict hAC hCX
  exact ⟨⟨Subgroup.IsSubnormal.trans hAC hCrel.2.1
    (inferInstance : C.Normal).isSubnormal, hCrel.quasisimple⟩, hAC⟩
end Theory.GroupTheory
