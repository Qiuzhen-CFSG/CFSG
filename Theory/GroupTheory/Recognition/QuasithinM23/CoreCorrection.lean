module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.Group

/-!
# Correcting automorphisms that fix the abelian core

Let U be a finite abelian self-centralizing normal subgroup. A fixed-point-free
actor c makes u ↦ [u,c] bijective on U, so any automorphism fixing U can be
adjusted by a unique core conjugation to fix c. If U⟨c⟩ is normal, this adjusted
automorphism fixes a normal subgroup with trivial centralizer and is identity.

This proves the core-fixing part of the local marking correction in
Aschbacher--Smith 5.2.20(5), printed pp.656--657. Its concrete application is
the original sixteen-group inside the four-pair stabilizer of M23.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23

/-- Fixing a self-centralizing abelian core is inner when a fixed-point-free
element generates a normal overgroup with that core. -/
theorem exists_core_conjugator
    {G : Type*} [Group G] (U : Subgroup G) [U.Normal] [Finite U]
    (hcomm : ∀ u v : U, u * v = v * u)
    (hself : centralizer (U : Set G) ≤ U)
    (c : G) (hfixed : ∀ u : U, Commute (u : G) c → u = 1)
    (hnormal : (U ⊔ zpowers c).Normal)
    (α : MulAut G) (hα : ∀ u : U, α u = u) :
    ∃ u : U, α = MulAut.conj (u : G) := by
  have displacement (β : MulAut G) (hβ : ∀ u : U, β u = u) (g : G) :
      β g * g⁻¹ ∈ U := by
    apply hself
    apply mem_centralizer_iff.mpr
    intro v hv
    have hin : g⁻¹ * v * g ∈ U := by
      simpa only [inv_inv] using (inferInstance : U.Normal).conj_mem v hv g⁻¹
    have hh := hβ ⟨_,hin⟩
    change β (g⁻¹ * v * g) = g⁻¹ * v * g at hh
    rw [map_mul,map_mul,map_inv,hβ ⟨v,hv⟩] at hh
    have hh' := congrArg (fun z => β g * z * g⁻¹) hh
    group at hh'
    simpa only [mul_assoc,zpow_neg_one] using hh'
  let f : U → U := fun u => u * (MulAut.conjNormal c u)⁻¹
  have hf : Function.Injective f := by
    intro u v huv
    have hh : (u : G) * c * (u : G)⁻¹ * c⁻¹ =
        (v : G) * c * (v : G)⁻¹ * c⁻¹ := by
      have hh := congrArg Subtype.val huv
      change (u : G) * (c * u * c⁻¹)⁻¹ = (v : G) * (c * v * c⁻¹)⁻¹ at hh
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
    have hc : Commute ((v⁻¹*u : U) : G) c := by
      change (v : G)⁻¹ * u * c = c * ((v : G)⁻¹ * u)
      have h := congrArg (fun z => (v : G)⁻¹ * z * c * u) hh
      group at h
      simpa only [mul_assoc,zpow_neg_one] using h
    have h := hfixed (v⁻¹*u) hc
    exact (inv_mul_eq_one.mp h).symm
  obtain ⟨u,hu⟩ := (Finite.surjective_of_injective hf) ⟨_,displacement α hα c⟩
  have huc : α c = (u : G) * c * (u : G)⁻¹ := by
    have hh := congrArg Subtype.val hu
    change (u : G) * (c * u * c⁻¹)⁻¹ = α c * c⁻¹ at hh
    have hh' := congrArg (fun z => z*c) hh
    group at hh'
    simpa only [zpow_neg_one] using hh'.symm
  let β : MulAut G := MulAut.conj (u : G)⁻¹ * α
  have hβ (v : U) : β v = v := by
    change (u : G)⁻¹ * α v * ((u : G)⁻¹)⁻¹ = v
    rw [hα]
    have hh := congrArg Subtype.val (hcomm u v)
    change (u : G) * v = (v : G) * u at hh
    simp only [inv_inv]
    rw [mul_assoc,←hh,inv_mul_cancel_left]
  have hβc : β c = c := by
    change (u : G)⁻¹ * α c * ((u : G)⁻¹)⁻¹ = c
    rw [huc]
    group
  let R := U ⊔ zpowers c
  have hR : ∀ r ∈ R, β r = r := by
    have hh : R ≤ β.toMonoidHom.eqLocus (MonoidHom.id G) :=
      sup_le (fun v hv => hβ ⟨v,hv⟩) (zpowers_le.mpr hβc)
    exact hh
  have hβall (g : G) : β g = g := by
    have hcentral : β g * g⁻¹ ∈ centralizer (R : Set G) := by
      apply mem_centralizer_iff.mpr
      intro r hr
      have hin : g⁻¹*r*g ∈ R := by
        simpa only [inv_inv] using hnormal.conj_mem r hr g⁻¹
      have hh := hR _ hin
      rw [map_mul,map_mul,map_inv,hR r hr] at hh
      have hh' := congrArg (fun z => β g*z*g⁻¹) hh
      group at hh'
      simpa only [mul_assoc,zpow_neg_one] using hh'
    have hc : Commute (β g*g⁻¹) c :=
      ((mem_centralizer_iff.mp hcentral) c (mem_sup_right (mem_zpowers c))).symm
    have hh := congrArg Subtype.val (hfixed ⟨_,displacement β hβ g⟩ hc)
    exact mul_inv_eq_one.mp hh
  refine ⟨u,?_⟩
  ext g
  have hh := hβall g
  change (u : G)⁻¹ * α g * ((u : G)⁻¹)⁻¹ = g at hh
  change α g = (u : G)*g*(u : G)⁻¹
  have hh' := congrArg (fun z => (u : G)*z*(u : G)⁻¹) hh
  group at hh'
  simpa only [zpow_neg_one] using hh'

end Theory.GroupTheory.QuasithinM23
