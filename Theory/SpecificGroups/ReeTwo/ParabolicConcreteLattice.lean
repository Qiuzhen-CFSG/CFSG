module
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteCore

/-!
# The extra characteristic subgroup in the actual full-Ree core

The characteristic subgroup W = Ω₁(Q) of order 512 is retained: E < W < Q,
W ∩ F = E, and WF = Q. Its derived subgroup is E, self-centralizing in W;
E is also Ω₁(F). These are the intrinsic inputs for excluding the extra
supplement in the repaired ambient argument. The second center of Q is E,
not the larger F. Every identity is transported through the verified root
embedding in the actual full-Ree parabolic.

Source: Aschbacher--Smith 14.2.21, p.989, with the corrections established
from the root relations of Shinoda (1975), pp.81--83.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.ParabolicConcrete
open Centralizer Centralizer.IndexTwo ParabolicMarkedComparison
open Tits.ExceptionalParabolics

/-- The intrinsic first omega subgroup, viewed in the actual parabolic. -/
def reeW : Subgroup FullRee.first := (omega₁ reeQ (p := 2)).map reeQ.subtype

theorem reeCoreMap_derived : (commutator Core).map reeCoreMap = reeE := by
  rw [reeCoreMap, ← Subgroup.map_map]
  exact reeE_eq

theorem reeCoreMap_centralizer :
    (centralizer (commutator Core : Set Core)).map reeCoreMap = reeF := by
  rw [reeCoreMap, ← Subgroup.map_map, ← centralizer_derived_eq_map]
  exact reeF_eq

theorem reeCoreMap_omega : (omega₁ Core (p := 2)).map reeCoreMap = reeW := by
  exact Subgroup.map_omega_eq_of_injective_of_range_eq reeCoreMap reeQ.subtype
    reeCoreMap_injective reeQ.subtype_injective (by rw [reeCoreMap_range, range_subtype]) 2 1

theorem reeW_card : Nat.card reeW = 512 := by
  rw [← reeCoreMap_omega, ← Nat.card_congr
    ((omega₁ Core (p := 2)).equivMapOfInjective reeCoreMap reeCoreMap_injective).toEquiv]
  exact Core.omega_card

theorem reeW_characteristic : reeW.Characteristic := by
  let : (omega₁ reeQ (p := 2)).Characteristic := omega₁_characteristic _
  exact inferInstanceAs (((omega₁ reeQ (p := 2)).map reeQ.subtype).Characteristic)

theorem reeW_inf_F : reeW ⊓ reeF = reeE := by
  rw [← reeCoreMap_omega, ← reeCoreMap_centralizer, ← Subgroup.map_inf _ _ _ reeCoreMap_injective,
    Core.omega_inf_centralizer_derived, reeCoreMap_derived]

theorem reeW_sup_F : reeW ⊔ reeF = reeQ := by
  rw [← reeCoreMap_omega, ← reeCoreMap_centralizer, ← Subgroup.map_sup,
    Core.omega_sup_centralizer_derived, ← MonoidHom.range_eq_map, reeCoreMap_range]

theorem reeE_lt_W : reeE < reeW := by
  apply lt_of_le_of_ne
  · rw [← reeW_inf_F]
    exact inf_le_left
  · intro h
    have hc := reeE_card
    rw [h, reeW_card] at hc
    omega

theorem reeW_lt_Q : reeW < reeQ := by
  apply lt_of_le_of_ne (map_subtype_le _)
  intro h
  change reeW = reeQ at h
  have hc := reeW_card
  rw [h, reeQ_card] at hc
  omega

/-- The extra candidate has the same derived subgroup as the full core. -/
theorem reeW_commutator : ⁅reeW,reeW⁆ = reeE := by
  rw [← reeCoreMap_omega, ← Subgroup.map_commutator, Core.omega_commutator, reeCoreMap_derived]

/-- E is intrinsically characteristic in W, so it is available to the parent's core argument. -/
theorem reeE_characteristic_in_W : (reeE.subgroupOf reeW).Characteristic := by
  have h : commutator reeW = reeE.subgroupOf reeW := by
    apply Subgroup.map_injective reeW.subtype_injective
    rw [map_subtype_commutator, reeW_commutator, map_subgroupOf_eq_of_le reeE_lt_W.le]
  rw [← h]
  infer_instance

/-- The extra candidate is self-centralizing on E inside W. -/
theorem reeW_centralizer_E : centralizer (reeE.subgroupOf reeW : Set reeW) =
    reeE.subgroupOf reeW := by
  ext x
  constructor
  · intro hx
    have hxW : (x : FullRee.first) ∈ (omega₁ Core (p := 2)).map reeCoreMap := by
      simpa only [reeCoreMap_omega] using x.property
    obtain ⟨u,hu,he⟩ := hxW
    have huc : u ∈ centralizer (commutator Core : Set Core) := by
      intro y hy
      have hyE : reeCoreMap y ∈ reeE := reeCoreMap_derived ▸ mem_map_of_mem _ hy
      have h := congrArg Subtype.val (hx ⟨reeCoreMap y,reeE_lt_W.le hyE⟩ hyE)
      change reeCoreMap y * (x : FullRee.first) = (x : FullRee.first) * reeCoreMap y at h
      apply reeCoreMap_injective
      simpa only [map_mul, he] using h
    have huE : u ∈ commutator Core := Core.omega_inf_centralizer_derived ▸ ⟨hu,huc⟩
    change (x : FullRee.first) ∈ reeE
    rw [← he, ← reeCoreMap_derived]
    exact mem_map_of_mem _ huE
  · intro hx y hy
    let := reeE_elementary
    have h := (IsMulCommutative.is_comm (M := reeE)).comm
      (⟨y,hy⟩ : reeE) ⟨x,hx⟩
    apply Subtype.ext
    exact congrArg (fun z : reeE => (z : FullRee.first)) h

/-- The characteristic derived subgroup is also the omega subgroup of F. -/
theorem reeF_omega : (omega₁ reeF (p := 2)).map reeF.subtype = reeE := by
  let C := centralizer (commutator Core : Set Core)
  have h := Subgroup.map_omega_eq_of_injective_of_range_eq
    (reeCoreMap.comp C.subtype) reeF.subtype
    (reeCoreMap_injective.comp C.subtype_injective) reeF.subtype_injective
    (by rw [MonoidHom.range_comp, range_subtype, reeCoreMap_centralizer, range_subtype]) 2 1
  rw [← h, ← Subgroup.map_map, Core.centralizer_omega_map_eq_derived, reeCoreMap_derived]

/-- E is characteristic in the other proper candidate F as well. -/
theorem reeE_characteristic_in_F : (reeE.subgroupOf reeF).Characteristic := by
  have h : omega₁ reeF (p := 2) = reeE.subgroupOf reeF := by
    apply Subgroup.map_injective reeF.subtype_injective
    rw [reeF_omega, map_subgroupOf_eq_of_le (by rw [← reeW_inf_F]; exact inf_le_right)]
  rw [← h]
  exact omega₁_characteristic _

/-- The second center is E in the actual core, and is distinct from F. -/
theorem ree_second_center : (Subgroup.upperCentralSeries reeQ 2).map reeQ.subtype = reeE := by
  have h : (Subgroup.upperCentralSeries Core 2).map reeCoreEquiv.toMonoidHom =
      Subgroup.upperCentralSeries reeQ 2 := by
    rw [← Subgroup.comap_upperCentralSeries reeCoreEquiv 2]
    exact map_comap_eq_self_of_surjective reeCoreEquiv.surjective _
  rw [← h, Core.second_center_eq_derived, Subgroup.map_map]
  exact reeCoreMap_derived

theorem ree_second_center_ne_F : (Subgroup.upperCentralSeries reeQ 2).map reeQ.subtype ≠ reeF := by
  rw [ree_second_center]
  intro h
  have hc := reeE_card
  rw [h, reeF_card] at hc
  omega

/-- The actual embedding of the Tits parabolic identifies its core with W,
not with the larger full-Ree core. -/
theorem tits_core_image_eq_W : titsQ.map FirstQuotient.embedding = reeW := by
  rw [titsQ, ← pCore_map_iso 2 Verified.titsFirstEquiv, Subgroup.map_map]
  have h : FirstQuotient.embedding.comp Verified.titsFirstEquiv.toMonoidHom =
      Verified.firstEquiv.toMonoidHom.comp mixedLocal.subtype :=
    MonoidHom.ext Verified.tits_embedding_commutes
  rw [h, ← Subgroup.map_map, alternative_pCore mixedCharacter (Or.inr rfl),
    map_subgroupOf_eq_of_le (omega_le_kernel mixedCharacter (Or.inr rfl)),
    Centralizer.IndexTwo.omega, Subgroup.map_map]
  exact reeCoreMap_omega

/-- Both derived tails agree under the literal ambient Tits embedding. -/
theorem tits_derived_image : titsE.map FirstQuotient.embedding = reeE := by
  change (⁅titsQ,titsQ⁆ : Subgroup _).map _ = _
  rw [Subgroup.map_commutator, tits_core_image_eq_W, reeW_commutator]

/-- The Tits centralizer maps onto E, a proper subgroup of the full-Ree F. -/
theorem tits_centralizer_image : titsF.map FirstQuotient.embedding = reeE := by
  rw [titsF_eq_E, tits_derived_image]

end ReeTwo.ParabolicConcrete
