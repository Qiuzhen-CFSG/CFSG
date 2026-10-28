module
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.OuterTransport
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
/-!
# Components of an outer G₂ involution centralizer

Every ordinary component of a full finite G₂ model is its actual derived
subgroup. Above field order two this follows from perfectness and simplicity;
at the binary endpoint it uses the proved simplicity of G₂(2)′. Transport
through the actual outer-involution fixed-group equivalence identifies the
literal image of every component and its quotient by its center. The original
action, inner conjugator and half-degree coefficient field are retained.

Source: Aschbacher--Smith 2.5.19, printed pp.562--563, and the field-involution
row 16.1.4(4), p.1171, with the full binary fixed group on p.1191.
No component model or component-center quotient is assumed.
-/
public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.EvenFieldFixedResidual
variable {F : Type*} [Field F] [Finite F]

/-- The derived subgroup of every actual finite G₂ model is simple, including
the proper derived subgroup at field order two. -/
theorem derived_isSimple : IsSimpleGroup (commutator (Model F)) := by
  by_cases hq : 2 < Nat.card F
  · let : Group.IsPerfect (Model F) := isPerfect hq
    rw [Group.IsPerfect.commutator_eq_top]
    let : IsSimpleGroup (Model F) := isSimple hq
    exact (Subgroup.topEquiv : (⊤ : Subgroup (Model F)) ≃* Model F).isSimpleGroup
  · have hcard : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let e := fieldEquiv (binaryFieldEquiv hcard)
    let d : commutator (Model F) ≃* commutator (Model (ZMod 2)) :=
      (e.subgroupMap (commutator (Model F))).trans
        (MulEquiv.subgroupCongr (by
          rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
          rfl))
    let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
    exact d.isSimpleGroup

/-- Every ordinary component of the full G₂ model is its actual derived
subgroup. This retains full versus derived G₂ at the binary endpoint. -/
theorem model_component_eq_commutator (D : Subgroup (Model F))
    (hD : IsComponent (Model F) D) : D = commutator (Model F) := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := hD.2.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hle : D ≤ commutator (Model F) := by
    calc
      D = ⁅D,D⁆ := (commutator_eq_self (H := D)).symm
      _ ≤ ⁅(⊤ : Subgroup (Model F)),⊤⁆ := commutator_mono le_top le_top
  rcases hD.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
    (derived_isSimple (F := F)) with hb | ht
  · have he := congrArg (Subgroup.map (commutator (Model F)).subtype) hb
    have hbot : D = ⊥ := by
      simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using he
    exact ((nontrivial_iff_ne_bot D).mp inferInstance hbot).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

/-- Transport identifies an ordinary component by its literal image in the
specified G₂ model. -/
theorem component_map_eq_commutator {C : Type*} [Group C]
    (e : C ≃* Model F) (D : Subgroup C) (hD : IsComponent C D) :
    D.map e.toMonoidHom = commutator (Model F) :=
  model_component_eq_commutator _ (hD.map_equiv e)

/-- The equivalence of the component with the derived model is the restriction
of the original fixed-group model equivalence. -/
noncomputable def componentEquivCommutator {C : Type*} [Group C]
    (e : C ≃* Model F) (D : Subgroup C) (hD : IsComponent C D) :
    D ≃* commutator (Model F) :=
  (e.subgroupMap D).trans (MulEquiv.subgroupCongr (component_map_eq_commutator e D hD))

@[simp] theorem componentEquivCommutator_apply {C : Type*} [Group C]
    (e : C ≃* Model F) (D : Subgroup C) (hD : IsComponent C D) (d : D) :
    (componentEquivCommutator e D hD d : Model F) = e (d : C) := by
  rfl

/-- Every component in a specified full G₂ carrier has trivial center. -/
theorem component_center_eq_bot {C : Type*} [Group C]
    (e : C ≃* Model F) (D : Subgroup C) (hD : IsComponent C D) : center D = ⊥ := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (commutator (Model F)) := derived_isSimple
  let : IsSimpleGroup D := (componentEquivCommutator e D hD).isSimpleGroup
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp h)).elim

/-- The literal quotient by the component center is the same derived model. -/
noncomputable def componentCenterQuotientEquiv {C : Type*} [Group C]
    (e : C ≃* Model F) (D : Subgroup C) (hD : IsComponent C D) :
    (D ⧸ center D) ≃* commutator (Model F) :=
  (QuotientGroup.quotientMulEquivOfEq (component_center_eq_bot e D hD)).trans
    ((QuotientGroup.quotientBot).trans (componentEquivCommutator e D hD))

/-- Full marked outer descent identifies every ordinary fixed component and
its literal central quotient, without replacing full G₂(2) by its derived
group in the fixed-group equivalence. -/
theorem outer_fixed_component_descent_of_equiv
    {G : Type*} [Group G] (e : G ≃* Model F)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = 2 ^ n)
    (a : MulAut G) (ha : orderOf a = 2) (hout : ∀ g : G, a ≠ MulAut.conj g)
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    ∃ (σ : F ≃+* F) (m : ℕ), 0 < m ∧ m < n ∧ n = 2 * m ∧
      Nat.card (fixedField σ) = 2 ^ m ∧ orderOf σ = 2 ∧
      (∃ c : Model F, MulAut.congr e a =
        MulAut.conj c * LieAutomorphismExtensions.fieldAction σ * (MulAut.conj c)⁻¹) ∧
      ∃ E : a.fixedSubgroup ≃* Model (fixedField σ),
        D.map E.toMonoidHom = commutator (Model (fixedField σ)) ∧
        center D = ⊥ ∧ Nonempty (D ≃* commutator (Model (fixedField σ))) ∧
        Nonempty ((D ⧸ center D) ≃* commutator (Model (fixedField σ))) := by
  obtain ⟨σ,m,hm,hmn,hnm,hcard,hs,hc',⟨E⟩,_⟩ :=
    outer_involution_conclusion_of_equiv e hn hc a ha hout
  exact ⟨σ,m,hm,hmn,hnm,hcard,hs,hc',E,component_map_eq_commutator E D hD,
    component_center_eq_bot E D hD,⟨componentEquivCommutator E D hD⟩,
    ⟨componentCenterQuotientEquiv E D hD⟩⟩
end Atlas.G2.EvenFieldFixedResidual
