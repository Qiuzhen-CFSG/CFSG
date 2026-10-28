module

public import Theory.Representation.BinaryPlaneCubicCentralizer
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging

/-!
# Two-elements on a binary plane section with a central cubic

Odd averaging carries a fixed-point-free cubic action to an invariant
section. When that section is a binary plane, a commuting two-element acts
trivially. This is the displacement calculation for the original
extraspecial kernel core.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A two-element commuting with a fixed-point-free cubic moves the upper
space of a binary plane section only inside the lower space. -/
theorem two_element_section_displacement
    (ρ : Representation (ZMod 2) D W) (U E : Subrepresentation ρ)
    (hUE : U ≤ E)
    (hd : Module.finrank (ZMod 2) E.toSubmodule =
      Module.finrank (ZMod 2) U.toSubmodule + 2)
    (Z : Subgroup D) [Finite Z] (hZ : Nat.card Z = 3)
    (hfix : fixedSpace ρ Z = ⊥)
    (x : D) (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (hc : x ∈ centralizer (Z : Set D)) :
    ∀ w ∈ E.toSubmodule, ρ x w - w ∈ U.toSubmodule := by
  let L := sectionLower ρ U E
  let σ := sectionRepresentation ρ U E
  have hdim : Module.finrank (ZMod 2) (E.toSubmodule ⧸ L.toSubmodule) = 2 := by
    have hh := L.toSubmodule.finrank_quotient_add_finrank
    have he := (sectionLowerEquiv ρ hUE).finrank_eq
    change Module.finrank (ZMod 2) L.toSubmodule = _ at he
    omega
  have hEfix : Module.finrank (ZMod 2) (fixedSpace E.toRepresentation Z) = 0 := by
    rw [(subrepresentationFixedEquiv ρ E Z).finrank_eq, hfix, inf_bot_eq, finrank_bot]
  have hσfix : fixedSpace σ Z = ⊥ := by
    have hh := finrank_fixedSpace_quotient_of_odd E.toRepresentation L Z
      (show Odd (Nat.card Z) by rw [hZ]; decide)
    rw [hEfix] at hh
    change Module.finrank (ZMod 2) (fixedSpace σ Z) + _ = 0 at hh
    exact Submodule.finrank_eq_zero.mp (by omega)
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α := Z)
  have hzgen : zpowers (z : D) = Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,orderOf_eq_card_of_forall_mem_zpowers hz]
  have hz3 : (z : D)^3 = 1 := by
    have he : z^3 = 1 := by rw [←hZ]; exact pow_card_eq_one'
    exact congrArg Subtype.val he
  let f : D →* ((E.toSubmodule ⧸ L.toSubmodule) ≃ₗ[ZMod 2]
      (E.toSubmodule ⧸ L.toSubmodule)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp σ.asGroupHom
  have hzne : f z ≠ 1 := by
    intro he
    have htop : fixedSpace σ Z = ⊤ := by
      apply top_unique
      intro v _
      rw [←hzgen,mem_fixedSpace_zpowers_iff]
      exact congrArg (fun a : _ ≃ₗ[ZMod 2] _ => a v) he
    have hh : (⊤ : Submodule (ZMod 2) (E.toSubmodule ⧸ L.toSubmodule)) = ⊥ :=
      htop.symm.trans hσfix
    have hh' := congrArg (fun F : Submodule (ZMod 2) (E.toSubmodule ⧸ L.toSubmodule) =>
      Module.finrank (ZMod 2) F) hh
    simp only [finrank_top,finrank_bot,hdim] at hh'
    omega
  have hcube : (f x)^3 = 1 := binary_plane_commuting_cubic_pow hdim (f x) (f z)
    (by rw [←map_pow,hz3,map_one]) hzne
    ((show Commute x (z:D) from (hc z z.property).symm).map f)
  obtain ⟨n,hn⟩ := hx
  have htwo : (f x)^(2^n) = 1 := by rw [←map_pow,hn,map_one]
  have hone : f x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right n)
      (orderOf_dvd_of_pow_eq_one hcube) (orderOf_dvd_of_pow_eq_one htwo))
  apply (sectionRepresentation_trivial_iff ρ U E x).mp
  intro v
  exact congrArg (fun a : _ ≃ₗ[ZMod 2] _ => a v) hone

/-- The fixed space modulo the moved space is centralized by every
two-element which normalizes the actor and centralizes the cubic. -/
theorem two_element_fixed_displacement
    (ρ : Representation (ZMod 2) D W) (R Z : Subgroup D)
    [Finite Z] (hZ : Nat.card Z = 3)
    (hZR : Z ≤ normalizer (R : Set D)) (hfix : fixedSpace ρ Z = ⊥)
    (hUE : subspaceCommutator ρ ⊤ R ≤ fixedSpace ρ R)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ R) =
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ R) + 2)
    (x : D) (hx : ∃ n : ℕ, x^(2^n) = 1)
    (hxR : x ∈ normalizer (R : Set D)) (hxZ : x ∈ centralizer (Z : Set D)) :
    ∀ w ∈ fixedSpace ρ R, ρ x w - w ∈ subspaceCommutator ρ ⊤ R := by
  let H := normalizer (R : Set D)
  let σ := ρ.comp H.subtype
  let U : Subrepresentation σ := {
    toSubmodule := subspaceCommutator ρ ⊤ R
    apply_mem_toSubmodule g v hv :=
      (subspaceCommutator_invariant_normalizer ρ
        (show H ≤ subspaceStabilizer ρ ⊤ from le_subspaceStabilizer ρ ⊤
          (by intros; trivial)) le_rfl g.property v).2 hv }
  let E : Subrepresentation σ := {
    toSubmodule := fixedSpace ρ R
    apply_mem_toSubmodule g v hv :=
      (fixedSpace_stable_of_normalizes ρ (show H ≤ normalizer (R : Set D) from le_rfl)
        g.property v).2 hv }
  have hZcard : Nat.card (Z.subgroupOf H) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,hZ]
  let : Finite (Z.subgroupOf H) := Nat.finite_of_card_ne_zero (by rw [hZcard]; decide)
  have hfixed : fixedSpace σ (Z.subgroupOf H) = ⊥ := by
    apply bot_unique
    intro w hw
    have hh : w ∈ fixedSpace ρ Z := fun z => hw ⟨⟨z,hZR z.property⟩,z.property⟩
    exact hfix ▸ hh
  have hh := two_element_section_displacement σ U E hUE hd
    (Z.subgroupOf H) hZcard hfixed ⟨x,hxR⟩
    (by obtain ⟨n,hn⟩ := hx; exact ⟨n,Subtype.ext hn⟩)
    (by intro z hz; exact Subtype.ext (hxZ z hz))
  exact hh

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
