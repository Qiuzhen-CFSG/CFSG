module

public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.PGroup.OmegaImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupAction.Defs

/-!
# Central omega subgroups in the ambient group

The subgroup Ω₁(Z(P)) has two common presentations: map omega along the
center and subgroup inclusions, or first embed the center and take its omega.
They agree. Centrality and the equation x²=1 give a direct membership test.
This also proves Ω₁(Z(R))=C_{Ω₁(Z(Q))}(R) when Q≤R and Z(R)≤Q.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.4.6, printed p.814; the source application proves the center containment.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
set_option linter.style.haveILetI false
namespace Subgroup
variable {G : Type*} [Group G]
/-- The actual first omega of the center, in the original ambient group. -/
abbrev omegaCenterIn (P : Subgroup G) : Subgroup G :=
  ((omega₁ (center P) (p := 2)).map (center P).subtype).map P.subtype

/-- Central omega subgroups are elementary abelian. -/
instance omegaCenterIn_elementary (P : Subgroup G) : IsElementaryAbelian 2 (omegaCenterIn P) := by
  letI : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  letI : IsElementaryAbelian 2 ((omega₁ (center P) (p := 2)).map (center P).subtype) :=
    IsElementaryAbelian.map _
  exact IsElementaryAbelian.map _

/-- Membership means centrality in P and square one. -/
theorem mem_omegaCenterIn_iff (P : Subgroup G) (x : G) :
    x ∈ omegaCenterIn P ↔ x ∈ P ∧ x ∈ centralizer (P : Set G) ∧ x ^ 2 = 1 := by
  constructor
  · intro hx
    refine ⟨map_subtype_le _ hx, ?_, elemPow_eq_one_of_isElementaryAbelian x hx⟩
    obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hx
    intro p hp
    exact congrArg P.subtype (mem_center_iff.mp b.property ⟨p,hp⟩)
  · rintro ⟨hp,hc,hs⟩
    let a : center P := ⟨⟨x,hp⟩, mem_center_iff.mpr (fun p => Subtype.ext (hc p p.property))⟩
    have ha : a ∈ omega₁ (center P) (p := 2) := by
      apply subset_closure
      change a ^ (2 ^ 1) = 1
      apply Subtype.ext
      apply Subtype.ext
      simpa using hs
    exact ⟨a, ⟨a, ha, rfl⟩, rfl⟩

/-- Agreement with omega taken after embedding the center. -/
theorem omegaCenterIn_eq_omegaOneAmbient (P : Subgroup G) :
    omegaCenterIn P = omegaOneAmbient ((center P).map P.subtype) := by
  rw [omegaCenterIn, map_map]
  apply map_omega_eq_of_injective_of_range_eq
    (P.subtype.comp (center P).subtype) ((center P).map P.subtype).subtype
    (P.subtype_injective.comp (center P).subtype_injective)
    ((center P).map P.subtype).subtype_injective
  simp only [MonoidHom.range_comp, range_subtype]

/-- Ambient normalizers preserve the characteristic central omega subgroup. -/
theorem normalizer_le_normalizer_omegaCenterIn (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (omegaCenterIn P : Set G) := by
  letI : (omega₁ (center P) (p := 2)).Characteristic := omega₁_characteristic _
  exact normalizer_le_normalizer_characteristic_image P
    ((omega₁ (center P) (p := 2)).map (center P).subtype)

/-- If Z(R) lies in Q ≤ R, central omega is obtained by centralizing R in Ω₁(Z(Q)). -/
theorem omegaCenterIn_eq_inf_of_center_le (Q R : Subgroup G)
    (hQR : Q ≤ R) (hc : centerIn R ≤ Q) :
    omegaCenterIn R = omegaCenterIn Q ⊓ centralizer (R : Set G) := by
  ext x
  simp only [mem_inf, mem_omegaCenterIn_iff]
  constructor
  · rintro ⟨hxR,hxc,hxs⟩
    exact ⟨⟨hc ⟨hxR,hxc⟩, centralizer_le hQR hxc, hxs⟩,hxc⟩
  · rintro ⟨⟨hxQ,_,hxs⟩,hxc⟩
    exact ⟨hQR hxQ,hxc,hxs⟩
end Subgroup
