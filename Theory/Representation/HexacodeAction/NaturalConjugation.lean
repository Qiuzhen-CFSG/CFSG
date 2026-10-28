module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The central-quotient action of a hexacode overgroup

For a normal subgroup C, transport actual conjugation on C/Z(C) to A₆.
A faithful embedding of the overgroup in the hexacode automorphism group,
with C mapping onto the even subgroup, forces this action into the natural
S₆. The coordinate permutation homomorphism proves the assertion on
representatives. Normality of the natural S₆ in Aut(A₆) makes it independent
of the chosen central-quotient equivalence.

This is the group-action transport needed after recognizing an irreducible
hexacode section. It does not assert that any given module has such a section.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(8),
B.4.5 (printed pp.86–87), K.1.3 (p.453), and 13.8.21(2) (p.956).
The hexacode and coordinate maps are the licensed ATLAS ports imported by
HexacodeAction.Cover.
-/

@[expose] public section

open Subgroup Atlas.Codes AlternatingSix.ShadowLocal

namespace Representation.Hexacode

variable {D : Type*} [Group D] (C : Subgroup D) [C.Normal]

def centralSixAction (e : (C ⧸ center C) ≃* A6) : D →* AutA6 :=
  (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (center C)).comp (MulAut.conjNormal : D →* MulAut C))

theorem centralSixAction_mk (e : (C ⧸ center C) ≃* A6) (d : D) (c : C) :
    centralSixAction C e d (e (QuotientGroup.mk' (center C) c)) =
      e (QuotientGroup.mk' (center C) (MulAut.conjNormal d c)) := by
  change e (quotientAut (center C) (MulAut.conjNormal d)
    (e.symm (e (QuotientGroup.mk' (center C) c)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]

theorem centralSixAction_change (e f : (C ⧸ center C) ≃* A6) (d : D) :
    centralSixAction C f d =
      (e.symm.trans f) * centralSixAction C e d * (e.symm.trans f)⁻¹ := by
  apply MulEquiv.ext
  intro a
  change f (quotientAut (center C) (MulAut.conjNormal d) (f.symm a)) =
    f (e.symm (e (quotientAut (center C) (MulAut.conjNormal d)
      (e.symm (e (f.symm a))))))
  simp only [e.symm_apply_apply]

theorem centralSixAction_natural_iff (e f : (C ⧸ center C) ≃* A6) (d : D) :
    centralSixAction C e d ∈ natural ↔ centralSixAction C f d ∈ natural := by
  let : natural.Normal := normal_of_index_eq_two
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  rw [centralSixAction_change C e f]
  constructor
  · intro h
    exact Subgroup.Normal.conj_mem inferInstance _ h _
  · intro h
    have hc := Subgroup.Normal.conj_mem (inferInstance : natural.Normal) _ h
      (e.symm.trans f)⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_inv, inv_mul_cancel, mul_one] using hc

noncomputable def componentEquiv (φ : D →* HexAutomorphisms)
    (hf : Function.Injective φ) (hc : C.map φ = hexSign.ker) :
    C ≃* HexEvenAutomorphisms :=
  (C.equivMapOfInjective φ hf).trans (MulEquiv.subgroupCongr hc)

omit [C.Normal] in
theorem componentEquiv_apply (φ : D →* HexAutomorphisms)
    (hf : Function.Injective φ) (hc : C.map φ = hexSign.ker) (c : C) :
    (componentEquiv C φ hf hc c : HexAutomorphisms) = φ c := rfl

private theorem map_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr e ⟨a, ha⟩).property
  · intro hb
    exact ⟨e.symm b, (centerCongr e.symm ⟨b, hb⟩).property, e.apply_symm_apply b⟩

noncomputable def componentCentralEquiv (φ : D →* HexAutomorphisms)
    (hf : Function.Injective φ) (hc : C.map φ = hexSign.ker) :
    (C ⧸ center C) ≃* A6 :=
  (QuotientGroup.congr _ _ (componentEquiv C φ hf hc)
    (by exact map_center_equiv _)).trans even_quotient_center_equiv

omit [C.Normal] in
theorem componentCentralEquiv_mk (φ : D →* HexAutomorphisms)
    (hf : Function.Injective φ) (hc : C.map φ = hexSign.ker) (c : C) :
    componentCentralEquiv C φ hf hc (QuotientGroup.mk' (center C) c) =
      hexEvenCoordinate (componentEquiv C φ hf hc c) := rfl

theorem centralSixAction_coordinate (φ : D →* HexAutomorphisms)
    (hf : Function.Injective φ) (hc : C.map φ = hexSign.ker) (d : D) :
    centralSixAction C (componentCentralEquiv C φ hf hc) d =
      permutationAction (hexCoordinateSixHom (φ d)) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨q, rfl⟩ := (componentCentralEquiv C φ hf hc).surjective a
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center C) q
  rw [centralSixAction_mk, componentCentralEquiv_mk, componentCentralEquiv_mk]
  apply Subtype.ext
  change hexCoordinateSixHom (φ ((MulAut.conjNormal d c : C) : D)) =
    hexCoordinateSixHom (φ d) * hexCoordinateSixHom (φ c) *
      (hexCoordinateSixHom (φ d))⁻¹
  rw [MulAut.conjNormal_apply]
  simp only [map_mul, map_inv]

theorem centralSixAction_mem_natural (e : (C ⧸ center C) ≃* A6)
    (φ : D →* HexAutomorphisms) (hf : Function.Injective φ)
    (hc : C.map φ = hexSign.ker) (d : D) : centralSixAction C e d ∈ natural := by
  apply (centralSixAction_natural_iff C e (componentCentralEquiv C φ hf hc) d).mpr
  rw [centralSixAction_coordinate]
  exact ⟨hexCoordinateSixHom (φ d), rfl⟩

end Representation.Hexacode
