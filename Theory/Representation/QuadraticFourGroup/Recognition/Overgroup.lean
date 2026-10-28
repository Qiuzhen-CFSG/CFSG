module

public import Theory.Representation.QuadraticFourGroup.Models

/-!
# Restriction to the generated overgroup

The hypotheses of GLS, volume 2, Theorem 25.14 survive restriction to any
subgroup containing both the component and the four-group. Components remain
subnormal and quasisimple in the overgroup; the centralizer and moved-component
conditions are checked using the injective inclusion into the original group.

The component orbit commutes with homomorphic images. Consequently restriction
to an overgroup gives actual group equivalences of the component orbits and
of their quotients by their intrinsic two-cores. These identifications justify
the generated-overgroup reduction in Step 2 without changing the quotient in
the source conclusion. The irreducible-section reduction is a separate step.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- All source hypotheses survive restriction to an overgroup of `L` and `B`. -/
theorem Hypotheses.restrictOvergroup (h : Hypotheses ρ L B a)
    {H : Subgroup G} (hLH : L ≤ H) (hBH : B ≤ H) :
    Hypotheses (ρ.comp H.subtype) (L.subgroupOf H) (B.subgroupOf H)
      (⟨a, hBH h.mem⟩ : H) := by
  let aH : H := ⟨a, hBH h.mem⟩
  refine {
    faithful := h.faithful.comp H.subtype_injective
    component := h.component.subgroupOf hLH
    elementary := ?_
    card_four := ?_
    mem := h.mem
    involution := ?_
    moves := ?_
    quadratic := ?_
    centralizer := ?_
  }
  · let := h.elementary
    exact IsElementaryAbelian.subgroupOf hBH
  · exact (Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv).trans h.card_four
  · simpa only [← Subgroup.orderOf_coe] using h.involution
  · intro he
    apply h.moves
    have hm := congrArg (Subgroup.map H.subtype) he
    have hcomp : H.subtype.comp (MulAut.conj aH).toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp H.subtype := by ext x; rfl
    change ((L.subgroupOf H).map (MulAut.conj aH).toMonoidHom).map H.subtype =
      (L.subgroupOf H).map H.subtype at hm
    rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hLH] at hm
    exact hm
  · intro b hb v
    exact h.quadratic b hb v
  · apply le_bot_iff.mp
    intro b hb
    have hc : (b : G) ∈ B ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨hb.1, mem_centralizer_iff.mpr ?_⟩
      intro x hx
      exact congrArg Subtype.val
        (mem_centralizer_iff.mp hb.2 (⟨x, hLH hx⟩ : H) hx)
    rw [h.centralizer, mem_bot] at hc
    exact mem_bot.mpr (Subtype.ext hc)

end Representation.QuadraticFourGroup

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

private theorem map_conjugate (L : Subgroup G) (f : G →* H) (b : G) :
    (L.map (MulAut.conj b).toMonoidHom).map f =
      (L.map f).map (MulAut.conj (f b)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- A homomorphism takes the actual component orbit to the orbit of the images. -/
theorem componentOrbit_map (L B : Subgroup G) (f : G →* H) :
    (componentOrbit L B).map f = componentOrbit (L.map f) (B.map f) := by
  unfold componentOrbit
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro b
    rw [map_conjugate]
    exact le_iSup (fun c : B.map f =>
      (L.map f).map (MulAut.conj (c : H)).toMonoidHom)
      ⟨f b, mem_map_of_mem f b.property⟩
  · apply iSup_le
    rintro ⟨b, hb⟩
    obtain ⟨c, hc, rfl⟩ := hb
    rw [← map_conjugate]
    exact le_iSup (fun c : B => (L.map (MulAut.conj (c : G)).toMonoidHom).map f)
      ⟨c, hc⟩

/-- Restricting to an overgroup does not change the actual component orbit. -/
noncomputable def componentOrbitOvergroupEquiv (L B H : Subgroup G)
    (hLH : L ≤ H) (hBH : B ≤ H) :
    componentOrbit (L.subgroupOf H) (B.subgroupOf H) ≃* componentOrbit L B :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [componentOrbit_map, map_subgroupOf_eq_of_le hLH,
        map_subgroupOf_eq_of_le hBH]))

end Theory.GroupTheory

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The same identification preserves the intrinsic two-core quotient. -/
noncomputable def componentOrbitQuotientOvergroupEquiv (L B H : Subgroup G)
    (hLH : L ≤ H) (hBH : B ≤ H) :
    componentOrbit (L.subgroupOf H) (B.subgroupOf H) ⧸
        pCore 2 (componentOrbit (L.subgroupOf H) (B.subgroupOf H)) ≃*
      componentOrbit L B ⧸ pCore 2 (componentOrbit L B) :=
  QuotientGroup.congr _ _ (componentOrbitOvergroupEquiv L B H hLH hBH)
    (pCore_map_iso 2 _)

end Theory.GroupTheory

end
