module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCoreGeometry
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4

/-!
# The original core geometry in the S₆ extension branch

The complete 13.5.15 conclusions identify H with the original point
centralizer. Transporting the proved point-core geometry gives
Φ(Q_H)=V₁ and Z(Q_H)=C_T(L₁). The Frattini identity identifies the ambient
normalizer of Q_H with H; characteristic two then identifies its entire
ambient centralizer with its center. In the S₆ branch that center has order
four. These are the literal inputs to the weak-closure argument.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921, the paragraph
beginning with the assumption M/V is isomorphic to S₆.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion

variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
  (b : CFSG.Quasithin.Chapter13.Section05.NormalBranch.Conclusions D M 6 g)

omit [Finite G] in
include b in
private theorem original_core_eq_module : D.LT.pCoreIn 2 = D.V := by
  rw [← b.seven.1]
  exact b.seven.2.symm

include d h e hseed hn hU b

theorem core_frattini_image : (frattini D.QH).map D.QH.subtype = D.V₁ := by
  have hp := SourcePointCoreGeometry.point_core_frattini_image
    d h e hseed hn hU (original_core_eq_module b)
  rw [← b.six.1] at hp
  exact hp

theorem core_center_image :
    (center D.QH).map D.QH.subtype =
      (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) := by
  have hp := SourcePointCoreGeometry.point_core_center_image
    d h e hseed hn hU (original_core_eq_module b)
  rw [← b.six.1] at hp
  change (center D.QH).map D.QH.subtype =
    D.QH ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) at hp
  rw [hp, inf_eq_right]
  rw [SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer
    d h e hseed hn hU]
  exact le_sup_right

theorem core_normalizer : normalizer (D.QH : Set G) = D.H := by
  apply le_antisymm ?_ (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D))
  have hp := normalizer_le_normalizer_characteristic_image D.QH (frattini D.QH)
  rw [core_frattini_image d h e hseed hn hU b, h.normalizer_point_eq, ← b.six.1] at hp
  exact hp

omit d e hseed hn hU in
theorem core_centralizer :
    centralizer (D.QH : Set G) = (center D.QH).map D.QH.subtype := by
  have hpoint : D.V₁ ≤ D.QH :=
    (h.point_lt.le.trans (le_conjugateSpanBy D.Vplus D.H)).trans h.UH_le_QH
  have hc : centralizer (D.QH : Set G) ≤ D.QH := by
    have hchar : centralizer (pCore 2 D.H : Set D.H) ≤ pCore 2 D.H := by
      simpa only [h.characteristic_H] using centralizer_generalizedFitting_le D.H
    intro x hx
    have hxH : x ∈ D.H := by
      rw [b.six.1]
      exact centralizer_le hpoint hx
    have hxC : (⟨x, hxH⟩ : D.H) ∈ centralizer (pCore 2 D.H : Set D.H) := by
      intro u hu
      exact Subtype.ext (hx u (mem_map_of_mem D.H.subtype hu))
    exact mem_map_of_mem D.H.subtype (hchar hxC)
  apply le_antisymm
  · intro x hx
    exact ⟨⟨x,hc hx⟩, mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property)), rfl⟩
  · rintro x ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)

omit [Finite G] d h hseed hn hU in
private theorem extension_alternative
    (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6))) :
    D.QH = D.UH ⊔ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ∧
      Nat.card ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) : Subgroup G) = 4 := by
  rcases (b.nine rfl).2 with hb | hb
  · obtain ⟨s⟩ := hS
    have hs : Nat.card (M ⧸ pCore 2 M) = 720 := by
      rw [Nat.card_congr s.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    have ha : Nat.card (D.L ⧸ pCore 2 D.L) = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hb.1,ha] at hs
    contradiction
  · exact hb.2

theorem extension_center_card
    (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6))) :
    Nat.card (center D.QH) = 4 := by
  have hc := (extension_alternative e b hS).2
  rw [← core_center_image d h e hseed hn hU b,
    card_map_of_injective D.QH.subtype_injective] at hc
  exact hc

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
