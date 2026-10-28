module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import Theory.ElementaryAbelian.Quotient

/-!
# The genuine quotient transvection configuration

An ambient commutator equal to an order-two line disjoint from the quotient
kernel gives a nontrivial group of linear transvections on the actual binary
quotient. The center is its actual commutator image. This is the recognition
step after endpoint transport in Aschbacher–Smith 13.8.7, pp.948–949.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial group of transvections, with the specified actual center. -/
theorem quotient_transvections_of_commutator_line
    (P U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G))
    (hZ : (Z.subgroupOf U).Normal)
    (hc : ⁅U, P⁆ = A) (hcard : Nat.card A = 2) (hdisj : Z ⊓ A = ⊥) :
    let _ := hZ
    ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        action p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (hn p.property) u).mp u.property⟩) ∧
      commutatorAction action.range (U ⧸ Z.subgroupOf U) =
        (A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) ∧
      Nat.card (commutatorAction action.range (U ⧸ Z.subgroupOf U)) = 2 ∧
      action.range ≠ ⊥ ∧
      ∀ p : P, binaryLinear (action p) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) := by
  let _ := hZ
  obtain ⟨action, hact⟩ := exists_quotient_conjugation_action P U Z hn hz hZ
  have hactors : (P.subgroupOf P).map action = action.range := by
    rw [subgroupOf_self, ← MonoidHom.range_eq_map]
  have himage := quotient_conjugation_commutatorAction_eq_image P U Z P hn le_rfl
    hZ action hact
  rw [hactors, hc] at himage
  have hsize := quotient_conjugation_commutatorAction_card P U Z P hn le_rfl
    hZ action hact
  rw [hactors, hc, ← inf_relIndex_right Z A, hdisj, relIndex_bot_left, hcard] at hsize
  have hntr : action.range ≠ ⊥ := by
    intro he
    have hi : (A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = ⊥ := by
      rw [← himage, commutatorAction_eq_closure]
      apply le_bot_iff.mp
      apply (closure_le _).mpr
      rintro _ ⟨a, w, rfl⟩
      have ha : (a : MulAut (U ⧸ Z.subgroupOf U)) = 1 := mem_bot.mp (he ▸ a.property)
      change w⁻¹ * (a : MulAut (U ⧸ Z.subgroupOf U)) w ∈ _
      simp [ha]
    rw [himage, hi] at hsize
    simp at hsize
  refine ⟨action, hact, himage, hsize, hntr, ?_⟩
  intro p
  exact transvections_of_displacement_card_two action.range hsize (action p) ⟨p, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
