module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.SolvableBlockCentralization.NormalAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.SolvableBlockCentralization.Orbit
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.Contracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.FixedNine
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# C-components centralize solvable A₃-blocks in characteristic two

Work inside the actual overgroup H. Characteristic two discharges the
O₂,₃ condition of C.1.9, so distinct conjugates of B commute. Three-rank at
most two bounds that conjugacy family by two, and the perfect C-component
X fixes B. The separate normal-action argument then centralizes the actual
A₃-block using its order-three quotient and natural four-element module.

The exported theorem constructs `ThreeBlockCentralization` from exact
`BlockCommutationInput` alone. Relative subnormality is preserved throughout;
no A₄ recognition, C-component classification, or assumed action conclusion
is used. This supplies the solvable-factor obligation of
`characteristicTwoComponentBlocks_of_threeBlockCentralization`; the remaining
source-theorem assembly stays with that consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–10,
printed pp.123–124, and E.6.7 and E.6.23, printed pp.246 and 254.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The A₃-block centralization obligation follows from exact C.1.9.
All relative normality, conjugation, rank and perfect-action steps are proved. -/
theorem threeBlockCentralization_of_blockCommutation
    (hc : BlockCommutationInput G) : ThreeBlockCentralization κ G := by
  intro H hsq hfit B X hBH hXH hB hsub hX
  let B' := B.subgroupOf H
  let X' := X.subgroupOf H
  let eB := subgroupOfEquivOfLe hBH
  let eX := subgroupOfEquivOfLe hXH
  let : Group.IsPerfect X' := hX.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := eX.toMonoidHom) eX.surjective
  have hshort : ChapterC.IsShort B' := hB.2.1.of_mulEquiv eB.symm
  have hblock : ChapterC.IsBlock B' := ⟨inferInstance, hshort, hsub⟩
  have h19 : C19Condition H := by
    apply twoThreeCore_generalizedFitting
    show centralizer (pCore 2 H : Set H) ≤ pCore 2 H
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hthree : ∃ a : B', orderOf a = 3 := by
    obtain ⟨a, ha⟩ := exists_order_three (Or.inr (Or.inl hB))
    exact ⟨eB.symm a, (eB.symm.orderOf_eq a).trans ha⟩
  have hn' : X' ≤ normalizer (B' : Set H) :=
    perfect_normalizes_of_commuting_three_conjugates B' X' hshort hthree
      (hsq.stronglyQuasithin 3 Nat.prime_three (by decide))
      (fun g h hne => hc H (fun _ => h19) _ _
        (hblock.map_equiv (MulAut.conj g)) (hblock.map_equiv (MulAut.conj h)) hne)
  have hn : X ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    have hx' : (⟨x, hXH hx⟩ : H) ∈ X' := hx
    exact (mem_normalizer_iff.mp (hn' hx') (⟨b, hBH hb⟩ : H)).mp hb
  exact perfect_centralizes_normalized_three_block hB hn

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
