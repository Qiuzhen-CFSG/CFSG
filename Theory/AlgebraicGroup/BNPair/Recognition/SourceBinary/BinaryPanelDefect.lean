module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SolvableNineAction
/-!
# The exact remainder defect on a binary unitary panel

The image of the same unipotent subgroup U is a Sylow two-subgroup of the
faithful local action. Its order is [U : U intersect K], for the full panel
kernel K. The canonical root has order eight on a nine-point panel, hence
[U : V] = 8. If the local group has order 72, these equations give
V = U intersect K and establish (2B). If its order is 144, they give the
exact exceptional index [V : U intersect K] = 2, so (2B) fails there.

No classification of arbitrary groups of order 144 is used. The original
source factor bounds in BinaryUnitaryOvergroup supply the two local orders;
BinaryUnitaryApplications applies this dichotomy on the original markings.
Source: Fong--Seitz I (2B), pp.7--9, and (5B)--(5C), pp.25--26.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The image of the actual source unipotent group is a Sylow subgroup of the local image. -/
def localSylow : Sylow 2 (localGroup Q split i) :=
  (split.sylow.subtype (show split.U ≤ localClosure Q split i from le_sup_left)).mapSurjective
    (localAction Q split i).rangeRestrict_surjective

theorem localSylow_card : Nat.card (localSylow Q split i) =
    (LocalCover.radical Q split i).relIndex split.U := by
  change Nat.card ((split.U.subgroupOf (localClosure Q split i)).map
    (localAction Q split i).rangeRestrict) = _
  rw [← relIndex_ker,MonoidHom.ker_rangeRestrict,localAction_ker,
    relIndex_subgroupOf (show split.U ≤ localClosure Q split i from le_sup_left)]
  exact (inf_relIndex_left split.U (localKernel Q i)).symm

/-- The exceptional local overgroup doubles the remainder modulo the actual two-kernel. -/
theorem remainder_index_cases (hp : Nat.card (Panel Q i) = 9)
    (hg : Nat.card (localGroup Q split i) = 72 ∨ Nat.card (localGroup Q split i) = 144) :
    (Nat.card (localGroup Q split i) = 72 ∧
      (LocalCover.radical Q split i).relIndex (simpleRemainder Q split i) = 1 ∧
      simpleRemainder Q split i ≤ localKernel Q i) ∨
    (Nat.card (localGroup Q split i) = 144 ∧
      (LocalCover.radical Q split i).relIndex (simpleRemainder Q split i) = 2 ∧
      ¬ simpleRemainder Q split i ≤ localKernel Q i) := by
  have hroot : Nat.card (simpleRoot Q split i) = 8 := by
    have hi := singleton_parabolic_root_index Q split i
    change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hi
    omega
  have he := relIndex_mul_relIndex (LocalCover.radical Q split i)
    (simpleRemainder Q split i) split.U
    (unipotent_inf_kernel_le_remainder Q split i) inf_le_left
  have hi : (simpleRemainder Q split i).relIndex split.U =
      Nat.card (simpleRoot Q split i) := simpleRemainder_index Q split i
  rw [hi,hroot,← localSylow_card] at he
  rcases hg with hg | hg
  · have hs : Nat.card (localSylow Q split i) = 8 := by
      rw [(localSylow Q split i).card_eq_multiplicity,hg]
      decide +kernel
    rw [hs] at he
    have hi : (LocalCover.radical Q split i).relIndex (simpleRemainder Q split i) = 1 := by omega
    exact Or.inl ⟨hg,hi,(relIndex_eq_one.mp hi).trans inf_le_right⟩
  · have hs : Nat.card (localSylow Q split i) = 16 := by
      rw [(localSylow Q split i).card_eq_multiplicity,hg]
      decide +kernel
    rw [hs] at he
    have hi : (LocalCover.radical Q split i).relIndex (simpleRemainder Q split i) = 2 := by omega
    refine Or.inr ⟨hg,hi,?_⟩
    intro hV
    have hr : simpleRemainder Q split i ≤ LocalCover.radical Q split i := le_inf inf_le_left hV
    have hh := relIndex_eq_one.mpr hr
    omega
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
