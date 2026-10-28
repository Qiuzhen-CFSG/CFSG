module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualCentralizers
public import Theory.GroupTheory.CentralizerImageConjugation

/-!
# Two exact centralizer images in the same marked product

An exact centralizer image for the first original block transports along
the prescribed conjugator. The opposite residual images then identify both
full symmetric-five axes, retaining the same quotient, marking and conjugator.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V) (q : G →* H) (hq : Function.Surjective q)
  (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
  (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))

include hq c in
theorem paired_symmetric_conjugate_centralizer_images
    (A : Subgroup G) (t : G)
    (haxes :
      (A.map q = (factorResidual q (offenderSubgroup ρ) d.first).map q ∧
        ((offenderSubgroup ρ).comap q ⊓ centralizer (A : Set G)).map q =
          d.second.map (offenderSubgroup ρ).subtype) ∨
      (A.map q = (factorResidual q (offenderSubgroup ρ) d.second).map q ∧
        ((offenderSubgroup ρ).comap q ⊓ centralizer (A : Set G)).map q =
          d.first.map (offenderSubgroup ρ).subtype))
    (hop :
      (A.map q = (factorResidual q (offenderSubgroup ρ) d.first).map q ∧
        (A.map (MulAut.conj t).toMonoidHom).map q =
          (factorResidual q (offenderSubgroup ρ) d.second).map q) ∨
      (A.map q = (factorResidual q (offenderSubgroup ρ) d.second).map q ∧
        (A.map (MulAut.conj t).toMonoidHom).map q =
          (factorResidual q (offenderSubgroup ρ) d.first).map q)) :
    (((offenderSubgroup ρ).comap q ⊓ centralizer (A : Set G)).map q =
        d.second.map (offenderSubgroup ρ).subtype ∧
      ((offenderSubgroup ρ).comap q ⊓ centralizer
        (A.map (MulAut.conj t).toMonoidHom : Set G)).map q =
          d.first.map (offenderSubgroup ρ).subtype) ∨
    (((offenderSubgroup ρ).comap q ⊓ centralizer (A : Set G)).map q =
        d.first.map (offenderSubgroup ρ).subtype ∧
      ((offenderSubgroup ρ).comap q ⊓ centralizer
        (A.map (MulAut.conj t).toMonoidHom : Set G)).map q =
          d.second.map (offenderSubgroup ρ).subtype) := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  have hA : (Y.comap q ⊓ centralizer (A : Set G)).map q =
      Y ⊓ centralizer (A.map q : Set H) := by
    rcases haxes with h | h
    · rw [h.1,paired_symmetric_first_residual_centralizer ρ q hq d c]
      exact h.2
    · rw [h.1,paired_symmetric_second_residual_centralizer ρ q hq d c]
      exact h.2
  have hB := centralizer_image_eq_conjugate q Y A t hA
  rcases hop with h | h
  · left
    rw [h.1,paired_symmetric_first_residual_centralizer ρ q hq d c] at hA
    rw [h.2,paired_symmetric_second_residual_centralizer ρ q hq d c] at hB
    exact ⟨hA,hB⟩
  · right
    rw [h.1,paired_symmetric_second_residual_centralizer ρ q hq d c] at hA
    rw [h.2,paired_symmetric_first_residual_centralizer ρ q hq d c] at hB
    exact ⟨hA,hB⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
