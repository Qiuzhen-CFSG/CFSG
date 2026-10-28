module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.DiagramKernel
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification

/-!
# Marked Suzuki models of relative involution centralizers

Restriction of the original socle marking identifies its relative centralizer
with the fixed subgroup of the literal extension action. A specified inner
conjugacy then transports that fixed subgroup to the exceptional graph-field
representative. The proved fixed-matrix identification and coefficient-field
transport give the concrete Suzuki group, with an explicit matrix equation.

The matrix equation includes the inverse inner conjugation. It supplies the
marking needed for the pending centralizer quotient and Sylow geometry; it
does not eliminate the graph cocycle or identify the full ambient centralizer.

Source: Aschbacher--Smith E.1.14(1), printed p.214, and 16.1.4(7),
printed p.1171; Huppert--Blackburn III, XI.3.1--3.3 for the Suzuki matrices.
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
open DiagramAutomorphisms GraphFieldFixedResidual BenderSuzuki.MatrixGroups
open GraphFieldFixedResidual.MatrixIdentification
variable {G F : Type*} [Group G] [Field F]

/-- Restricting the marked socle model identifies the relative centralizer
with the actual fixed subgroup of the extension action. -/
noncomputable def socleCentralizerEquivFixed (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) (t : G) :
    (L ⊓ centralizer ({t} : Set G) : Subgroup G) ≃*
      (extensionAction L e t).fixedSubgroup := by
  let nt : normalizer (L : Set G) := ⟨t, normalizer_eq_top (H := L) ▸ mem_top t⟩
  let r := normalizerFixedEquivCentralizer L nt
  refine r.symm.trans (MulAut.fixedSubgroupEquivOfCompatible e.symm
    (L.normalizerMonoidHom nt) (extensionAction L e t) ?_)
  intro x
  change e.symm ((L.normalizerMonoidHom nt) x) =
    e.symm ((L.normalizerMonoidHom nt) (e (e.symm x)))
  rw [e.apply_symm_apply]

/-- This restriction retains the original ambient socle element. -/
theorem socleCentralizerEquivFixed_apply (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) (t : G) (x : (L ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    (socleCentralizerEquivFixed L e t x : Sp F) = e.symm ⟨x.val, x.property.1⟩ := by
  unfold socleCentralizerEquivFixed
  rw [MulEquiv.trans_apply, MulAut.fixedSubgroupEquivOfCompatible_apply]
  rfl

variable [Finite F] [CharP F 2]

/-- A specified inner conjugacy, rather than an outer-coset equality,
transports the whole fixed subgroup to the standard graph-field fixed group. -/
noncomputable def fixedEquivOfConjugacy (m : ℕ) (a : MulAut (Sp F)) (h : Sp F)
    (ha : a = MulAut.conj h * ExceptionalGraph.graphAut ^ (2 * m + 1) *
      (MulAut.conj h)⁻¹) : a.fixedSubgroup ≃* (graphFieldAut (F := F) m).fixedSubgroup :=
  MulAut.fixedSubgroupEquivOfCompatible (MulAut.conj h).symm a (graphFieldAut m) (by
    intro x
    rw [ha]
    change (MulAut.conj h).symm
      ((MulAut.conj h) (graphFieldAut m ((MulAut.conj h).symm x))) = _
    rw [MulEquiv.symm_apply_apply])

/-- The fixed-subgroup map is exactly conjugation by the inverse marking. -/
theorem fixedEquivOfConjugacy_apply (m : ℕ) (a : MulAut (Sp F)) (h : Sp F)
    (ha : a = MulAut.conj h * ExceptionalGraph.graphAut ^ (2 * m + 1) *
      (MulAut.conj h)⁻¹) (x : a.fixedSubgroup) :
    (fixedEquivOfConjugacy m a h ha x : Sp F) = h⁻¹ * x.val * h := by
  exact MulAut.fixedSubgroupEquivOfCompatible_apply _ _ _ _ _

/-- The literal relative centralizer is Suzuki once the specified cocycle
has been eliminated. Standard fixed-matrix identification is fully discharged. -/
noncomputable def socleCentralizerEquivSuzukiOfConjugacy
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) (t : G) (h : Sp F)
    (ht : extensionAction L e t =
      MulAut.conj h * ExceptionalGraph.graphAut ^ (2 * m + 1) * (MulAut.conj h)⁻¹) :
    (L ⊓ centralizer ({t} : Set G) : Subgroup G) ≃* SuzukiMatrixGroup m :=
  (socleCentralizerEquivFixed L e t).trans
    ((fixedEquivOfConjugacy m _ h ht).trans
      (fixedEquivOfBinaryModel m hF (fixedSuzukiEquiv m)))

/-- The Suzuki identification has the prescribed matrix formula, including
the inverse inner conjugation and the actual coefficient-field map. -/
theorem socleCentralizerEquivSuzukiOfConjugacy_matrix
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) (t : G) (h : Sp F)
    (ht : extensionAction L e t =
      MulAut.conj h * ExceptionalGraph.graphAut ^ (2 * m + 1) * (MulAut.conj h)⁻¹)
    (x : (L ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    ((socleCentralizerEquivSuzukiOfConjugacy L e m hF t h ht x :
      GL (Fin 4) (SuzukiField m)) : Matrix (Fin 4) (Fin 4) (SuzukiField m)) =
      matrixCoordinates (coefficientFieldEquiv m hF)
        (h⁻¹ * e.symm ⟨x.val, x.property.1⟩ * h) := by
  unfold socleCentralizerEquivSuzukiOfConjugacy
  simp only [MulEquiv.trans_apply]
  rw [fixedEquivOfBinaryModel_matrix m hF (fixedSuzukiEquiv m)
    (fixedSuzukiEquiv_matrix m), fixedEquivOfConjugacy_apply,
    socleCentralizerEquivFixed_apply]

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
