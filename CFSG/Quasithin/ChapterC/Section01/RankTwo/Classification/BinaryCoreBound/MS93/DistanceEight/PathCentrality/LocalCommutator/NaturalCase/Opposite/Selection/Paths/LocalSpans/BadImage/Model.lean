module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model

/-!
# A fixed point shared by bad displacement planes

A nonidentity element of SL₃(2) fixing a plane pointwise has precisely that
plane as its fixed space. Thus every vector fixed by an actor belongs to
each plane whose pointwise centralizer in that actor is nontrivial.
Covectors annihilating those planes all annihilate the same fixed vector.
The proof uses subgroup cardinalities, without enumerating matrix subgroups.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), p.891.
Only the independent binary geometry from the p.884 development is reused.
-/

public section

open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
open Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

/-- A nontrivial matrix fixing a plane has no further fixed vectors. -/
theorem fixed_mem_plane (E : Subgroup Space) (hE : Nat.card E = 4)
    (g : SL) (hg : g ≠ 1) (hfix : g ∈ planeFixer E)
    (v : Space) (hv : modelAction g v = v) : v ∈ E := by
  let F := (modelAction g).fixedSubgroup
  have hEF : E ≤ F := fun v hv => (MulAut.mem_fixedSubgroup _ _).mpr (hfix v hv)
  have hFne : F ≠ ⊤ := by
    intro h
    apply hg
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro w
    change g.val.mulVec w = (1 : SL).val.mulVec w
    rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    exact congrArg Multiplicative.toAdd ((MulAut.mem_fixedSubgroup _ _).mp
      (show Multiplicative.ofAdd w ∈ F from h.ge (mem_top _)))
  have hspace : Nat.card Space = 8 := by simp
  have htop : Nat.card (⊤ : Subgroup Space) = 8 := by simp
  have hFlt : Nat.card F < 8 := by
    by_contra! hh
    exact hFne (eq_of_le_of_card_ge le_top (htop ▸ hh))
  have hFge : 4 ≤ Nat.card F := hE ▸ card_le_of_le hEF
  have hdvd : Nat.card F ∣ 8 := hspace ▸ F.card_subgroup_dvd_card
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have heq : E = F := eq_of_le_of_card_ge hEF (by omega)
  exact heq.ge ((MulAut.mem_fixedSubgroup _ _).mpr hv)

/-- One nonzero natural vector cuts out a proper subgroup of covectors. -/
theorem annihilator_ne_top (v : Space) (hv : v ≠ 1) : Model.annihilator v ≠ ⊤ := by
  intro he
  have hc := Model.annihilator_card v hv
  rw [he] at hc
  norm_num at hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
