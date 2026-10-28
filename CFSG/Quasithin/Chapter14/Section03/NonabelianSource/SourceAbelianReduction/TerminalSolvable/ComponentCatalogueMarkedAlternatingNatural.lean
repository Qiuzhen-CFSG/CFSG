module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLowRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.NaturalModels

/-!
# Natural alternating rows in the marked two-copy branch

Complementary copies of the original constituent give an actual product
intertwiner for its whole component orbit, without any low-displacement
assumption. Natural A₅, A₆ and A₇ actions give the required component image;
the A₇ case retains equality with the normal orbit. A natural A₈ action
would yield the doubled whole-module model excluded by the already proved
ambient odd-rank and centralizer argument.

The final theorem supplies the original local lift and intrinsic two-core
quotient. Source: Aschbacher–Smith G.11.8, printed pp.368–369, and original
14.3.15, printed p.994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
private theorem doubled_quasiequivalent
    {D E U V W : Type*} [Group D] [Group E]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D U) (R : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) E W)
    (d : ρ.Equiv (R.prod R)) (hm : ChapterG.Section09.Quasiequivalent R σ) :
    ChapterG.Section09.Quasiequivalent ρ (σ.prod σ) := by
  obtain ⟨e,c,hc⟩ := hm
  refine ⟨e,d.toLinearEquiv.trans (c.prodCongr c),?_⟩
  intro a w
  have hh := LinearMap.congr_fun (d.isIntertwining' a) w
  change d (ρ a w) = (R a (d w).1,R a (d w).2) at hh
  change (c (d (ρ a w)).1,c (d (ρ a w)).2) = _
  rw [hh,hc,hc]
  rfl

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- The original two-copy source has genuine product coordinates for its
whole component orbit, without assuming a low-displacement actor. -/
theorem double_constituent_equiv
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    let H := componentOrbit L ⊤
    let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
    Nonempty (Representation.Equiv (F.terminalRepresentation.comp H.subtype)
      (R.toRepresentation.prod R.toRepresentation)) := by
  intro H R
  obtain ⟨J,⟨e⟩,hdis,hsup⟩ := s.exists_complementary_copy_of_double_dimension hk hd
  let q := Submodule.prodEquivOfIsCompl I J.toSubmodule
    (show IsCompl I J.toSubmodule from ⟨hdis,codisjoint_iff.mpr hsup⟩)
  let c := (LinearEquiv.refl (ZMod 2) I).prodCongr e.toLinearEquiv
  let f : Representation.Equiv (R.toRepresentation.prod R.toRepresentation)
      (F.terminalRepresentation.comp H.subtype) := .mk (c.trans q) (by
    intro a
    apply LinearMap.ext
    intro w
    have he := LinearMap.congr_fun (e.isIntertwining' a) w.2
    change e (R.toRepresentation a w.2) = J.toRepresentation a (e w.2) at he
    change (R.toRepresentation a w.1 : Additive F.Uhat) +
      (e (R.toRepresentation a w.2) : Additive F.Uhat) =
      F.terminalRepresentation a ((w.1 : Additive F.Uhat) + (e w.2 : Additive F.Uhat))
    rw [he,map_add]
    rfl)
  exact ⟨f.symm⟩

/-- Natural A₅–A₈ recognition on the original marked I closes the two-copy
image catalogue. A₇ retains the original component-orbit equality. -/
theorem imageCases_of_double_dimension_alternating_natural
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (n : ℕ) (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) : s.ImageCases := by
  by_cases he : n = 8
  · subst n
    obtain ⟨d⟩ := s.double_constituent_equiv hk hd
    exact (s.not_doubled_natural_six_seven_eight hk 8 (Or.inr (Or.inr rfl))
      (doubled_quasiequivalent _ _ _ d hm)).elim
  · obtain ⟨e,_,_⟩ := hm
    exact s.imageCases_of_natural_orbit_below_eight n hn5 (by omega) e

/-- The actual local component lift follows from the two-copy alternating
natural recognition, with the same intrinsic two-core quotient. -/
theorem local_lift_of_double_dimension_alternating_natural
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (n : ℕ) (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases
    (s.imageCases_of_double_dimension_alternating_natural hk hd n hn5 hn8 hm)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
