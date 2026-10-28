module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms

/-!
# The full binary Ree local model and its compatible transport

The model predicate requires an isomorphism to the concrete inclusion amalgam
in the full fixed matrix group. Transport therefore retains both overlap maps.
The intrinsic core orders and the actual Sz(2) and PSL₂(2) quotients follow
from the proved root projections. The ambient equivalence with all automorphisms
of the Atlas Tits group identifies the full marked extension, with the same
inner-subgroup intersections. No uniqueness assertion is included.

Source: Aschbacher--Smith F.1.12(I)(5), q = 2, printed pp.263--264,
and 14.2.21, printed pp.988--989.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook
open Theory.GroupTheory

/-- Compatibility with both inclusions of the actual full binary Ree model. -/
def IsBinaryReeAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) : Prop :=
  Nonempty (RankTwoAmalgam.Iso α Tits.ExceptionalParabolics.FullRee.amalgam)

namespace IsBinaryReeAmalgam
variable {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}

/-- The orders of the full parabolics and their whole common overlap. -/
theorem cards (h : IsBinaryReeAmalgam α) :
    Nat.card L = 20480 ∧ Nat.card B = 4096 ∧ Nat.card R = 12288 := by
  obtain ⟨e⟩ := h
  exact ⟨(Nat.card_congr e.left.toEquiv).trans
      Tits.ExceptionalParabolics.FullRee.first_card,
    (Nat.card_congr e.middle.toEquiv).trans
      Tits.ExceptionalParabolics.FullRee.borel_card,
    (Nat.card_congr e.right.toEquiv).trans
      Tits.ExceptionalParabolics.FullRee.second_card⟩

/-- The orders concern the intrinsic cores of the full local groups. -/
theorem core_cards (h : IsBinaryReeAmalgam α) :
    Nat.card (pCore 2 L) = 1024 ∧ Nat.card (pCore 2 R) = 2048 := by
  obtain ⟨e⟩ := h
  exact ⟨(LocalCoreTransport.core_card 2 e.left).trans
      Tits.ExceptionalParabolics.FullRee.first_core_card,
    (LocalCoreTransport.core_card 2 e.right).trans
      Tits.ExceptionalParabolics.FullRee.second_core_card⟩

/-- The overlap is the specified Sylow subgroup of order 4096. -/
theorem overlap_card (h : IsBinaryReeAmalgam α) : Nat.card B = 4096 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.middle.toEquiv).trans
    Tits.ExceptionalParabolics.FullRee.borel_card

/-- Transport to the actual binary Suzuki and projective linear matrix groups. -/
theorem core_quotients (h : IsBinaryReeAmalgam α) :
    Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
    Nonempty ((R ⧸ pCore 2 R) ≃* ReeF4.LargeLocalSeeds.LinearQuotient 0) := by
  obtain ⟨e⟩ := h
  exact ⟨⟨(LocalCoreTransport.quotientEquiv 2 e.left).trans
      Tits.ExceptionalParabolics.FullRee.firstCoreQuotientEquiv⟩,
    ⟨(LocalCoreTransport.quotientEquiv 2 e.right).trans
      Tits.ExceptionalParabolics.FullRee.secondCoreQuotientEquiv⟩⟩

/-- The same marked amalgam occurs inside the actual full automorphism group. -/
theorem automorphism_model (h : IsBinaryReeAmalgam α) :
    Nonempty (RankTwoAmalgam.Iso α
      Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgamIso⟩

end IsBinaryReeAmalgam

/-- The concrete automorphism amalgam supplies the model witness, so all the
local transport theorems apply to its literal subgroups of `MulAut`. -/
theorem isBinaryReeAmalgam_automorphism :
    IsBinaryReeAmalgam Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam :=
  ⟨Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgamIso.symm⟩

/-- Actual core orders in the full automorphism group, not an abstract family tag. -/
theorem binaryReeAutomorphism_core_cards :
    Nat.card (pCore 2 Tits.ExceptionalParabolics.FullRee.AutomorphismModel.first) = 1024 ∧
    Nat.card (pCore 2 Tits.ExceptionalParabolics.FullRee.AutomorphismModel.second) = 2048 :=
  isBinaryReeAmalgam_automorphism.core_cards

end CFSG.Quasithin.ChapterF.GreenBook
