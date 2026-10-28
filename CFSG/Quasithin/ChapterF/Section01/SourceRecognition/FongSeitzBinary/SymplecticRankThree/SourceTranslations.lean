module
public import Theory.GroupAction.SymplecticRankThree.AdditiveLines
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceAffine

/-!
# Additive affine geometry of the original C₂ quotient

Apply the spatial projection and translation-group constructions to the
polarity design on the same original parabolic cosets. The resulting abelian
translation group has order q², its direction subgroups have order q, and
its cosets are exactly the actual affine lines. The actual affine point set
receives an abelian addition with zero at the chosen origin and the proved
additive line equations. All constructions include q=2 and use no field
coordinates as input.

The earlier local PSL₂ markings and selected (6A)(a) commutator clause retain
their original producers. This discharges the additive part of coordinate
reconstruction; multiplication, projective coordinates and the final
nonbinary marked comparison remain unproved by this module. These geometric
translations are not asserted to be elements of the original source group.

Source: Fong–Seitz I (6A)(a), II (7C), p.193 and (8A), p.197;
Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
local notation "a₀" => C2RankThree.rightCosetPoint Q 1 1
local notation "b₀" => C2RankThree.neighborPoint Q
local notation "Γ" => MulAction.SwappedOrbital.graph a₀ b₀ (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)

include e h in
/-- Construct the abelian translation group and additive line equations on
the original parabolic cosets. All earlier row and local marking inputs
remain precisely those of the incidence producer. -/
theorem marked_affine_addition_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨ (Γ).Adj x y) ∧
      ∃ (hl : ∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1)
        (f : AffineFrame D), f.infinity = a₀ ∧
      ∃ hq' : 2 ≤ Nat.card F,
        Nat.card (f.translations hl hq') = Nat.card F^2 ∧
        (∀ d : f.Direction hl hq', Nat.card (f.directionTranslations hl hq' d) = Nat.card F) ∧
        (∀ (T U : f.translations hl hq') (d : f.Direction hl hq'),
          (f.translationEquiv hl hq' U : C2RankThree.Points Q 1) ∈
            D.line d (f.translationEquiv hl hq' T) ↔
              T⁻¹ * U ∈ f.directionTranslations hl hq' d) ∧
        ∃ A : AddCommGroup (f.Base hl hq'),
          letI := A
          (0 : f.Base hl hq') = f.baseOrigin hl hq' ∧
          ∀ (a b : f.Base hl hq') (d : f.Direction hl hq'),
            (a : C2RankThree.Points Q 1) ∈ D.line d b ↔
              (a-b : f.Base hl hq').val.val ∈ D.line d f.origin := by
  obtain ⟨D,hD,hl,f,hf,hq',_⟩ := marked_affine_charts_of_linear_row Q e h split hm μ hq hrow
  exact ⟨D,hD,hl,f,hf,hq',f.translations_card hl hq',f.directionTranslations_card hl hq',
    f.affine_line_coset hl hq',f.affineAddCommGroup hl hq',
    f.affine_zero hl hq',f.affine_line_add hl hq'⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
