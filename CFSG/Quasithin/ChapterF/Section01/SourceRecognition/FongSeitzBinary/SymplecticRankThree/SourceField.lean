module
public import Theory.GroupAction.SymplecticRankThree.FieldPlane
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceTranslations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceProjective

/-!
# Field-linear affine planes on the original C₂ quotient

The original local PSL₂ markings and selected (6A)(a) row construct incidence
on the same second-parabolic cosets. Spatial homotheties and translations
now construct a field of the required order, with multiplication and all
field laws proved internally. Finite-field uniqueness identifies it with
the original local field F. The actual affine base plane consequently has
coordinates in F² with every line given by x=c or y=mx+b.

The line relation below is the literal orbitalLine of the original action,
so this is an application to the same marked quotient, not an abstract
translation-plane tag. It includes q=2 and q=4. Extending these planar
coordinates to the full projective three-space is still required by
SourceProjective before its nonbinary marked comparison can be discharged.
All original row, local-marking and normal-generation producers are retained.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155;
Fong–Seitz I (6A)(a), II (7C), p.193, and (8A), p.197.
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
/-- Construct field-linear coordinates on the actual source affine plane,
including all ordinary line equations, with no coordinate premise. -/
theorem marked_field_plane_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨ (Γ).Adj x y) ∧
      ∃ (hl : ∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1)
        (f : AffineFrame D), f.infinity = a₀ ∧
      ∃ (hq' : 2 ≤ Nat.card F) (C : f.Base hl hq' ≃ F × F),
        (∀ a b x : f.Base hl hq',
          (x : C2RankThree.Points Q 1) ∈ orbitalLine Q a b ↔
            ∃ r : F, C x = C a + r • (C b-C a)) ∧
        (∀ a b : f.Base hl hq', a ≠ b →
          (∃ c : F, ∀ x : f.Base hl hq',
            (x : C2RankThree.Points Q 1) ∈ orbitalLine Q a b ↔ (C x).1 = c) ∨
          (∃ m c : F, ∀ x : f.Base hl hq',
            (x : C2RankThree.Points Q 1) ∈ orbitalLine Q a b ↔ (C x).2 = m*(C x).1+c)) := by
  obtain ⟨D,hD,hl,f,hf,hq',_⟩ := marked_affine_charts_of_linear_row Q e h split hm μ hq hrow
  have hL (x y : C2RankThree.Points Q 1) : D.line x y = orbitalLine Q x y := by
    ext z
    simp only [PolarityDesign.mem_line,hD,orbitalLine,Set.mem_ofPred_eq]
  refine ⟨D,hD,hl,f,hf,hq',f.fieldPlaneCoordinatesOver hl hq' F rfl,?_,?_⟩
  · intro a b x
    simpa only [hL] using f.fieldPlaneCoordinatesOver_line hl hq' F rfl a b x
  · intro a b hab
    simpa only [hL] using f.fieldPlaneCoordinatesOver_equations hl hq' F rfl a b hab

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
