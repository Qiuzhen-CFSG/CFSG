module
public import Theory.GroupAction.SymplecticRankThree.ProjectivePlanes
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceProjective

/-!
# Projective planes on the original C₂ coset geometry

Complete the proved affine field plane by adding its actual directions at
infinity, then project to every source block. This constructs an ordinary
projective-plane chart over the original local field on every closed
neighborhood of the literal second-parabolic coset action. Every line formula
is the same orbitalLine already consumed by SourceProjective. No planar
coordinate map, field equations or recognition premise is assumed, including
when q=2 or q=4.

These are coordinates on whole planes. Their compatible extension to one
projective three-space chart remains necessary before the general marked
symplectic comparison can be discharged. Both endpoint markings, the full
Borel, original quotient map, row and local-action producers are retained by
the existing comparison route.

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
local notation "a₀" => C2RankThree.rightCosetPoint Q 1 1
local notation "b₀" => C2RankThree.neighborPoint Q
local notation "Γ" => MulAction.SwappedOrbital.graph a₀ b₀ (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)

/-- The actual closed neighbor block in the original parabolic coset action. -/
@[expose] def orbitalBlock (p : C2RankThree.Points Q 1) : Set (C2RankThree.Points Q 1) :=
  {x | x = p ∨ (Γ).Adj p x}

variable (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- Every whole original orbital block has constructed projective-plane
coordinates, preserving the literal source lines in both directions. -/
theorem marked_projective_planes_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∀ p : C2RankThree.Points Q 1,
      ∃ C : ↥(orbitalBlock Q p) ≃ Projectivization F (F × (F × F)),
        ∀ a b x : ↥(orbitalBlock Q p),
          (C x).submodule ≤ (C a).submodule ⊔ (C b).submodule ↔
            (x : C2RankThree.Points Q 1) ∈ orbitalLine Q a b := by
  obtain ⟨D,hD,_,hl,_⟩ := marked_projective_incidence_of_linear_row Q e h split hm μ hq hrow
  have hL (x y : C2RankThree.Points Q 1) : D.line x y = orbitalLine Q x y := by
    ext z
    simp only [PolarityDesign.mem_line,hD,orbitalLine,Set.mem_ofPred_eq]
  have hq' : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  intro p
  obtain ⟨C,hC⟩ := D.exists_projective_plane_coordinates hl hq'
    (C2RankThree.points_card Q split hm (hq 0) (hq 1) 1) p F rfl
  let E : ↥(orbitalBlock Q p) ≃ ↥(D.block p) := Equiv.setCongr (by
    ext x
    exact (hD p x).symm)
  refine ⟨E.trans C,?_⟩
  intro a b x
  have hh := hC (E a) (E b) (E x)
  change (C (E x)).submodule ≤ (C (E a)).submodule ⊔ (C (E b)).submodule ↔
    (x : C2RankThree.Points Q 1) ∈ D.line a b at hh
  exact hh.trans (by rw [hL])

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
