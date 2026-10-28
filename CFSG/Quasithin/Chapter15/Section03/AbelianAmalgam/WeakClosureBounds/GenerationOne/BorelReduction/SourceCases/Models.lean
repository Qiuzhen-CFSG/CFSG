module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.RankOneTori
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.SymplecticFour.Flag
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import CFSG.Quasithin.ClassicalModels

/-!
# Concrete model clauses for the full E.2.2 output

The six source alternatives use actual component images in H/J and actual
matrix groups. A Borel pair uses one isomorphism for both the group and its
overlap. Diagram conditions refer to conjugacy classes of the standard
parabolics; inner-field conditions are equations on projective matrices.
The unitary parameter is the fixed-field order, and the symplectic derived
subgroup is retained even at field order two.

These are source conclusion predicates, not classification proofs. The full
conditional reduction is assembled in the parent `SourceCases` module.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and 15.3.65, printed p.1152.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

/-- The actual overlap inside the component image in H/J. -/
abbrev componentOverlap (H M K : Subgroup G) :=
  (sourceImage H M (M ⊓ K)).subgroupOf (sourceImage H M K)

/-- Recognition of the component and its Borel by the same isomorphism. -/
def ModelBorelPair (H M K : Subgroup G) {X : Type*} [Group X] (B : Subgroup X) : Prop :=
  ∃ e : sourceImage H M K ≃* X, (componentOverlap H M K).map e.toMonoidHom = B

/-- Restrict a recognized pair using the existing quotient comparison API. -/
theorem ModelBorelPair.borel_equiv {H M K : Subgroup G}
    {X : Type*} [Group X] {B : Subgroup X} (h : ModelBorelPair H M K B) :
    Nonempty (sourceImage H M (M ⊓ K) ≃* B) := by
  obtain ⟨e, he⟩ := h
  exact ⟨componentBorelEquiv B e he⟩

/-- Aut_T(K*) uses the normalizing elements of T*, including in the exchanged case. -/
def sourceAutomizer (H M K T : Subgroup G) : Subgroup (MulAut (sourceImage H M K)) :=
  ((sourceImage H M T).subgroupOf (normalizer (sourceImage H M K : Set _))).map
    (sourceImage H M K).normalizerMonoidHom

/-- The source centralizer C_{K*}(Z((T ∩ K)*)), internal to K*. -/
def CentralizerOverlap (H M K T : Subgroup G) : Prop :=
  componentOverlap H M K = centralizer
    (((center ((sourceImage H M (T ⊓ K)).subgroupOf (sourceImage H M K))).map
      ((sourceImage H M (T ⊓ K)).subgroupOf (sourceImage H M K)).subtype :
        Subgroup (sourceImage H M K)) : Set _)

/-- Parabolic conjugacy classes give an intrinsic meaning to the diagram clause. -/
def PreservesParabolicClass {X : Type*} [Group X] (a : MulAut X) (P : Subgroup X) : Prop :=
  ∃ g : X, P.map a.toMonoidHom = P.map (MulAut.conj g).toMonoidHom

/-- Some actual T-induced automorphism moves one of the two diagram vertices. -/
def MovesDiagram (H M K T : Subgroup G) {X : Type*} [Group X]
    (e : sourceImage H M K ≃* X) (P Q : Subgroup X) : Prop :=
  ∃ a ∈ sourceAutomizer H M K T,
    ¬ (PreservesParabolicClass (MulAut.congr e a) P ∧
      PreservesParabolicClass (MulAut.congr e a) Q)

/-- Inner-field means an inner automorphism followed by an entrywise field
map on the actual projective matrices, in either characteristic. -/
def IsInnerFieldPSL2 {F : Type*} [Field F]
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) : Prop :=
  ∃ (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (σ : F ≃+* F),
    ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      a (QuotientGroup.mk' _ x) =
        g * QuotientGroup.mk' _ (Matrix.SpecialLinearGroup.map σ.toRingHom x) * g⁻¹

/-- The concrete unitary Borel: the join of the named projective root and torus
ranges. Its matrices use the quadratic field; the parameter below is the
order of the fixed field. -/
abbrev unitaryBorel {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :=
  (BenderSuzuki.External.hermitianUnipotentPSU J hJ).range ⊔
    (BenderSuzuki.External.hermitianTorusPSU J hJ).range

/-- Sp₄(q)' is retained literally, also at q = 2. -/
abbrev Sp4Derived (F : Type*) [Field F] :=
  commutator (Theory.SpecificGroups.SymplecticFour.Sp F)

/-- The Borel and the two parabolics in the derived symplectic model are
restrictions of the named matrix subgroups. -/
abbrev sp4DerivedBorel (F : Type*) [Field F] : Subgroup (Sp4Derived F) :=
  (Theory.SpecificGroups.SymplecticFour.borel (F := F)).subgroupOf (Sp4Derived F)

/-- The exchanged characteristic-two families, with exact Suzuki exponent. -/
def ExchangedModel (H M K : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    2 ≤ f ∧ Nat.card F = 2 ^ f ∧ ModelBorelPair H M K (BenderSuzuki.Converse.PBorel F)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
    ModelBorelPair H M K (SuzukiBorelSubgroup m))

/-- The remaining Bender family, PSU₃(2^f), over a matrix field of order 2^(2f). -/
def UnitaryModel (H M K : Subgroup G) (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
    2 ≤ f ∧ Nat.card F = (2 ^ f) ^ 2 ∧
    (∀ x, J.conj x = x ^ (2 ^ f)) ∧
    Nat.card {x : F // J.conj x = x} = 2 ^ f ∧
    ModelBorelPair H M K (unitaryBorel J hJ)

/-- All three simple Bender families, with their Borel pairs. -/
def BenderModel (H M K : Subgroup G) (f : ℕ) : Prop :=
  ExchangedModel H M K f ∨ UnitaryModel H M K f

/-- The two rank-two cases, including the actual induced diagram action.
No parity of f and no replacement of PSL₃ by SL₃ is made here. -/
def DiagramModel (H M K T : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage H M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
      (componentOverlap H M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F ∧
      MovesDiagram H M K T e (Matrix.PSL3.LinearThree.pointParabolic F)
        (Matrix.PSL3.LinearThree.lineParabolic F)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage H M K ≃* Sp4Derived F,
      (componentOverlap H M K).map e.toMonoidHom = sp4DerivedBorel F ∧
      MovesDiagram H M K T e
        ((Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)).subgroupOf (Sp4Derived F))
        ((Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)).subgroupOf (Sp4Derived F)))

/-- Case (1b), with p prime, the mod-eight condition, and the automizer bound. -/
def ExchangedOddModel (H M K T : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧
    ClassicalGroup.IsPSL (sourceImage H M K) 2 p ∧
    CentralizerOverlap H M K T ∧ 8 < Nat.card (sourceAutomizer H M K T)

/-- Case (2c). At exponent two the induced automizer is not contained in
inner-field automorphisms; the witness uses the same recognition map. -/
def SingleOddLinearModel (H M K T : Subgroup G) : Prop :=
  ∃ p d : ℕ, p.Prime ∧ 3 < p ∧ 0 < d ∧ d ≤ 2 ∧
    (p ^ d % 8 = 1 ∨ p ^ d % 8 = 7) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ d ∧
    ∃ e : sourceImage H M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      CentralizerOverlap H M K T ∧ 8 < Nat.card (sourceAutomizer H M K T) ∧
      (d = 2 → ∃ a ∈ sourceAutomizer H M K T, ¬ IsInnerFieldPSL2 (MulAut.congr e a))

/-- Case (2d), spelling out the sign: epsilon = +1 gives PSU₃(p), p = 1 mod 4;
epsilon = -1 gives PSL₃(p), p = 3 mod 4, with nontrivial diagram action. -/
def SingleOddRankThreeModel (H M K T : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ CentralizerOverlap H M K T ∧
    ((p % 4 = 1 ∧ ClassicalGroup.IsPSU (sourceImage H M K) 3 p) ∨
     (p % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
       ∃ e : sourceImage H M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
         MovesDiagram H M K T e (Matrix.PSL3.LinearThree.pointParabolic F)
           (Matrix.PSL3.LinearThree.lineParabolic F)))
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
