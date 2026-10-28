module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.SymplecticFour.Flag
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.CComponent.Basic
public import CFSG.Quasithin.ClassicalModels

/-!
# Marked source alternatives for E.6.27

The full E.2.2 contract retains all six alternatives, actual component/Borel
isomorphisms, automizer and diagram clauses, and exact generation values.
The kernel is the normal core of the unique maximal subgroup. Its quotient
is kept distinct from the two-core quotient, including the source center
identity. Genuine SQTK hypotheses retain both strong quasithinness and K.

E.1.13 and E.2.2 are explicit earlier-source implications; neither contains
Cartan existence, Hall abelianness, solvability of the maximal subgroup, or
the desired construction. Their application reduces n(X) > 1 to the three
characteristic-two branches, whose Hall construction remains to be proved.

The concrete markings adapt the independently meaningful definitions in
Chapter15/Section03/AbelianAmalgam/WeakClosureBounds/GenerationOne/
BorelReduction/SourceCases/Models.lean without importing that later chapter.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.1.13 and
E.2.2, printed pp.214--216; E.6.27, p.257.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Subgroup BenderSuzuki.MatrixGroups ChapterB
open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- The literal source kernel J = core_X(M). -/
abbrev sourceKernel (M : Subgroup G) : Subgroup G := M.normalCore

/-- Images in X/J, distinct from images in X/O₂(X). -/
def sourceImage (M L : Subgroup G) : Subgroup (G ⧸ sourceKernel M) :=
  L.map (QuotientGroup.mk' (sourceKernel M))

/-- Images in the quotient by the two-core; central extensions are retained. -/
def actorImage (L : Subgroup G) : Subgroup (G ⧸ pCore 2 G) :=
  L.map (QuotientGroup.mk' (pCore 2 G))

/-- The actual overlap inside the component image in H/J. -/
abbrev componentOverlap (M K : Subgroup G) :=
  (sourceImage M (M ⊓ K)).subgroupOf (sourceImage M K)

/-- Recognition of the component and its Borel by the same isomorphism. -/
def ModelBorelPair (M K : Subgroup G) {X : Type*} [Group X] (B : Subgroup X) : Prop :=
  ∃ e : sourceImage M K ≃* X, (componentOverlap M K).map e.toMonoidHom = B

/-- Aut_T(K*) uses the normalizing elements of T*, including in the exchanged case. -/
def sourceAutomizer (M K T : Subgroup G) : Subgroup (MulAut (sourceImage M K)) :=
  ((sourceImage M T).subgroupOf (normalizer (sourceImage M K : Set _))).map
    (sourceImage M K).normalizerMonoidHom

/-- The source centralizer C_{K*}(Z((T ∩ K)*)), internal to K*. -/
def CentralizerOverlap (M K T : Subgroup G) : Prop :=
  componentOverlap M K = centralizer
    (((center ((sourceImage M (T ⊓ K)).subgroupOf (sourceImage M K))).map
      ((sourceImage M (T ⊓ K)).subgroupOf (sourceImage M K)).subtype :
        Subgroup (sourceImage M K)) : Set _)

/-- Parabolic conjugacy classes give an intrinsic meaning to the diagram clause. -/
def PreservesParabolicClass {X : Type*} [Group X] (a : MulAut X) (P : Subgroup X) : Prop :=
  ∃ g : X, P.map a.toMonoidHom = P.map (MulAut.conj g).toMonoidHom

/-- Some actual T-induced automorphism moves one of the two diagram vertices. -/
def MovesDiagram (M K T : Subgroup G) {X : Type*} [Group X]
    (e : sourceImage M K ≃* X) (P Q : Subgroup X) : Prop :=
  ∃ a ∈ sourceAutomizer M K T,
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
def ExchangedModel (M K : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    2 ≤ f ∧ Nat.card F = 2 ^ f ∧ ModelBorelPair M K (BenderSuzuki.Converse.PBorel F)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
    ModelBorelPair M K (SuzukiBorelSubgroup m))

/-- The remaining Bender family, PSU₃(2^f), over a matrix field of order 2^(2f). -/
def UnitaryModel (M K : Subgroup G) (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
    2 ≤ f ∧ Nat.card F = (2 ^ f) ^ 2 ∧
    (∀ x, J.conj x = x ^ (2 ^ f)) ∧
    Nat.card {x : F // J.conj x = x} = 2 ^ f ∧
    ModelBorelPair M K (unitaryBorel J hJ)

/-- All three simple Bender families, with their Borel pairs. -/
def BenderModel (M K : Subgroup G) (f : ℕ) : Prop :=
  ExchangedModel M K f ∨ UnitaryModel M K f

/-- The two rank-two cases, including the actual induced diagram action.
No parity of f and no replacement of PSL₃ by SL₃ is made here. -/
def DiagramModel (M K T : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
      (componentOverlap M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F ∧
      MovesDiagram M K T e (Matrix.PSL3.LinearThree.pointParabolic F)
        (Matrix.PSL3.LinearThree.lineParabolic F)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage M K ≃* Sp4Derived F,
      (componentOverlap M K).map e.toMonoidHom = sp4DerivedBorel F ∧
      MovesDiagram M K T e
        ((Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)).subgroupOf (Sp4Derived F))
        ((Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)).subgroupOf (Sp4Derived F)))

/-- Case (1b), with p prime, the mod-eight condition, and the automizer bound. -/
def ExchangedOddModel (M K T : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧
    ClassicalGroup.IsPSL (sourceImage M K) 2 p ∧
    CentralizerOverlap M K T ∧ 8 < Nat.card (sourceAutomizer M K T)

/-- Case (2c). At exponent two the induced automizer is not contained in
inner-field automorphisms; the witness uses the same recognition map. -/
def SingleOddLinearModel (M K T : Subgroup G) : Prop :=
  ∃ p d : ℕ, p.Prime ∧ 3 < p ∧ 0 < d ∧ d ≤ 2 ∧
    (p ^ d % 8 = 1 ∨ p ^ d % 8 = 7) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ d ∧
    ∃ e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      CentralizerOverlap M K T ∧ 8 < Nat.card (sourceAutomizer M K T) ∧
      (d = 2 → ∃ a ∈ sourceAutomizer M K T, ¬ IsInnerFieldPSL2 (MulAut.congr e a))

/-- Case (2d), spelling out the sign: epsilon = +1 gives PSU₃(p), p = 1 mod 4;
epsilon = -1 gives PSL₃(p), p = 3 mod 4, with nontrivial diagram action. -/
def SingleOddRankThreeModel (M K T : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ CentralizerOverlap M K T ∧
    ((p % 4 = 1 ∧ ClassicalGroup.IsPSU (sourceImage M K) 3 p) ∨
     (p % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
       ∃ e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
         MovesDiagram M K T e (Matrix.PSL3.LinearThree.pointParabolic F)
           (Matrix.PSL3.LinearThree.lineParabolic F)))

/-- E.2.2(1), with the source right-conjugation convention. -/
structure ExchangedClauses (M K T : Subgroup G) : Prop where
  kernel_eq : sourceKernel M = pCore 2 G
  exchanged_product : ∃ t ∈ T, K ≠ K.conjBy t⁻¹ ∧
    (M : Set G) = (M ⊓ K : Subgroup G) *
      (((M ⊓ K).conjBy t⁻¹ : Subgroup G) : Set G) * (T : Set G)

/-- E.2.2(2). The center equality is in X/O₂(X), not in X/J. -/
structure SingleClauses (M K T : Subgroup G) : Prop where
  product : (Set.univ : Set G) = (K : Set G) * (T : Set G)
  kernel_center : (sourceKernel M).map (QuotientGroup.mk' (pCore 2 G)) =
    (center (actorImage K)).map (actorImage K).subtype

variable [Finite G]

/-- All six alternatives, including their exact generation values. -/
inductive FullAlternatives (M K T : Subgroup G) : Prop
  | oneA (f : ℕ) : ExchangedClauses M K T → ExchangedModel M K f →
      generationParameter G = f → FullAlternatives M K T
  | oneB : ExchangedClauses M K T → ExchangedOddModel M K T →
      generationParameter G = 1 → FullAlternatives M K T
  | twoA (f : ℕ) : SingleClauses M K T → BenderModel M K f →
      generationParameter G = f → FullAlternatives M K T
  | twoB (f : ℕ) : SingleClauses M K T → DiagramModel M K T f →
      generationParameter G = f → FullAlternatives M K T
  | twoC : SingleClauses M K T → SingleOddLinearModel M K T →
      generationParameter G = 1 → FullAlternatives M K T
  | twoD : SingleClauses M K T → SingleOddRankThreeModel M K T →
      generationParameter G = 1 → FullAlternatives M K T

/-- The full E.2.2 conclusion on the original parabolic carrier. -/
def FullE22Conclusion (Kc : GroupClass.{u}) (M T : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K.IsCComponent ∧
    Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) ∧
    (⊤ : Subgroup G) = K ⊔ T ∧ IsSQTK Kc (G ⧸ sourceKernel M) ∧
    FullAlternatives M K T

/-- Exact earlier-source implication E.1.13, without Cartan output. -/
def SourceE113 (X : Type u) [Group X] [Finite X] : Prop :=
  Group.IsSolvable X → generationParameter X ≤ 1

/-- Earlier-source implication E.2.2. The assembly instantiates Kc with the
full known-simple class; there is no theorem here for arbitrary class labels.
Neither Cartan existence nor Hall abelianness nor maximal solvability is an
input field of this source implication. -/
def SourceE22 (Kc : GroupClass.{u}) (X : Type u) [Group X] [Finite X] : Prop :=
  IsSQTK Kc X → ∀ (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤),
    ¬ Group.IsSolvable X → FullE22Conclusion Kc (minimalParabolicMax S hP) S

/-- The three genuine characteristic-two branches, with the central kernel
and diagram action unchanged. -/
inductive ReducedCases (M K T : Subgroup G) (f : ℕ) : Prop
  | exchanged : ExchangedClauses M K T → ExchangedModel M K f → ReducedCases M K T f
  | bender : SingleClauses M K T → BenderModel M K f → ReducedCases M K T f
  | diagram : SingleClauses M K T → DiagramModel M K T f → ReducedCases M K T f

/-- The numerical clauses exclude precisely the characteristic-odd branches. -/
theorem FullAlternatives.reduce {M K T : Subgroup G}
    (h : FullAlternatives M K T) (hn : 1 < generationParameter G) :
    ReducedCases M K T (generationParameter G) := by
  cases h with
  | oneA f hc hm he => exact he ▸ ReducedCases.exchanged hc hm
  | oneB _ _ he => omega
  | twoA f hc hm he => exact he ▸ ReducedCases.bender hc hm
  | twoB f hc hm he => exact he ▸ ReducedCases.diagram hc hm
  | twoC _ _ he => omega
  | twoD _ _ he => omega

/-- Actual source application, including E.1.13's nonsolvability deduction.
This is a reduction to model branches, not the Hall–Cartan construction. -/
theorem reduced_of_source {Kc : GroupClass.{u}} (hX : IsSQTK Kc G)
    (h113 : SourceE113 G) (h22 : SourceE22 Kc G)
    (S : Sylow 2 G) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter G) :
    ∃ K : Subgroup G, K.IsCComponent ∧
      Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) ∧
      (⊤ : Subgroup G) = K ⊔ (S : Subgroup G) ∧
      IsSQTK Kc (G ⧸ sourceKernel (minimalParabolicMax S hP)) ∧
      ReducedCases (minimalParabolicMax S hP) K S (generationParameter G) := by
  obtain ⟨K, hK, hqs, hgen, hquot, hc⟩ := h22 hX S hP (fun hs => (h113 hs).not_gt hn)
  exact ⟨K, hK, hqs, hgen, hquot, hc.reduce hn⟩

omit [Finite G] in
/-- The comparison X/O₂(X) → X/J has the required kernel containment. -/
theorem twoCore_le_sourceKernel (S : Sylow 2 G) (hP : IsMinimalParabolicOver S ⊤) :
    pCore 2 G ≤ sourceKernel (minimalParabolicMax S hP) := by
  exact normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal S).trans (minimalParabolicMax_spec S hP).2)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
