module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.EqualLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NormalGeneration

/-!
# Equal-linear quadrangle input for the original C2 consumer

Apply the DGS b=1 root orders and elementary-core commutator theorem to
the exact kernelRoot used by the C2 rank-three development. The conclusion
also holds for a coherent simple reflection lying inside its root-generated
rank-one subgroup. At rotation order four the actual unipotent group has
order q^4, and its two complementary sections are elementary of order q^3.

The existing full-group normal-subgroup theorem now receives both root
orders and normal generation from the same original markings. Its later
recognized subgroup remains explicit. The original-source specialization
uses the literal quotient image of S. All marked statements also apply to
an independently marked geometric quotient, without an ambient descent.

This supplies commuting and order inputs for (6A)(a), including q=2.
It does not yet identify the two faithful rank-one groups or carry out the
subsequent rank-three geometry and projective reconstruction.
Source: DGS (10.5), pp.156--157; Fong--Seitz I (6A)(a), pp.37--38,
and II (7C), (8A). Earlier action and local-kernel inputs retain their
source producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open DGS85.NoncommutingProfile DGS85.Reduction Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S)
      (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S)
      (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)

include e h c₀ c₁


/-- The exact kernel root used by the C2 consumer commutes with U_2. -/
theorem marked_bOne_kernelRoot_commutator (split : SplitData Q.tits)
    (hV : simpleRemainder Q split 0 ≤ localKernel Q 0) :
    ⁅simpleRoot Q split 1, C2RankThree.kernelRoot Q split⁆ = ⊥ :=
  marked_bOne_root_commutator Q e h c₀ c₁ split 1 0 (by decide) hV

/-- The same conclusion uses any coherent source reflection chosen inside R_1. -/
theorem marked_bOne_rootReflection_commutator (split : SplitData Q.tits)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j) :
    ⁅simpleRoot Q split i, rightConjugate (simpleRoot Q split i)
      (s.val : X ⧸ Q.D)⁆ = ⊥ := by
  let := marked_bOne_core_elementary Q e h c₀ c₁ j
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.root_commutator_eq_bot_of_abelian_core_lift
    Q split i j hij hV inferInstance s.val s.class_eq

variable (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include hactor₀ hactor₁


/-- The q^4 Sylow order needed by full Sp4 recognition is derived from the actual DGS profile. -/
theorem marked_bOne_unipotent_card (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    Nat.card split.U = Nat.card k₀ ^ 4 :=
  C2RankThree.unipotent_card Q split hm
    (marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split 0)
    (marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split 1)

/-- The actual complementary section has order q^3 and is elementary abelian. -/
theorem marked_bOne_remainder_structure (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    IsElementaryAbelian 2 (simpleRemainder Q split i) ∧
      Nat.card (simpleRemainder Q split i) = Nat.card k₀ ^ 3 := by
  have hcore := marked_bOne_core_elementary Q e h c₀ c₁ i
  have hR := marked_remainder_eq_core Q e h split i hV
  refine ⟨hR.symm ▸ hcore, ?_⟩
  have hc := unipotent_card_simple Q split i
  rw [marked_bOne_unipotent_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split hm,
    marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split i] at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := k₀))
  exact hc.symm.trans (by ring)

/-- The existing full-group consumer now takes its root orders and normal generation
from the same original markings. The later recognized subgroup remains its input. -/
theorem marked_bOne_normal_eq_top (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (K V : Subgroup (X ⧸ Q.D)) [K.Normal]
    (hVK : V ≤ K) (hcard : Nat.card V = Nat.card k₀ ^ 4) : K = ⊤ :=
  SymplecticRankThree.marked_normal_eq_top Q split hm
    (marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split 0)
    (marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split 1)
    (A2Source.unipotent_normalClosure_eq_top Q e h split) K V hVK hcard

omit Q e in
/-- Literal original-source application: the original S image has order q^4
and the exact C2 kernel root commutes. Both source endpoints are retained. -/
theorem original_bOne_c2_data (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4)
    (hV : simpleRemainder Q₀ split₀ 0 ≤ localKernel Q₀ 0) :
    (∀ i, Nat.card (simpleRoot Q₀ split₀ i) = Nat.card k₀) ∧
      ⁅simpleRoot Q₀ split₀ 1, C2RankThree.kernelRoot Q₀ split₀⁆ = ⊥ ∧
      Nat.card ((S.subgroupOf (generated L S)).map Q₀.q) = Nat.card k₀ ^ 4 := by
  refine ⟨fun i => marked_bOne_simpleRoot_card Q₀ (originalMarkedIso Q₀)
    h c₀ c₁ hactor₀ hactor₁ E₀ split₀ i,
    marked_bOne_kernelRoot_commutator Q₀ (originalMarkedIso Q₀) h c₀ c₁ split₀ hV, ?_⟩
  rw [quotient_sourceS_image_eq_unipotent h Q₀ split₀]
  exact marked_bOne_unipotent_card Q₀ (originalMarkedIso Q₀)
    h c₀ c₁ hactor₀ hactor₁ E₀ split₀ hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
