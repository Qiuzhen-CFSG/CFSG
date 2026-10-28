module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiNaturalPlacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiDerivedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiCartanProduct

/-!
# Natural Suzuki factor placement on the original source quotient

The original F.1.1 markings construct the actual rank-one and root
isomorphisms, the local-kernel containments, and the core-free Borel. After
synchronizing the positive Suzuki parameters, the natural module is realized
as an equivariant quotient of an actual subgroup of the derived radical.
Its kernel lies in the literal middle root; its numerator is exactly the
four nonmiddle root Frattini subgroups followed by that kernel.

These applications preserve arbitrary original/geometric markings and the
literal Q.q image of S, without original-factor perfectness. The supplied
split structure and rotation-six premise retain their earlier source producers
and final discharge in source assembly. Source: Fong--Seitz I (6C), p.41.
The triple-commutator contradiction and the inherited small, unitary and
exhaustive (6E) branches are still required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The natural factor and its exact source placement for any original or
geometric marked amalgam. -/
theorem original_suzuki_natural_placement (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∃ (μ : rankOne Q split j ≃* SuzukiMatrixGroup n) (A : Subgroup (X ⧸ Q.D)),
      A ≤ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ∧
      ∃ (hRA : rankOne Q split j ≤ normalizer (A : Set (X ⧸ Q.D)))
        (f : A →* Multiplicative (Representation.SuzukiNatural.W n)),
        Function.Surjective f ∧
        f.ker.map A.subtype ≤ rootAt Q split i (Q.simple j*Q.simple i) ∧
        (A : Set (X ⧸ Q.D)) = naturalRootProduct Q split i j (f.ker.map A.subtype) ∧
        ∀ (r : rankOne Q split j) (a : A),
          (f (A.normalizerMonoidHom (inclusion hRA r) a)).toAdd =
            Representation.SuzukiNatural.natural n (μ r) (f a).toAdd := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  refine ⟨suzukiAllRankOneEquiv Q e h split j Tj hTj μj,?_⟩
  exact suzuki_derived_natural_placement Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

/-- The same natural section is a subquotient of the derived radical of
the marked Sylow image, using the literal right-conjugation reflection. -/
theorem marked_suzuki_natural_placement (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    ∃ (μ : rankOne Q split j ≃* SuzukiMatrixGroup n) (A : Subgroup (X ⧸ Q.D)),
      A ≤ ⁅V,V⁆ ∧
      ∃ (hRA : rankOne Q split j ≤ normalizer (A : Set (X ⧸ Q.D)))
        (f : A →* Multiplicative (Representation.SuzukiNatural.W n)),
        Function.Surjective f ∧
        f.ker.map A.subtype ≤ rootAt Q split i (Q.simple j*Q.simple i) ∧
        (A : Set (X ⧸ Q.D)) = naturalRootProduct Q split i j (f.ker.map A.subtype) ∧
        ∀ (r : rankOne Q split j) (a : A),
          (f (A.normalizerMonoidHom (inclusion hRA r) a)).toAdd =
            Representation.SuzukiNatural.natural n (μ r) (f a).toAdd := by
  dsimp only
  rw [←marked_radical_eq h Q e split j
    (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact original_suzuki_natural_placement Q e h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- Exact natural-factor placement for the original source quotient Q.q. -/
theorem quotient_suzuki_natural_placement (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    ∃ (μ : rankOne Q split j ≃* SuzukiMatrixGroup n) (A : Subgroup ((generated L S) ⧸ Q.D)),
      A ≤ ⁅V,V⁆ ∧
      ∃ (hRA : rankOne Q split j ≤ normalizer (A : Set ((generated L S) ⧸ Q.D)))
        (f : A →* Multiplicative (Representation.SuzukiNatural.W n)),
        Function.Surjective f ∧
        f.ker.map A.subtype ≤ rootAt Q split i (Q.simple j*Q.simple i) ∧
        (A : Set ((generated L S) ⧸ Q.D)) = naturalRootProduct Q split i j (f.ker.map A.subtype) ∧
        ∀ (r : rankOne Q split j) (a : A),
          (f (A.normalizerMonoidHom (inclusion hRA r) a)).toAdd =
            Representation.SuzukiNatural.natural n (μ r) (f a).toAdd := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_suzuki_natural_placement Q (originalMarkedIso Q) h split
    hhex i j hij hm hn μi μj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
