module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.Irreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedCommutators

/-!
# The unequal-linear irreducible action on the original source quotient

The actual radical abelianization now carries a proved irreducible binary
representation of the root-generated R_j, of dimension 2a+2b. The literal
original Sylow image gives the same radical; its relative center equals
the smaller middle root and [R_j,V_j]=V_j. The action formula retains the
source's right-conjugation convention on actual representatives. Arbitrary
marked-amalgam data include the universal/geometric carrier without any
universal-to-ambient descent assumption; the SourceQuotient application
retains the original Q.q image of S.

The triality application supplies both the existing StructuralRow and this
actual irreducible action. All earlier local models and kernel inclusions
remain explicit. No perfectness of an original factor is imposed, and the
binary opposite field, acting field four and exponent six are preserved.
The companion CubicRatio proves the field ratio. Full local-type exclusions
and nonlinear/solvable section arguments remain needed for the source dichotomy. This
module does not replace those obligations by a representation tag.

Source: Fong--Seitz I (6E)(b), printed pp.43--45; DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- The published triality structural row together with the actual irreducible
radical representation and its exact binary dimension. -/
theorem triality_unequal_structure_and_irreducible
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    letI := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    TrialitySource.StructuralRow Q split j i ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 2*a+2*b :=
  ⟨triality_structuralRow_of_unequal_linear Q split hm i j hij hKi hKj μi μj ha hab hE hF,
    unequal_linear_radical_irreducible Q split hm i j hij hKi hKj μi μj
      (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
      ha hab hE hF,
    unequal_linear_radical_finrank Q split hm i j hij hKi hKj μi μj
      (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
      ha hab hE hF⟩

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- The action is irreducible on the same radical as the original/geometric
Sylow image, with the exact center, full movement and right-conjugation formula. -/
theorem marked_unequal_irreducible_action
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    letI := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U (sj.val : X ⧸ Q.D)
    simpleRemainder Q split j = V ∧
      ⁅rankOne Q split j,V⁆ = V ∧
      V ⊓ centralizer (V : Set (X ⧸ Q.D)) =
        rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N) ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 2*a+2*b ∧
      ∀ (r : rankOne Q split j) (v v' : simpleRemainder Q split j),
        (v' : X ⧸ Q.D) = (r : X ⧸ Q.D)⁻¹*v*r →
        radicalRepresentation Q split j hKj r⁻¹ (Additive.ofMul (Abelianization.of v)) =
          Additive.ofMul (Abelianization.of v') := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [← marked_radical_eq h Q e split j sj.val sj.class_eq,
    ← rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul,sj.class_eq,si.class_eq])]
  exact ⟨rfl,
    unequal_linear_radical_fully_moved Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_radical_center Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_radical_irreducible Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_radical_finrank Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    radicalRepresentation_right_conjugation Q split j hKj⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal Q.q image of S supplies the same irreducible source action. -/
theorem quotient_unequal_irreducible_action
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    letI := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U (sj.val : (generated L S) ⧸ Q.D)
    simpleRemainder Q split j = V ∧
      ⁅rankOne Q split j,V⁆ = V ∧
      V ⊓ centralizer (V : Set ((generated L S) ⧸ Q.D)) =
        rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N) ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 2*a+2*b ∧
      ∀ (r : rankOne Q split j) (v v' : simpleRemainder Q split j),
        (v' : (generated L S) ⧸ Q.D) = (r : (generated L S) ⧸ Q.D)⁻¹*v*r →
        radicalRepresentation Q split j hKj r⁻¹ (Additive.ofMul (Abelianization.of v)) =
          Additive.ofMul (Abelianization.of v') := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_unequal_irreducible_action Q split (originalMarkedIso Q) h hm i j hij
    hKi hKj μi μj ha hab hE hF
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
