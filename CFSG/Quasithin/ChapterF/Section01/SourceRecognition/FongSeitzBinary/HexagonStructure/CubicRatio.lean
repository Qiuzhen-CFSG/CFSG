module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.CubicRatio
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.Irreducibility

/-!
# Full unequal-linear hexagon structure on the original quotient

Under the earlier actual local linear models and kernel inclusions, the
unequal exponents satisfy b=3a. The root-generated R_j itself is isomorphic
to SL2(F), with |F|=|E|³. All seven literal subgroup identities hold, and
R_j acts irreducibly on its actual radical abelianization, of binary
dimension 8a. The arbitrary marked-amalgam theorem covers the geometric
carrier; the SourceQuotient theorem uses the literal Q.q image of S.

The published triality StructuralRow and its irreducible source module
are supplied together with the cubic field ratio and actual rank-one
isomorphism. Compatible common/cubic field pinnings and the later mixed
polynomial equations remain with the triality source-relation owner.

This completes the unequal-linear branch from the stated earlier local
inputs, including q=2. It does not exclude Suzuki or unitary local groups,
prove the nonlinear/solvable effective-section reductions, or discharge
the earlier catalogue/transport premises of the full binary dichotomy.
No perfectness of either original local factor is imposed.

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

/-- The actual triality structural consumer with its cubic field ratio,
full rank-one group and irreducible radical action all established. -/
theorem triality_unequal_cubic_structure
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    letI := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    b = 3*a ∧ Nat.card F = (Nat.card E)^3 ∧
      Nonempty (rankOne Q split j ≃* SL(2,F)) ∧
      TrialitySource.StructuralRow Q split j i ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 8*a := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  have hcube := unequal_linear_cubic_ratio Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hcard : Nat.card F = (Nat.card E)^3 := by
    rw [hE,hF,hcube,←pow_mul,Nat.mul_comm a 3]
  obtain ⟨hrow,hirr,hdim⟩ := triality_unequal_structure_and_irreducible Q split hm i j hij
    hKi hKj μi μj ha hab hE hF
  refine ⟨hcube,hcard,⟨(GTwoSource.alignedPinning Q split j hKj μj sj).symm⟩,hrow,hirr,?_⟩
  rw [hdim,hcube]
  omega

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- The complete unequal-linear structural output on the original/geometric
Sylow image, retaining both literal right-conjugation words and actual R_j. -/
theorem marked_unequal_triality_structure
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
    let A := simpleRoot Q split i
    let B := rightConjugate (simpleRoot Q split j) (si.val : X ⧸ Q.D)
    let C := rightConjugate A (sj.val*si.val : Q.tits.N)
    let D := rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)
    let E₀ := rightConjugate A (sj.val : X ⧸ Q.D)
    b = 3*a ∧ Nat.card F = (Nat.card E)^3 ∧
      Nonempty (rankOne Q split j ≃* SL(2,F)) ∧
      ⁅V,V⁆ = C ∧ ⁅A,E₀⁆ = C ∧ ⁅B,D⁆ = C ∧
      ⁅A,C⁆ = ⊥ ∧ ⁅C,E₀⁆ = ⊥ ∧ ⁅A,D⁆ = ⊥ ∧ ⁅B,E₀⁆ = ⊥ ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 8*a := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  dsimp only
  obtain ⟨hcube,hcard,hR,_,hirr,hdim⟩ := triality_unequal_cubic_structure Q split hm i j hij
    hKi hKj μi μj ha hab hE hF
  obtain ⟨hder,hlong,hshort,hAC,hCE,hAD,hBE⟩ := marked_unequal_commutator_relations Q split e h
    hm i j hij hKi hKj μi μj ha hab hE hF
  exact ⟨hcube,hcard,hR,hder,hlong,hshort,hAC,hCE,hAD,hBE,hirr,hdim⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full unequal-linear branch for the literal original Q.q image of S. -/
theorem quotient_unequal_triality_structure
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
    let A := simpleRoot Q split i
    let B := rightConjugate (simpleRoot Q split j) (si.val : (generated L S) ⧸ Q.D)
    let C := rightConjugate A (sj.val*si.val : Q.tits.N)
    let D := rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)
    let E₀ := rightConjugate A (sj.val : (generated L S) ⧸ Q.D)
    b = 3*a ∧ Nat.card F = (Nat.card E)^3 ∧
      Nonempty (rankOne Q split j ≃* SL(2,F)) ∧
      ⁅V,V⁆ = C ∧ ⁅A,E₀⁆ = C ∧ ⁅B,D⁆ = C ∧
      ⁅A,C⁆ = ⊥ ∧ ⁅C,E₀⁆ = ⊥ ∧ ⁅A,D⁆ = ⊥ ∧ ⁅B,E₀⁆ = ⊥ ∧
      (radicalRepresentation Q split j hKj).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 8*a := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_unequal_triality_structure Q split (originalMarkedIso Q) h hm i j hij
    hKi hKj μi μj ha hab hE hF
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
