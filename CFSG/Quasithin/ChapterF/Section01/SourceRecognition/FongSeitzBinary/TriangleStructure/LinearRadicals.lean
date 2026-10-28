module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddLinearFactors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleStructure.Radicals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearIrreducibility
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RankOneFaithfulness

/-!
# Original elementary triangle cores and their irreducible actions

One original linear factor on a split triangle forces both factors to have
the same binary degree. The two-root radical calculation proves both
radicals elementary of order q². Transport through the actual endpoint
maps gives the same conclusions for the original full parabolic two-cores,
including the binary field and either orientation.

For degree greater than one, the original factor identifies the full
root-generated actor with SL2(q). Its reflection moves the opposite root,
and the minimum binary degree bound makes its action on the q² radical
irreducible. Core elementarity, core order and irreducibility are outputs.
Natural coordinates and the final full A₂ comparison remain obligations.

Source: Fong--Seitz I (3E), (4B), pp.15,19--22; DGS, Groups and Graphs,
(10.5) and Theorem D, pp.156,224. Chapter12 applies these constructions
to the literal original prepared pair with full KnownSimple/proper-K scope.
-/

public noncomputable section
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split in
/-- The same original linear degree occurs at every endpoint of the triangle. -/
theorem original_linear_factors (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2) :
    ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) := by
  by_cases he : i = j
  · exact he ▸ hi
  · exact odd_linear_factors_same_degree Q e h split (hm ▸ (by decide : Odd 3)) i j he hi

include e h split in
/-- Both actual radicals are elementary, with no core-elementarity premise. -/
theorem original_remainders_elementary (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2) :
    IsElementaryAbelian 2 (simpleRemainder Q split j) := by
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_elementary
    Q split hm (fun k => (odd_linear_regularity Q e h split
      (hm ▸ (by decide : Odd 3)) i hi k).1)
    (fun k => elementary_root_of_linear_factor Q e h split k
      (original_linear_factors Q e h split hm i hi k)) j

include e h split in
/-- Transport elementarity and the exact square order to both original full
parabolic cores through their unchanged endpoint maps. -/
theorem original_cores_elementary_order (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2) :
    IsElementaryAbelian 2 ((parabolic L S j).pCoreIn 2) ∧
      Nat.card ((parabolic L S j).pCoreIn 2) = 2^(2*n) := by
  have hreg := odd_linear_regularity Q e h split (hm ▸ (by decide : Odd 3)) i hi j
  let := original_remainders_elementary Q e h split hm i hi j
  have hf : Function.Injective (endpointMap Q e j) :=
    (Q.tits.standardParabolic {Q.simple j}).subtype_injective.comp (endpoint Q e j).injective
  have hE := IsElementaryAbelian.comap_of_injective (p := 2) (endpointMap Q e j) hf
    (simpleRemainder Q split j)
  rw [hreg.2] at hE
  let := hE
  refine ⟨IsElementaryAbelian.map _,?_⟩
  rw [←QuadrangleStructure.marked_remainder_card Q e h split j hreg.1,
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_card Q split hm j]
  have hj := original_linear_factors Q e h split hm i hi j
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hj
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rw [simpleRoot_card_linear Q e h split j T hT μ,hcard,←pow_mul,Nat.mul_comm n 2]

include e h split in
/-- Above the binary field, the actual radical is an irreducible module
for its full root-generated actor. The original factor supplies the actor
identification, and the triangle proves the elementary square order. -/
theorem original_radical_irreducible (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ} (hn : 1 < n)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2) :
    let hV := (odd_linear_regularity Q e h split (hm ▸ (by decide : Odd 3)) i hi j).1
    letI := original_remainders_elementary Q e h split hm i hi j
    (Representation.elementaryRepresentation (p := 2) (radicalAction Q split j hV)).IsIrreducible := by
  dsimp only
  let hV := (odd_linear_regularity Q e h split (hm ▸ (by decide : Odd 3)) i hi j).1
  let := original_remainders_elementary Q e h split hm i hi j
  have hj := original_linear_factors Q e h split hm i hi j
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hj
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨f,hf,hk,_⟩ := linear_actor_quotient_of_factor Q e h split j μ
  let A := (S ⊔ L j).subgroupOf (parabolic L S j)
  let : A.Normal := QuadrangleStructure.marked_sylow_factor_normal Q e h split j
  obtain ⟨_,ν,_,_⟩ := QuadrangleStructure.marked_linear_localGroup Q e h split j
    (UnitarySource.actorReflection Q split j) hV A (subgroupOf_mono _ le_sup_left) f hf hk
  apply Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.minimal_linear_action_irreducible
    (GTwoSource.rankOneLinearEquiv Q split j hV ν) (radicalAction Q split j hV)
    (Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radicalAction_nontrivial Q split hm j hV)
    hn hcard
  rw [Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_card Q split hm j,
    GTwoSource.simpleRoot_card Q split j hV ν]
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
