module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.LocalActions

/-!
# Original and geometric linear-hexagon structure applications

The original S image gives exactly the canonical root and radical
intersections. Its radical has the five source factors in the literal
right-conjugation order. A marking of the actual source L_i by binary
PSL2 supplies elementary simple roots, the nontrivial derived subgroup
inside the three middle roots, and the actual binary radical quotient
representation. Its source reflection acts nontrivially. The action formula
uses original S representatives and the same finite quotient, also when
the numerator is the infinite universal completion.

Source: Fong--Seitz I (3G), (5C)--(5F) and the initial argument in (6E),
printed pp.14--16,26--28,44--45; DGS Theorem D, printed p.224.
The actual local-model markings, reflection witnesses and radical-kernel
inclusions remain earlier source inputs. The Suzuki and unitary exclusions,
the unequal-parameter commutator equalities and irreducibility still need
proof. The eventual full structural outputs are intended for GTwoSource
and TrialitySource; these partial statements do not supply either complete
6E branch and do not assume its later pinning or presentation relations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- The source simple root is the canonical intersection of the same original S image. -/
theorem marked_simpleRoot_eq (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      longest Q*Q.simple i) :
    simpleRoot Q split i = (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) := by
  rw [MarkedLocal.sylow_range Q e h split, simpleRoot, rootIntersection,
    unipotentConjugate_eq split _ n hn]

/-- The five source roots multiply to the literal original radical, with the
right-conjugation words and either endpoint orientation retained. -/
theorem marked_radical_five_product (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : ∀ k, RootReflection Q split k) :
    let U := (MarkedLocal.sylowMap Q e h).range
    (U ⊓ rightConjugate U ((s j).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split j) ((s i).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split i) ((s j).val*(s i).val : Q.tits.N) : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split j) ((s i).val*(s j).val : Q.tits.N) : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split i) ((s j).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) := by
  dsimp only
  change (( (MarkedLocal.sylowMap Q e h).range ⊓
    rightConjugate (MarkedLocal.sylowMap Q e h).range ((s j).val : X ⧸ Q.D) :
      Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) = _
  rw [← marked_radical_eq h Q e split j (s j).val (s j).class_eq,
    radical_five_product Q split hm i j hij,
    rootAt_eq Q split j (Q.simple i) (s i).val (s i).class_eq,
    rootAt_eq Q split i (Q.simple j*Q.simple i) ((s j).val*(s i).val)
      (by rw [map_mul, (s j).class_eq, (s i).class_eq]),
    rootAt_eq Q split j (Q.simple i*Q.simple j) ((s i).val*(s j).val)
      (by rw [map_mul, (s i).class_eq, (s j).class_eq]),
    rootAt_eq Q split i (Q.simple j) (s j).val (s j).class_eq]

/-- A marking of the actual source local group supplies the initial 6E bound
and the nontrivial derived subgroup on the literal original radical. -/
theorem marked_linear_radical_commutator {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : ∀ k, RootReflection Q split k)
    (hK : (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range ((s i).val : X ⧸ Q.D) ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U ((s j).val : X ⧸ Q.D)
    ⁅V,V⁆ ≠ ⊥ ∧ ⁅V,V⁆ ≤
      rightConjugate (simpleRoot Q split j) ((s i).val : X ⧸ Q.D) ⊔
      rightConjugate (simpleRoot Q split i) ((s j).val*(s i).val : Q.tits.N) ⊔
      rightConjugate (simpleRoot Q split j) ((s i).val*(s j).val : Q.tits.N) := by
  dsimp only
  rw [← marked_radical_eq h Q e split j (s j).val (s j).class_eq]
  refine ⟨radical_commutator_ne_bot Q split hm i j hij (s i),?_⟩
  have hKi : simpleRemainder Q split i ≤ localKernel Q i :=
    (marked_radical_eq h Q e split i (s i).val (s i).class_eq).symm ▸ hK
  have hh := radical_commutator_le_middle_of_linear Q split hm i j hij hKi μ
  rwa [middleRoots,
    rootAt_eq Q split j (Q.simple i) (s i).val (s i).class_eq,
    rootAt_eq Q split i (Q.simple j*Q.simple i) ((s j).val*(s i).val)
      (by rw [map_mul, (s j).class_eq, (s i).class_eq]),
    rootAt_eq Q split j (Q.simple i*Q.simple j) ((s i).val*(s j).val)
      (by rw [map_mul, (s i).class_eq, (s j).class_eq])] at hh

variable {F : Fin 2 → Type*} [∀ i, Field (F i)] [∀ i, Finite (F i)] [∀ i, CharP (F i) 2]
  (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F i))

include hm μ in
/-- The scalar premise for the actual radical quotient follows from the two
actual local PSL2 markings, without restricting either field size. -/
theorem source_linear_radicalQuotient_elementary (j : Fin 2) :
    IsElementaryAbelian 2 (RadicalQuotient Q split j) :=
  radicalQuotient_elementary Q split hm
    (fun i => simpleRoot_elementary_of_linear Q split i (μ i)) j

/-- The resulting representation acts on the original S representatives by
literal right conjugation in the same quotient; this also applies to the
universal/geometric marking, without a universal-to-ambient descent. -/
theorem marked_linear_radical_action (h : HypothesisF11 L S) (j : Fin 2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (r : rankOne Q split j) (x y : S)
    (hx : MarkedLocal.sylowMap Q e h x ∈ simpleRemainder Q split j)
    (hy : MarkedLocal.sylowMap Q e h y ∈ simpleRemainder Q split j)
    (hxy : MarkedLocal.sylowMap Q e h y =
      (r : X ⧸ Q.D)⁻¹*MarkedLocal.sylowMap Q e h x*(r : X ⧸ Q.D)) :
    let := source_linear_radicalQuotient_elementary Q split hm μ j
    radicalRepresentation Q split j hK r⁻¹
      (Additive.ofMul (Abelianization.of ⟨MarkedLocal.sylowMap Q e h x,hx⟩)) =
      Additive.ofMul (Abelianization.of ⟨MarkedLocal.sylowMap Q e h y,hy⟩) := by
  let := source_linear_radicalQuotient_elementary Q split hm μ j
  exact radicalRepresentation_right_conjugation Q split j hK r _ _ hxy

/-- In the source linear branch the actual source reflection moves the actual
binary radical module. This is a nontrivial-action conclusion, not an
irreducibility assertion. -/
theorem source_linear_reflection_moves (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j) :
    letI := source_linear_radicalQuotient_elementary Q split hm μ j
    radicalRepresentation Q split j hKj ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  let := source_linear_radicalQuotient_elementary Q split hm μ j
  exact radicalRepresentation_reflection_ne_one Q split hm i j hij hKi hKj
    (simpleRoot_commutator_eq_bot_of_linear Q split i (μ i)) s

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same commutator bound and nontriviality under the literal original
quotient map Q.q. The faithful local group, roots and orientation are unchanged. -/
theorem quotient_linear_radical_commutator {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : ∀ k, RootReflection Q split k)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U ((s j).val : (generated L S) ⧸ Q.D)
    ⁅V,V⁆ ≠ ⊥ ∧ ⁅V,V⁆ ≤ middleRoots Q split i j := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ← unipotentConjugate_eq split (Q.simple j) (s j).val (s j).class_eq]
  exact ⟨radical_commutator_ne_bot Q split hm i j hij (s i),
    radical_commutator_le_middle_of_linear Q split hm i j hij hK μ⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
