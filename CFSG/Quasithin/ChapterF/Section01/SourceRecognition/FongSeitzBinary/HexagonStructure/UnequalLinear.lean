module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.EffectiveSections

/-!
# Unequal linear hexagon radicals on the original marking

Apply the non-invariance and strict commutator containment of Fong--Seitz I
(6E), printed p.44, to the same original Sylow image, the same finite marked
quotient, and both literal endpoint orientations. The general marking covers
the universal/geometric carrier without a descent to the ambient completion.

The original-factor application discharges local-kernel inclusions and the
acting linear local marking using the proved original identification. Only
that identification requires the acting original factor to be perfect; the
marking-level theorem has no such premise and includes a binary opposite
endpoint. These are intermediate structural consequences: the nonlinear
exclusions, torus isolation of the middle root, mixed commutator equalities
and irreducibility remain needed by GTwoSource and TrialitySource.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- The actual geometric radical and literal right-conjugation words satisfy
strict containment; this is not a field-size-only alternative. -/
theorem marked_unequal_linear_middle
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U (sj.val : X ⧸ Q.D)
    let M := rightConjugate (simpleRoot Q split j) (si.val : X ⧸ Q.D) ⊔
      rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N) ⊔
      rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)
    ¬ rankOne Q split j ≤ normalizer (M : Set _) ∧ ⊥ < ⁅V,V⁆ ∧ ⁅V,V⁆ < M := by
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [← marked_radical_eq h Q e split j sj.val sj.class_eq]
  have hh := unequal_linear_middle_structure Q split j hKj μj sj
    hm i hij hKi μi si ha hab hE hF
  rwa [middleRoots,
    rootAt_eq Q split j (Q.simple i) si.val si.class_eq,
    rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul, sj.class_eq, si.class_eq]),
    rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul, si.class_eq, sj.class_eq])] at hh

/-- Original linear factors discharge the exact earlier local-model and kernel
premises. The abelianness of the opposite canonical root remains an explicit
earlier local-type input; the opposite original factor need not be perfect. -/
theorem unequal_middle_of_original_linear_factors
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    (hAi : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    ¬ rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) ∧
      ⊥ < ⁅V,V⁆ ∧ ⁅V,V⁆ < middleRoots Q split i j := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  dsimp only
  rw [← marked_radical_eq h Q e split j
    (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  have hKi := MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi
  have hKj := MarkedLocal.linear_remainder_le_kernel Q e h split j Tj hTj μj
  let μ := MarkedLocal.linearLocalEquiv Q e h split j hpj Tj hTj μj
  let sj := UnitarySource.actorReflection Q split j
  have hsmall : Nat.card (simpleRoot Q split i) < Nat.card F := by
    rw [MarkedLocal.simpleRoot_card_linear Q e h split i Ti hTi μi, hE, hF]
    exact Nat.pow_lt_pow_right (by decide) hab
  exact ⟨rankOne_not_normalizes_middle Q split j hKj μ sj hm i hij hKi hAi (by omega) hF hsmall,
    bot_lt_iff_ne_bot.mpr (radical_commutator_ne_bot Q split hm i j hij
      (UnitarySource.actorReflection Q split i)),
    radical_commutator_lt_middle Q split j hKj μ sj hm i hij hKi hAi (by omega) hF hsmall⟩

/-- The smallest opposite endpoint needs no perfectness or extra abelian-root
premise: its literal root has order two by the original panel count. -/
theorem binary_opposite_middle_of_original_factors
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    {b : ℕ} (hb : 1 < b) (hE : Nat.card E = 2) (hF : Nat.card F = 2^b) :
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    ¬ rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) ∧
      ⊥ < ⁅V,V⁆ ∧ ⁅V,V⁆ < middleRoots Q split i j := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  have hc : Nat.card (simpleRoot Q split i) = 2 :=
    (MarkedLocal.simpleRoot_card_linear Q e h split i Ti hTi μi).trans hE
  let : IsCyclic (simpleRoot Q split i) := isCyclic_of_prime_card (p := 2) hc
  have hAi : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  exact unequal_middle_of_original_linear_factors Q e h split hm i j hij hpj μi μj hAi
    (a := 1) (by decide) hb (by simpa using hE) hF

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original SourceQuotient application retains the literal Q.q and
includes the nonperfect PSL₂(2) opposite endpoint. -/
theorem quotient_binary_opposite_middle
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    {b : ℕ} (hb : 1 < b) (hE : Nat.card E = 2) (hF : Nat.card F = 2^b) :
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    ¬ rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) ∧
      ⊥ < ⁅V,V⁆ ∧ ⁅V,V⁆ < middleRoots Q split i j := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := binary_opposite_middle_of_original_factors Q (originalMarkedIso Q) h split
    hm i j hij hpj μi μj hb hE hF
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
