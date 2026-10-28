module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnequalLinear

/-!
# Small sections and middle-root centrality on the original marking

The original linear identification supplies the local model and kernel for
the actual section-action bound. Its perfectness hypothesis is retained
exactly where the identification requires it. The marked middle-root
application uses actual local models and retains both endpoint orientations.
The binary opposite-root application uses its proved order two directly;
it needs no original-factor perfectness and no additional local-model
identification. All radical expressions use the original Sylow map, and
the final quotient application uses the literal Q.q.

These implications discharge centralization and the four zero commutators
in Fong–Seitz I (6E)(b), p.44, once the preceding torus argument identifies
the radical's derived subgroup. That identity remains an obligation of
HexagonStructure, together with the two nonzero commutators and the
irreducible module. No completed structural dichotomy is claimed here.
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

include e h in
/-- The original acting factor supplies the actual local identification;
the quotient and conjugation action remain those of the given section. -/
theorem small_section_action_of_original_linear_factor
    (j : Fin 2) (hpj : Group.IsPerfect (L j))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    (d : RootSection Q split j) {b : ℕ} (hb : 1 < b)
    (hF : Nat.card F = 2^b) (hsmall : Nat.card d.Carrier < 2^(2*b)) : d.action = 1 := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  exact linear_small_section_action Q split j
    (MarkedLocal.linear_remainder_le_kernel Q e h split j T hT μj)
    (MarkedLocal.linearLocalEquiv Q e h split j hpj T hT μj)
    (UnitarySource.actorReflection Q split j) d hb hF hsmall

/-- The marked geometric application retains the original Sylow image,
the two actual source reflections, and every right-conjugation word. -/
theorem marked_derived_middle_zero_relations
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
    let C := rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N)
    ⁅V,V⁆ = C →
    ⁅V,C⁆ = ⊥ ∧ ⁅rankOne Q split j,C⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,C⁆ = ⊥ ∧
    ⁅C,rightConjugate (simpleRoot Q split i) (sj.val : X ⧸ Q.D)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)⁆ = ⊥ ∧
    ⁅rightConjugate (simpleRoot Q split j) (si.val : X ⧸ Q.D),
      rightConjugate (simpleRoot Q split i) (sj.val : X ⧸ Q.D)⁆ = ⊥ := by
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [←marked_radical_eq h Q e split j sj.val sj.class_eq,
    ←rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul,sj.class_eq,si.class_eq]),
    ←rootAt_eq Q split i (Q.simple j) sj.val sj.class_eq,
    ←rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq]),
    ←rootAt_eq Q split j (Q.simple i) si.val si.class_eq]
  intro hd
  have hsmall : Nat.card (simpleRoot Q split i) < 2^(2*b) := by
    rw [GTwoSource.simpleRoot_card Q split i hKi μi, hE]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨derived_middle_root_radical_centralized Q split j hm i hij hKi μi hKj hd,
    derived_middle_root_centralized Q split j hKj μj sj hm i hij hd (by omega) hF hsmall,
    derived_middle_root_zero_relations Q split j hKj μj sj hm i hij hKi μi hd (by omega) hF hsmall⟩

/-- For an original PSL₂(2) opposite factor, the panel count alone supplies
all six centralizations after the torus identity. Neither factor is assumed perfect. -/
theorem marked_binary_derived_middle_zero_relations
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    (hE : Nat.card E = 2) :
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U (sj.val : X ⧸ Q.D)
    let C := rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N)
    ⁅V,V⁆ = C →
    ⁅V,C⁆ = ⊥ ∧ ⁅rankOne Q split j,C⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,C⁆ = ⊥ ∧
    ⁅C,rightConjugate (simpleRoot Q split i) (sj.val : X ⧸ Q.D)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)⁆ = ⊥ ∧
    ⁅rightConjugate (simpleRoot Q split j) (si.val : X ⧸ Q.D),
      rightConjugate (simpleRoot Q split i) (sj.val : X ⧸ Q.D)⁆ = ⊥ := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hKj := MarkedLocal.linear_remainder_le_kernel Q e h split j Tj hTj μj
  have hc : Nat.card (simpleRoot Q split i) = 2 :=
    (MarkedLocal.simpleRoot_card_linear Q e h split i Ti hTi μi).trans hE
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [←marked_radical_eq h Q e split j sj.val sj.class_eq,
    ←rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul,sj.class_eq,si.class_eq]),
    ←rootAt_eq Q split i (Q.simple j) sj.val sj.class_eq,
    ←rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq]),
    ←rootAt_eq Q split j (Q.simple i) si.val si.class_eq]
  intro hd
  have hz := binary_derived_middle_root_centralized Q split j i hKj hd hc
  exact ⟨hz.1,hz.2,binary_derived_middle_root_zero_relations Q split j hm i hij hKj hd hc⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original quotient version uses precisely the image of S under Q.q,
and includes nonperfect binary original factors. -/
theorem quotient_binary_derived_middle_zero_relations
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F)) (hE : Nat.card E = 2) :
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U (sj.val : (generated L S) ⧸ Q.D)
    let C := rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N)
    ⁅V,V⁆ = C →
    ⁅V,C⁆ = ⊥ ∧ ⁅rankOne Q split j,C⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,C⁆ = ⊥ ∧
    ⁅C,rightConjugate (simpleRoot Q split i) (sj.val : (generated L S) ⧸ Q.D)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)⁆ = ⊥ ∧
    ⁅rightConjugate (simpleRoot Q split j) (si.val : (generated L S) ⧸ Q.D),
      rightConjugate (simpleRoot Q split i) (sj.val : (generated L S) ⧸ Q.D)⁆ = ⊥ := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_binary_derived_middle_zero_relations Q (originalMarkedIso Q) h split
    hm i j hij μi μj hE
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
