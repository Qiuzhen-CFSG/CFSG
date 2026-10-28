module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleIsolation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.TrialityCentrality

/-!
# The isolated middle root on the original hexagon and triality consumer

Odd-Cartan isolation proves the exact derived subgroup on the same finite
marked quotient. The marked and original-quotient applications retain the
actual Sylow image and the literal right-conjugation word s_j s_i. The
marking is arbitrary, so it applies to the universal/geometric carrier too.
Actual local linear models and the earlier kernel inclusions remain inputs;
no original local perfectness is imposed and field orders two and four and
the exponent-six exception are retained.

The triality application now constructs StructuralRow from just its still
unproved nonzero long-root commutator. The derived, long-central and
orthogonal fields are proved here. Applying the row to the existing pair,
Weyl placement and original root ranges supplies all ten positive commuting
pairs. The two nonzero commutator identities, irreducibility, cubic field
ratio, nonlinear effective sections, and Suzuki/unitary exclusions remain
obligations of the hexagon family; this is not the full (6E) dichotomy.

Source: Fong--Seitz I (6E), printed pp.43--45; II (9.22), pp.217--220.
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

/-- Discharge the derived-subgroup premise of the actual triality row.
Only the nonzero long-root commutator remains a structural premise. -/
theorem triality_structuralRow_of_long_commutator
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i)) :
    TrialitySource.StructuralRow Q split j i :=
  triality_structuralRow_of_middle_root Q split hm i j hij hKi hKj μi μj ha hab hE hF
    (unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj
      (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
      ha hab hE hF) hlong

/-- The actual published positive-commutation consumer with its previous
derived-subgroup premise proved, preserving both signed-root markings. -/
theorem triality_positiveCommutations_of_long_commutator
    {σ : F ≃+* F}
    (p : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair σ (X ⧸ Q.D))
    (w : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.WeylPlacement Q p)
    (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
    (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
    (hm : rotationOrder Q = 6)
    (hKi : simpleRemainder Q split (w.indices 1) ≤ localKernel Q (w.indices 1))
    (hKj : simpleRemainder Q split (w.indices 0) ≤ localKernel Q (w.indices 0))
    (μi : localGroup Q split (w.indices 1) ≃* PSL(2,E))
    (μj : localGroup Q split (w.indices 0) ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (hlong : ⁅simpleRoot Q split (w.indices 1),rootAt Q split (w.indices 1) (Q.simple (w.indices 0))⁆ =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1))) :
    p.PositiveCommutations :=
  TrialitySource.StructuralApplication.positiveCommutations Q split p w shortBase longBase hm
    (triality_structuralRow_of_long_commutator Q split hm (w.indices 1) (w.indices 0)
      (w.indices.injective.ne (by decide)) hKi hKj μi μj ha hab hE hF hlong)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- The same derived identity on the literal original/geometric Sylow image,
with the source's exact right-conjugation word. -/
theorem marked_unequal_derived_middle_root
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
    ⁅V,V⁆ = rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N) := by
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [← marked_radical_eq h Q e split j sj.val sj.class_eq]
  have hh := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj
    si sj ha hab hE hF
  rwa [rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul,sj.class_eq,si.class_eq])] at hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original SourceQuotient version with the literal Q.q image of S. -/
theorem quotient_unequal_derived_middle_root
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
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U (sj.val : (generated L S) ⧸ Q.D)
    ⁅V,V⁆ = rightConjugate (simpleRoot Q split i) (sj.val*si.val : Q.tits.N) := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_unequal_derived_middle_root Q split (originalMarkedIso Q) h hm i j hij
    hKi hKj μi μj ha hab hE hF
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
