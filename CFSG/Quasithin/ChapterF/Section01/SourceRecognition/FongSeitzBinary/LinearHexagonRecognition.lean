module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.CubicRatio
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SourceFieldApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.CommonFieldRecognition
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink

/-!
# Full G₂ and triality comparisons from the original linear factors

Start with actual PSL₂ quotient isomorphisms on both original F.1.1
factors, the same marked split quotient, and rotation order six. The
original actors and their exact two-core kernels supply the faithful
local PSL₂ markings and both remainder-to-panel-kernel containments.
No perfectness of either original factor is required.

For equal field orders, transport both entire local models to one finite
field and apply the completed G₂ source equations and presentation. For
unequal orders, the actual hexagon structure forces the cubic ratio and
supplies the triality structural row. The completed triality construction
then builds the extension field, common labels, root relations and full
comparison. In each case the original F.1.1 data supply normal generation.
The full Borel and both endpoint inclusion squares are retained, including
binary fields and both orientations.

The final case split covers every pair of original linear factors. The
Chapter 12 application consumes the original factor assertions directly;
no common field, cubic ratio, local-action marking, structural row or
presentation equation is an extra input. Construction of the marked split
quotient and selection of the linear hexagon branch remain earlier source
obligations; this does not assert exhaustive seven-row recognition.

Source: Fong--Seitz I (6E), pp.43--45; II §9, pp.211--220;
DGS Theorem D, p.224; Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearHexagon
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
private theorem local_model {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := MarkedLocal.linear_remainder_le_kernel Q mark h split i T hT μ
  obtain ⟨f,hf,hk,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μ
  let A := (S ⊔ L i).subgroupOf (parabolic L S i)
  let : A.Normal := QuadrangleStructure.marked_sylow_factor_normal Q mark h split i
  obtain ⟨_,ν,_,_⟩ := QuadrangleStructure.marked_linear_localGroup Q mark h split i
    (UnitarySource.actorReflection Q split i) hV A (subgroupOf_mono _ le_sup_left) f hf hk
  exact ⟨hV,⟨ν⟩⟩

include mark h split in
/-- Unequal original linear factors force the cubic parameter and the full
triality amalgam, without a structural-row or local-model hypothesis. -/
theorem marked_unequal_linear_triality
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    b = 3*a ∧ Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (TrialityPresentation.flagAmalgam a ha j)) := by
  obtain ⟨hVi,⟨νi⟩⟩ := local_model Q mark h split i μi
  obtain ⟨hVj,⟨νj⟩⟩ := local_model Q mark h split j μj
  obtain ⟨hc,hcard,_,row,_,_⟩ := HexagonStructure.triality_unequal_cubic_structure
    Q split hm i j hij hVi hVj νi νj ha hab hE hF
  let indices : Fin 2 ≃ Fin 2 := Equiv.swap 0 j
  have hi : indices 0 = j := Equiv.swap_apply_left 0 j
  have hj : indices 1 = i := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · decide
    · decide
    · exact (hij rfl).elim
  have hVj' : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0) := hi ▸ hVj
  have hVi' : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1) := hj ▸ hVi
  let νj' : localGroup Q split (indices 0) ≃* PSL(2,F) := hi ▸ νj
  let νi' : localGroup Q split (indices 1) ≃* PSL(2,E) := hj ▸ νi
  have row' : TrialitySource.StructuralRow
      Q split (indices 0) (indices 1) := by simpa only [hi,hj] using row
  have hcard' : Nat.card F = (2^a)^3 := by simpa only [hE] using hcard
  let roots := TrialitySource.SourceFieldApplication.markedRootData (hn := ha)
    Q split indices hVj' hVi' νj' νi' hm row' hcard' hE mark h
  refine ⟨hc,?_⟩
  have e : Nonempty (RankTwoAmalgam.Iso _ (TrialityPresentation.flagAmalgam a ha (indices 0))) :=
    ⟨roots.comparison mark⟩
  rw [hi] at e
  exact e

include mark h split in
/-- Equal original linear factor orders give a full G₂ comparison in the
orientation selected by the actual middle-root commutator pairing. -/
theorem marked_equal_linear_gTwo
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6)
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F))
    (hcard : Nat.card E = Nat.card F) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = Nat.card E ∧
      (Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (GreenBook.LieModels.G2.amalgam (F := K))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (GreenBook.LieModels.G2.amalgam (F := K)).reverse)) := by
  obtain ⟨hV₀,⟨ν₀⟩⟩ := local_model Q mark h split 0 μ₀
  obtain ⟨hV₁,⟨ν₁⟩⟩ := local_model Q mark h split 1 μ₁
  let K := Shrink.{0} E
  let k₀ : E ≃+* K := (Shrink.ringEquiv.{0,_} E).symm
  let : CharP K 2 := (k₀.toRingHom.charP_iff_charP 2).mp inferInstance
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  let k₁ : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using
      hcard.symm.trans (Nat.card_congr k₀.toEquiv))
  let ν : ∀ i, localGroup Q split i ≃* PSL(2,K) :=
    fun i => if hi : i = 0 then hi ▸ (ν₀.trans (Atlas.fieldEquivPSL 2 k₀)) else
      (show i = 1 by omega) ▸ (ν₁.trans (Atlas.fieldEquivPSL 2 k₁))
  have hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i := by
    intro i
    fin_cases i
    · exact hV₀
    · exact hV₁
  let roots := GTwoSource.CommonFieldSource.rootData Q split hm hV ν
    (UnitarySource.actorReflection Q split)
    (MarkedLocal.unipotentClosure_eq_top_of_source Q mark h split)
  refine ⟨K,inferInstance,inferInstance,inferInstance,(Nat.card_congr k₀.toEquiv).symm,?_⟩
  let cmp := G2Presentation.comparison Q mark split roots
  have hc : ∀ (short : Fin 2), Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (Atlas.G2.RootPresentationRecognition.flagAmalgam K short)) →
        Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
            (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
          (GreenBook.LieModels.G2.amalgam (F := K))) ∨
        Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
            (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
          (GreenBook.LieModels.G2.amalgam (F := K)).reverse) := by
    intro short ⟨c⟩
    fin_cases short
    · exact Or.inl ⟨c.trans GreenBook.LieModels.G2.borelIso.symm⟩
    · exact Or.inr ⟨c.trans GreenBook.LieModels.G2.borelIso.symm.reverse⟩
  exact hc _ ⟨cmp⟩

include mark h split in
/-- Exhaust the equal and unequal field orders for two original linear factors.
No common field, cubic ratio, local model, root relation or generation premise
is required beyond the original factor markings. -/
theorem marked_linear_hexagon_catalogue
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6)
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  obtain ⟨a,_,ha⟩ := FiniteField.card E 2
  obtain ⟨b,_,hb⟩ := FiniteField.card F 2
  have hE : Nat.card E = 2^(a : ℕ) := by simpa only [Nat.card_eq_fintype_card] using ha
  have hF : Nat.card F = 2^(b : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hb
  rcases lt_trichotomy (a : ℕ) b with hab | hab | hab
  · obtain ⟨_,⟨cmp⟩⟩ := marked_unequal_linear_triality Q mark h split hm 0 1
      (by decide) μ₀ μ₁ a.property hab hE hF
    exact .triality a a.property (Or.inr ⟨cmp⟩)
  · have hcard : Nat.card E = Nat.card F := by rw [hE,hF,hab]
    obtain ⟨K,hK,hfin,hchar,_,cmp⟩ := marked_equal_linear_gTwo Q mark h split hm μ₀ μ₁ hcard
    exact .g2 K cmp
  · obtain ⟨_,⟨cmp⟩⟩ := marked_unequal_linear_triality Q mark h split hm 1 0
      (by decide) μ₁ μ₀ b.property hab hF hE
    exact .triality b b.property (Or.inl ⟨cmp⟩)

include mark h split in
/-- The actual PSL₂ quotient isomorphisms encoded by the original factor
assertions suffice, including the solvable binary factors. -/
theorem marked_linear_hexagon_of_factor_types
    (hm : rotationOrder Q = 6) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^a))
    (h₁ : ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 (2^b)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨E,hE,hfinE,hcardE,⟨μ₀⟩⟩ := h₀
  obtain ⟨F,hF,hfinF,hcardF,⟨μ₁⟩⟩ := h₁
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨hb.ne'⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardE)
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  exact marked_linear_hexagon_catalogue Q mark h split hm μ₀ μ₁

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearHexagon
