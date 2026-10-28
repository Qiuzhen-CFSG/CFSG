module
public import Theory.GroupTheory.MarkedInnerStrongClosure.OmegaAction
public import Theory.SpecificGroups.SU3.OmegaDisplacementInner
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# The square-displacement criterion for the complete simple Bender list

Binary PSL₂ has elementary abelian Sylows, so fixing their first omega is
pointwise fixation and the proved pointwise-inner theorem applies. Suzuki
square-one automorphisms are inner by the established odd outer index.
For PSU₃ the square-displacement coordinate argument excludes outer actions.
An actual Hermitian basis change handles every form in the source model
predicate; field and fixed-field orders remain distinct. The order-five
PSL₂ overlap is transported through the proved PSL₂(5)≃PSL₂(4) equivalence.
-/

public section
open Subgroup Theory.GroupTheory.MarkedInnerStrongClosure
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.BenderFusion.InnerActionModels
variable {K : Type*} [Group K] [Finite K]

private theorem linear (F : Type*) [Field F] [Finite F] [CharP F 2] :
    SquareDisplacementInner PSL(2,F) := by
  intro P a ha hs hf hd ht
  obtain ⟨g, _, hg⟩ := Theory.PSL2.aut_fixing_sylow_inner P a (by
    intro x hx
    apply hf
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
    let e := BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive P
    have hxp : (⟨x, hx⟩ : P) ^ 2 = 1 := by
      apply e.symm.injective
      rw [map_pow, map_one]
      change 2 • (e.symm ⟨x, hx⟩).toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
    exact congrArg Subtype.val hxp)
  exact ⟨g, hg⟩

private theorem unitary_standard {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    SquareDisplacementInner (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  intro P a ha hs hf hd ⟨t, htP, htn, ht2⟩
  exact J.projective_inner_of_square_displacements hJ hn hcard hfixed P a ha hs
    t htP htn ht2 (hf t ((omegaOneAmbient_le_iff _ _).mp le_rfl t htP ht2)) hd

/-- All three permitted simple Bender families satisfy the exact intrinsic
criterion; the original source model predicate supplies every case. -/
theorem of_bender_model (hmodel : ClassificationModels.IsBenderModel K) :
    SquareDisplacementInner K := by
  cases hmodel with
  | linear n hn h =>
    obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := h
    let := hfield
    let := hfinite
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [← Nat.card_eq_fintype_card] using hF)
    exact SquareDisplacementInner.of_mulEquiv e (linear F)
  | unitary n hn h =>
    obtain ⟨F, hfield, hfinite, J, hF, hconj, ⟨e⟩⟩ := h
    let := hfield
    let := hfinite
    have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
    obtain ⟨eJ⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2 ^ n) hF hfixed
    exact SquareDisplacementInner.of_mulEquiv (e.trans eJ)
      (unitary_standard _ rfl hn hF hfixed)
  | suzuki m hm h =>
    obtain ⟨e⟩ := h
    apply SquareDisplacementInner.of_mulEquiv e
    intro P a ha hs hf hd ht
    obtain ⟨g, hg, _⟩ := BenderSuzuki.ZD.suzuki_involutoryAut_inner_and_twoRank m hm a ha
    exact ⟨g, hg⟩

omit [Finite K] in
/-- The exceptional prime-field parameter five is retained as the actual
binary Bender model, with an explicit field and group equivalence. -/
theorem bender_model_of_psl2_five (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 5) (e : K ≃* PSL(2,F)) : ClassificationModels.IsBenderModel K := by
  apply ClassificationModels.IsBenderModel.linear 2 (by decide)
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩⟩
  exact GaloisField.card 2 2 (by decide)

end CFSG.Quasithin.Chapter2.BenderFusion.InnerActionModels
