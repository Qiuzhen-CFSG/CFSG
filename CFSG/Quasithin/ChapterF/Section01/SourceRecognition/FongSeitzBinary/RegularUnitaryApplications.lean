module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryElementaryExclusion
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearIdentificationApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddLinearRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover

/-!
# Original regularity on odd Weyl branches and the generic unitary cover

Odd Weyl opposition conjugates the two actual simple roots. The original
perfect linear first factor makes its root elementary abelian, whereas the
proved solvable nine-point obstruction forbids an elementary second root.
This excludes the binary affine exception on every odd branch of the same
marked source quotient and proves both (2B) containments and core preimages.

The literal Chapter 12 application uses the inherited perfectness of its
first factor. Its remaining affine alternative now has even Weyl rotation,
with the original central odd cover, full Borel and both endpoint maps.
On the regular branch an actual SU3-or-PSU3 factor quotient constructs the
generic surjective SU3 cover and its projective square, including q = 2.

The earlier quotient/split data retain the apartment/exchange producer;
the unitary factor marking retains its original catalogue producer. Even
affine exclusion, minimality, exhaustive row selection and the final seven
amalgam isomorphisms remain with source recognition and its assembly owner.
Source: Fong--Seitz I (2A)--(2B), (5B)--(5C); DGS pp.80--81,224;
Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- Odd global opposition excludes the affine second panel when the first
original factor is perfect linear. Both literal (2B) containments follow. -/
theorem regularity_of_first_linear_of_odd
    (hp : Group.IsPerfect (L 0)) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n))
    (hm : Odd (rotationOrder Q)) :
    ∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) := by
  have h0 := linear_remainder_le_kernel_of_model Q e h split 0 hmodel
  have hE : IsElementaryAbelian 2 (simpleRoot Q split 0) := by
    let := h.finite_local 0
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    obtain ⟨T,hT⟩ := h.sylow 0
    exact simpleRoot_elementary_of_linear Q split 0
      (linearLocalEquiv Q e h split 0 hp T hT μ)
  let := hE
  let a := simpleRootOppositionEquiv Q split hm
  have hE1 : IsElementaryAbelian 2 (simpleRoot Q split 1) :=
    IsElementaryAbelian.of_injective a.symm.toMonoidHom a.symm.injective
  let := h.finite_local 1
  obtain ⟨T,hT⟩ := h.sylow 1
  have h1 : simpleRemainder Q split 1 ≤ localKernel Q 1 ∧
      (simpleRemainder Q split 1).comap (endpointMap Q e 1) = pCore 2 (parabolic L S 1) := by
    rcases remainder_le_kernel_or_binary_unitary_exception Q e h split 1 T hT with hr | hx
    · exact hr
    · exact (simpleRoot_not_elementary_of_solvable_nine Q split 1 hx.1 hx.2.1 hE1).elim
  intro i
  fin_cases i
  · exact ⟨h0,remainder_comap_of_containment Q e split 0 h0⟩
  · exact h1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The actual Chapter 12 pair has both source kernels on every odd Weyl branch. -/
theorem rankOne_global_regularity_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    ∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact MarkedLocal.regularity_of_first_linear_of_odd Q e (d.hypothesisF11 hi hTH) split
    (Chapter1.mem_L_isPerfect hi.local_mem.1.1) hpsl hm

/-- The remaining affine alternative has even Weyl rotation; the original
full Borel, central cover and both endpoint markings are unchanged. -/
theorem rankOne_global_regularity_or_even_binary_affine
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
    (MarkedLocal.BinaryUnitaryException Q split 1 ∧
      MarkedLocal.BinaryAffineComparison Q e hf split 1 ∧ Even (rotationOrder Q)) := by
  rcases D.rankOne_global_regularity_or_binary_affine h hmany hn hpsl d hTH Q e split with hr | hx
  · exact Or.inl hr
  · refine Or.inr ⟨hx.1,hx.2,?_⟩
    apply Nat.not_odd_iff_even.mp
    intro ho
    exact hx.1.2.2.2.2.1 ((D.rankOne_global_regularity_of_odd h hmany hn hpsl d hTH Q e split ho 1).1)

/-- The actual unitary factor supplies the generic SU3 cover, or the precise
remaining affine exception. This includes every positive field degree. -/
theorem rankOne_global_unitary_cover_or_binary_affine
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    ((∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∧
      ∃ ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ π : J.specialSubgroup →* rankOne Q split 1,
          Function.Surjective π ∧
          ∀ a, ν (RootLocalCover.projection Q split 1 (π a)) = J.specialToProjective a) ∨
      (MarkedLocal.BinaryUnitaryException Q split 1 ∧
        MarkedLocal.BinaryAffineComparison Q e hf split 1 ∧ Even (rotationOrder Q)) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases D.rankOne_global_regularity_or_even_binary_affine h hmany hn hpsl d hTH Q e split with hr | hx
  · exact Or.inl ⟨hr,MarkedLocal.regular_unitary_cover_of_factor Q e hf split
      J hm hc hconj 1 (hr 1).1 hfactor⟩
  · exact Or.inr hx

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
