module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineUnitaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover

/-!
# Original unitary factors exclude the opposite affine hexagon

The original SU3 or PSU3 quotient at q greater than two supplies its local
regularity, the exact root order and the full root-actor equivalence.
The global Cartan-fixed kernel argument excludes the opposite order-144
alternative. Exhausting the existing source endpoint catalogue then gives
(2B) at both endpoints and identifies their literal remainder preimages
with the original two-cores, without perfectness of either source factor.

For a unitary opposite factor, this also constructs its surjective SU3
cover and its actual projective square. Its parameter may be one: the
nonperfect binary cover uses the generic regular-factor construction.
The original full Borel and both endpoint inclusion squares remain those
of the same input amalgam isomorphism; no ambient completion is identified
with the finite quotient.

Source: Fong--Seitz I (2B), (5B)--(5C), (5I), pp.9,25--26,31--35;
DGS Theorem D, p.224; Aschbacher--Smith F.1.1--3. Rotation order six, the
marked quotient and split data remain genuine earlier-source inputs from
the apartment/exchange and profile producers. Their final discharge, the
other even branches, minimality and all seven marked rows remain with the
source assembly. These theorems close this conditional source branch only.
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
/-- Either original unitary cover excludes the opposite affine hexagon,
without perfectness of either original factor. -/
theorem binary_affine_hexagon_false_of_unitary
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hfactor : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  rcases hfactor with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hV := specialUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj μ
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow
      Q e h split i T hT J (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split i T hT hV hc).trans μ
    exact no_affine_hexagon_of_special_unitary Q split J hn hcard hconj hm i j hij hV a
      (specialUnitary_simpleRoot_card Q e h split i T hT J (by omega) hcard hconj μ)
      hx.1 hx.2.1 hx.2.2.1
  · have hV := projectiveUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj μ
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow
      Q e h split i T hT J (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split i T hT hV hc).trans μ
    exact no_affine_hexagon_of_projective_unitary Q split J hn hcard hconj hm i j hij hV a
      (projectiveUnitary_simpleRoot_card Q e h split i T hT J (by omega) hcard hconj μ)
      hx.1 hx.2.1 hx.2.2.1

include e h in
/-- Both original two-cores are the literal remainder preimages when one
original factor has a nonbinary SU3 or PSU3 quotient. -/
theorem marked_hexagon_regularity_of_unitary
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 6) (i : Fin 2)
    (hfactor : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) =
        pCore 2 (parabolic L S j) := by
  intro j
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  by_cases he : i = j
  · subst j
    have hV : simpleRemainder Q split i ≤ localKernel Q i := by
      rcases hfactor with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
      · exact specialUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj μ
      · exact projectiveUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj μ
    exact ⟨hV,remainder_comap_of_containment Q e split i hV⟩
  · rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
    · exact hr
    · exact (binary_affine_hexagon_false_of_unitary
        Q e h split J hn hcard hconj hm i j he hfactor hx).elim

include e h in
/-- The unitary hexagon branch constructs the opposite generic SU3 cover,
including its binary case, with both original cores and the projective square. -/
theorem marked_hexagon_unitary_cover_of_unitary_opposite
    {E F : Type*} [Field E] [Finite E] [Field F] [Finite F]
    (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (hE : Nat.card E = (2^n)^2) (hF : Nat.card F = (2^m)^2)
    (hJ : ∀ x, J.conj x = x^(2^n)) (hK : ∀ x, K.conj x = x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2)
    (hfirst : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hsecond : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* K.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup K)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (endpointMap Q e k) = pCore 2 (parabolic L S k)) ∧
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup K,
      ∃ π : K.specialSubgroup →* rankOne Q split j,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split j (π a)) = K.specialToProjective a := by
  have hr := marked_hexagon_regularity_of_unitary Q e h split J hn hE hJ hhex i hfirst
  exact ⟨hr,regular_unitary_cover_of_factor Q e h split K hm hF hK j (hr j).1 hsecond⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
