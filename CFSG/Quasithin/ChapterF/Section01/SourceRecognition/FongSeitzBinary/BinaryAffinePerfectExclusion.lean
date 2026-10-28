module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SuzukiAffineExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectLocalRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineUnitaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllLocalIdentification

/-!
# Both hexagon endpoint kernels from one perfect original factor

The original nonbinary Suzuki quotient supplies its canonical root actor
and exact root order without original-factor perfectness. Its Cartan
fixed-point theorem excludes the opposite affine endpoint. Together with
the proved linear and unitary exclusions, this exhausts the actual F.1.1
catalogue whenever one original factor is perfect. Perfectness derives
the needed parameter bounds and excludes the dihedral case; it is never
required at the other endpoint.

Consequently both canonical remainders pull back along the original
endpoint maps to their respective two-cores. An actual unitary quotient
at either endpoint then constructs the surjective SU3 cover and its
literal scalar/projective square, including the nonperfect q=2 case.
The Chapter 12 application supplies the first factor's perfectness from
its original local hypothesis. The same full-Borel amalgam marking and
both endpoint inclusion squares are retained throughout.

Source: Fong--Seitz I (2B), (5B)--(5C), (5I), pp.9,25--26,31--35;
DGS Theorem D, p.224; Aschbacher--Smith F.1.1--3 and 12.2.2. The genuine
marked quotient, split data and rotation order six remain earlier inputs
from the apartment/exchange and profile producers. This closes the stated
conditional hexagon branch. Other even branches, minimality and the seven
marked rank-two rows remain with the original source-recognition assembly.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups

open Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
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
/-- The actual Suzuki quotient at either original endpoint excludes the opposite affine hexagon. -/
theorem binary_affine_hexagon_false_of_suzuki
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (hm : 0 < m)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact no_affine_hexagon_of_suzuki Q split hhex i j hij hm
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzukiAllRankOneEquiv Q e h split i T hT μ)
    (suzuki_simpleRoot_card Q e h split i T hT μ) hx.1 hx.2.1 hx.2.2.1

include e h in
/-- A nonbinary Suzuki factor gives both original core equalities, without perfectness. -/
theorem marked_hexagon_regularity_of_suzuki
    (hhex : rotationOrder Q = 6) (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  intro j
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  by_cases he : i = j
  · subst j
    have hV := suzuki_remainder_le_kernel_all Q e h split i T hT μ
    exact ⟨hV,remainder_comap_of_containment Q e split i hV⟩
  · rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
    · exact hr
    · exact (binary_affine_hexagon_false_of_suzuki Q e h split hhex i j he hm μ hx).elim

include e h in
/-- Exhausting the actual original perfect-factor catalogue excludes every affine opposite hexagon. -/
theorem binary_affine_hexagon_false_of_perfect
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L i)) (hx : BinaryUnitaryException Q split j) : False := by
  let := hp
  let := h.finite_local i
  cases h.quotient i with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let : Group.IsPerfect PSL(2,F) :=
      Group.IsPerfect.ofSurjective (f := μ.toMonoidHom) μ.surjective
    exact binary_affine_hexagon_false_of_linear Q e h split
      Theory.PSL2.CartanPanel.card_gt_two_of_perfect hhex i j hij hp μ hx
  | suzuki m hm =>
    exact binary_affine_hexagon_false_of_suzuki Q e h split hhex i j hij
      (suzuki_parameter_pos i hp hm.some) hm.some hx
  | projective_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact binary_affine_hexagon_false_of_unitary Q e h split J
      (projectiveUnitary_parameter_ge_two i hp J hn hcard hconj μ)
      hcard hconj hhex i j hij (Or.inr ⟨μ⟩) hx
  | special_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact binary_affine_hexagon_false_of_unitary Q e h split J
      (specialUnitary_parameter_ge_two i hp J hn hcard hconj μ)
      hcard hconj hhex i j hij (Or.inl ⟨μ⟩) hx
  | dihedral hm =>
    exact not_perfect_dihedral_model hm.some inferInstance

include e h in
/-- One perfect original factor suffices for both (2B) equalities on the marked hexagon. -/
theorem marked_hexagon_regularity_of_perfect
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  intro j
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  by_cases he : i = j
  · subst j
    have hV := perfect_remainder_le_kernel Q e h split i hp T hT
    exact ⟨hV,remainder_comap_of_containment Q e split i hV⟩
  · rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
    · exact hr
    · exact (binary_affine_hexagon_false_of_perfect Q e h split hhex i j he hp hx).elim

include e h in
/-- The opposite unitary cover is constructed on every such hexagon, including q=2. -/
theorem marked_hexagon_unitary_cover_of_perfect_opposite
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hp : Group.IsPerfect (L i))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (endpointMap Q e k) = pCore 2 (parabolic L S k)) ∧
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split j,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a := by
  have hr := marked_hexagon_regularity_of_perfect Q e h split hhex i hp
  exact ⟨hr,regular_unitary_cover_of_factor Q e h split J hn hc hconj j (hr j).1 hfactor⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal hexagon branch supplies the surjective SU3 cover at the selected
second endpoint, even when that factor is nonperfect and its parameter is one. -/
theorem rankOne_global_hexagon_unitary_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q e k) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) k)) ∧
    ∃ ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split 1,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split 1 (π a)) = J.specialToProjective a := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let hf := d.hypothesisF11 hi hTH
  exact MarkedLocal.marked_hexagon_unitary_cover_of_perfect_opposite Q e hf split
    hhex 0 1 (Chapter1.mem_L_isPerfect hi.local_mem.1.1) J hm hc hconj hfactor
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
