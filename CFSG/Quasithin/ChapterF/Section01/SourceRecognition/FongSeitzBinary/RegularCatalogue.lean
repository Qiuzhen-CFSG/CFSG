module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates

/-!
# Regular original covers and the precise remaining small quotients

Exhaust the actual F.1.1 quotient catalogue without original perfectness.
Every binary linear parameter and every Suzuki parameter, including zero,
supply (2B) and the quotient-Sylow order. The same is true for SU3 and
PSU3 with fixed-field order at least four. RegularFactorCover therefore
constructs the original root and whole-cover comparisons, retaining the
scalar cover and both factor and root representative equations.

The remaining alternatives retain actual model isomorphisms: PSU3(2),
SU3(2), and the dihedral group of order ten. This is a list of still open
local branches, not a claim that each violates (2B). In particular the
dihedral quotient has a Sylow of order two but panel degree five, so the
quotient-Sylow equality used for the other rows cannot be imposed on it.

The literal Chapter 12 application proves both endpoint containments on
the regular branch and keeps every remaining small alternative explicit.
Neither this local catalogue exhaustion nor its cover comparison is the
seven-row rank-two classification. The full Borel, both endpoint squares,
split quotient, small-branch proofs, minimality and global row selection
remain with their genuine source construction and final assembly.
Source: Fong--Seitz I (2B), (5B)--(5C), pp.7--9,25--26;
AS F.1.1--3 and 12.2.2; DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
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
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hT in
/-- All ordinary source rows supply regularity and the exact Sylow count; only three concrete small quotients remain. -/
theorem regularity_or_small_unitary_or_dihedral :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T)) ∨
    ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
    IsSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
    Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) := by
  cases h.quotient i with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hs : Nat.card (quotientSylow T) = Nat.card F :=
      (Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
        ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
          (linearModelSylow i T μ)).symm.toEquiv).trans
            (Nat.card_congr Multiplicative.toAdd))
    exact Or.inl ⟨linear_remainder_le_kernel Q e h split i T hT μ,
      (simpleRoot_card_linear Q e h split i T hT μ).trans hs.symm⟩
  | suzuki m hm =>
    exact Or.inl ⟨suzuki_remainder_le_kernel_all Q e h split i T hT hm.some,
      suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT hm.some⟩
  | projective_unitary n hn hm =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
      exact Or.inl ⟨projectiveUnitary_remainder_le_kernel Q e h split i T hT J hn2 hcard hconj μ,
        projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ⟩
    · have he : n = 1 := by omega
      subst n
      exact Or.inr (Or.inl (by simpa using hm))
  | special_unitary n hn hm =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
      exact Or.inl ⟨specialUnitary_remainder_le_kernel Q e h split i T hT J hn2 hcard hconj μ,
        specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ⟩
    · have he : n = 1 := by omega
      subst n
      exact Or.inr (Or.inr (Or.inl (by simpa using hm)))
  | dihedral hm => exact Or.inr (Or.inr (Or.inr hm))

include h hT in
/-- Construct the regular original cover, with its representative equations, or retain a concrete small quotient. -/
theorem original_cover_or_small_unitary_or_dihedral :
    letI := originalRadicalInClosure_normal Q e h split i
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) ∧
      ∃ c : (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
          ((L i) ⧸ pCore 2 (L i)),
        ∃ a : originalRankOne Q e split i ≃* ((L i) ⧸ pCore 2 (L i)),
          (∀ l : L i, c (QuotientGroup.mk' _ (originalFactorIntoClosure Q e h split i l)) =
            QuotientGroup.mk' (pCore 2 (L i)) l) ∧
          ∀ r, c (QuotientGroup.mk' _ (inclusion (originalRankOne_le_localClosure Q e split i) r)) = a r) ∨
    ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
    IsSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
    Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) := by
  let := originalRadicalInClosure_normal Q e h split i
  rcases regularity_or_small_unitary_or_dihedral Q e h split i T hT with ⟨hV,hc⟩ | he
  · exact Or.inl ⟨hV,remainder_comap_of_containment Q e split i hV,
      regularOriginalFactorCoverEquiv Q e h split i T hT hV hc,
      regularOriginalFactorRootEquiv Q e h split i T hT hV hc,
      regularOriginalFactorCoverEquiv_mk_factor Q e h split i T hT hV hc,
      regularOriginalFactorCoverEquiv_mk_root Q e h split i T hT hV hc⟩
  · exact Or.inr he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 pair: both regular endpoint kernels and the selected original cover, or a concrete small quotient. -/
theorem rankOne_global_regular_cover_or_small
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
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ((∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∧
      ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
          MarkedLocal.originalRadicalInClosure Q e split 1) ≃* (R ⧸ pCore 2 R),
        ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* (R ⧸ pCore 2 R),
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            QuotientGroup.mk' (pCore 2 R) l) ∧
          ∀ r, c (QuotientGroup.mk' _ (inclusion
            (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∨
      ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 2 ∨
      IsSU (R ⧸ pCore 2 R) 3 2 ∨ Nonempty ((R ⧸ pCore 2 R) ≃* DihedralGroup 5) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases MarkedLocal.original_cover_or_small_unitary_or_dihedral Q e hf split 1 T₁ hT₁ with
    ⟨hV,hcore,c,a,hc,ha⟩ | he
  · refine Or.inl ⟨?_,c,a,hc,ha⟩
    intro i
    fin_cases i
    · have h0 := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
      exact ⟨h0,MarkedLocal.remainder_comap_of_containment Q e split 0 h0⟩
    · exact ⟨hV,hcore⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
