module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectLocalCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocal

/-!
# The full perfect-factor catalogue satisfies (2B)

Exhaust the actual original rank-one quotient catalogue. The linear,
Suzuki, special-unitary and projective-unitary branches use their proved
local regularity. Original perfectness excludes the small parameters and
the dihedral case exactly where needed. Consequently every perfect
original factor has its canonical remainder equal, on pullback, to the
original parabolic two-core. Its whole-root cover is the same original
factor quotient, with the literal representative equation retained.

The Chapter 12 consumer applies this to its selected perfect second factor
and combines it with the original first linear factor, discharging BOTH
endpoint (2B) premises on the same marked quotient and full Borel. This
is local regularity and cover transport; minimality, nonperfect exits,
rank-two row selection and the final seven-row marked assembly remain.
Source: Fong--Seitz I (2B), (5C), pp.7--9,25--26;
Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hp hT in
/-- Every original perfect rank-one factor satisfies (2B), by its actual catalogue model. -/
theorem perfect_remainder_le_kernel :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let : Group.IsPerfect (L i) := hp
  cases h.quotient i with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact linear_remainder_le_kernel Q e h split i T hT μ
  | suzuki m hm =>
    exact suzuki_remainder_le_kernel_of_perfect Q e h split i T hT hp hm.some
  | projective_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact projectiveUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hn hcard hconj μ
  | special_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact specialUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hn hcard hconj μ
  | dihedral hm =>
    exact (not_perfect_dihedral_model hm.some inferInstance).elim

include e h hp hT in
/-- The canonical remainder pulls back to the original parabolic two-core. -/
theorem perfect_remainder_comap :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i (perfect_remainder_le_kernel Q e h split i hp T hT)

/-- The full original cover is its actual factor quotient, with (2B) discharged. -/
def regularOriginalPerfectCoverEquiv :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
      (L i) ⧸ pCore 2 (L i) :=
  originalPerfectCoverEquiv Q e h split i hp T hT (perfect_remainder_le_kernel Q e h split i hp T hT)

@[simp] theorem regularOriginalPerfectCoverEquiv_mk (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    regularOriginalPerfectCoverEquiv Q e h split i hp T hT
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r)) :=
  originalPerfectCoverEquiv_mk Q e h split i hp T hT _ r

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The selected perfect second factor has its original quotient as canonical
root group and cannot yield the solvable type VI local action. -/
theorem rankOne_global_perfect_regular_local_catalogue
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRemainder Q split 1 ≤ localKernel Q 1 ∧
      (simpleRemainder Q split 1).comap (MarkedLocal.endpointMap Q e 1) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) 1) ∧
      Nonempty (MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R) ∧
      (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1) ∧
      ¬ Group.IsSolvable (localGroup Q split 1) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  exact ⟨MarkedLocal.perfect_remainder_le_kernel Q e hf split 1 hp T₁ hT₁,
    MarkedLocal.perfect_remainder_comap Q e hf split 1 hp T₁ hT₁,
    ⟨MarkedLocal.originalPerfectRankOneEquiv Q e hf split 1 hp T₁ hT₁⟩,
    MarkedLocal.perfect_root_projection_ker_eq_center Q e hf split 1 hp T₁ hT₁,
    MarkedLocal.perfect_local_not_isSolvable Q e hf split 1 hp T₁ hT₁⟩

/-- Both original endpoint remainders satisfy (2B) on the literal selected Chapter 12 pair. -/
theorem rankOne_global_perfect_remainders
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  have h0 := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
  have h1 := MarkedLocal.perfect_remainder_le_kernel Q e hf split 1 hp T₁ hT₁
  intro i
  fin_cases i
  · exact ⟨h0,MarkedLocal.remainder_comap_of_containment Q e split 0 h0⟩
  · exact ⟨h1,MarkedLocal.remainder_comap_of_containment Q e split 1 h1⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
