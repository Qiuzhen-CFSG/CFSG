module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates

/-!
# Every perfect original factor and its actual root-generated local cover

Exhaust the original F.1.1 rank-one catalogue, using its actual model
isomorphisms. The canonical simple root covers the quotient Sylow in the
linear, Suzuki, special-unitary and projective-unitary cases. The dihedral
case contradicts original perfectness. Thus the same lifted projection
identifies the canonical root-generated group with L_i/O2(L_i), and its
full panel-action kernel is exactly its center, before (2B).

The actual local permutation group is consequently nonsolvable. This
excludes the solvable type VI case at every perfect original endpoint,
without assuming (2B), a local-model witness, or a field bound. Once (2B)
is proved, the original whole-root cover is also L_i/O2(L_i), with its
literal representatives. The Chapter 12 application uses the selected R
and the same independent quotient and full-Borel amalgam marking.

Source: Fong--Seitz I (2A), (5B)--(5C), pp.7--9,25--26;
Aschbacher--Smith F.1.1--3 and 12.2.2. The nonperfect endpoints, unitary
(2B), rank-two row selection and final marked amalgam assembly remain open.
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

/-- Exhaust the actual source catalogue to cover the original quotient Sylow. -/
theorem perfect_simpleRootSylowProjection_surjective :
    Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT) := by
  let : Group.IsPerfect (L i) := hp
  cases h.quotient i with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact linear_simpleRootSylowProjection_surjective Q e h split i hp T hT μ
  | suzuki m hm =>
    exact suzuki_simpleRootSylowProjection_surjective Q e h split i hp T hT hm.some
  | projective_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact projectiveUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj μ
  | special_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    exact specialUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj μ
  | dihedral hm =>
    exact (not_perfect_dihedral_model hm.some inferInstance).elim

/-- No local-model tag remains: the canonical roots generate the original quotient. -/
def perfectRankOneEquiv : rankOne Q split i ≃* (L i) ⧸ pCore 2 (L i) :=
  rankOneQuotientEquiv Q e h split i hp T hT
    (perfect_simpleRootSylowProjection_surjective Q e h split i hp T hT)

@[simp] theorem perfectRankOneEquiv_apply (r : rankOne Q split i) :
    perfectRankOneEquiv Q e h split i hp T hT r =
      QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r) :=
  rankOneQuotientEquiv_apply Q e h split i hp T hT _ r

include e h hp hT in
theorem perfect_root_projection_ker_eq_center :
    (RootLocalCover.projection Q split i).ker = center (rankOne Q split i) :=
  root_projection_ker_eq_center_of_full_sylow Q e h split i hp T hT
    (perfect_simpleRootSylowProjection_surjective Q e h split i hp T hT)

include e h hp hT in
/-- The solvable type VI local action is impossible at a perfect original factor. -/
theorem perfect_local_not_isSolvable : ¬ Group.IsSolvable (localGroup Q split i) :=
  localGroup_not_isSolvable_of_full_sylow Q e h split i hp T hT
    (perfect_simpleRootSylowProjection_surjective Q e h split i hp T hT)

def originalPerfectRankOneEquiv : originalRankOne Q e split i ≃* (L i) ⧸ pCore 2 (L i) :=
  (originalRankOneEquiv Q e split i).trans (perfectRankOneEquiv Q e h split i hp T hT)

@[simp] theorem originalPerfectRankOneEquiv_apply (r : originalRankOne Q e split i) :
    originalPerfectRankOneEquiv Q e h split i hp T hT r =
      QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r)) := by
  rw [originalPerfectRankOneEquiv, MulEquiv.trans_apply, perfectRankOneEquiv_apply]

def originalPerfectCoverEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
      (L i) ⧸ pCore 2 (L i) := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact (originalRootCoverEquiv Q e h split i hV).symm.trans
    (originalPerfectRankOneEquiv Q e h split i hp T hT)

@[simp] theorem originalPerfectCoverEquiv_mk
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalPerfectCoverEquiv Q e h split i hp T hT hV
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r)) := by
  let := originalRadicalInClosure_normal Q e h split i
  rw [← originalRootCoverEquiv_apply Q e h split i hV r]
  change originalPerfectRankOneEquiv Q e h split i hp T hT
    ((originalRootCoverEquiv Q e h split i hV).symm
      (originalRootCoverEquiv Q e h split i hV r)) = _
  rw [MulEquiv.symm_apply_apply, originalPerfectRankOneEquiv_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The selected perfect second factor has its original quotient as canonical
root group and cannot yield the solvable type VI local action. -/
theorem rankOne_global_perfect_local_catalogue
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Nonempty (MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R) ∧
      (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1) ∧
      ¬ Group.IsSolvable (localGroup Q split 1) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  exact ⟨⟨MarkedLocal.originalPerfectRankOneEquiv Q e hf split 1 hp T₁ hT₁⟩,
    MarkedLocal.perfect_root_projection_ker_eq_center Q e hf split 1 hp T₁ hT₁,
    MarkedLocal.perfect_local_not_isSolvable Q e hf split 1 hp T₁ hT₁⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
