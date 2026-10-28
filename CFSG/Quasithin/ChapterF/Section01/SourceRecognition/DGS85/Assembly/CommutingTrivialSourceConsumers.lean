module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialBinaryConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TheoremB

/-!
# Original consumers of the commuting-trivial source theorem

DGS 9.10 supplies both adjacent fields of order two. Transporting its actual
intrinsic markings gives both original starred quotients and the full
parabolic conclusion of 13.1(b), with the original quotient representatives.
The original quintic index and the selected generic nonsolvable endpoint
then exclude this branch in their respective quasithin consumers.

The full intrinsic rank-one catalogue, reverse Chapter 8 linear output and
three concrete binary model witnesses remain explicit source inputs. The
numerical field-two conclusion, Cartan geometry and page 150 contradiction
are proved internally. The chosen-module application preserves its same
selected perfect subgroup R. Theorem B is re-exported at this assembly boundary.

Source: DGS, *Groups and Graphs* (1985), Theorem B, 8.4--8.7, 9.10,
and 13.1, pp.102,137--150,191; Aschbacher--Smith F.1.9--12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
universe u

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Reduction
section Reduced
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S


/-- Source 9.10 marks both original starred quotients over the binary field. -/
theorem reduced_critical_binary_starred_quotients_of_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex Γ,
      (graph Γ).Adj z a' → IsCriticalPair Γ z beta →
      ⁅Z Γ z,Z Γ beta⁆ = ⊥ →
      ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b Γ = 3 ∧ Nonempty ((graphLocalGroup Γ z ⧸
          pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,F)))
    (Mα : BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) :
    b Γ = 3 ∧ ∀ i : Bool,
      Nonempty ((CommutingThreeProfile.ReducedLayer.star L S i ⧸
        pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_of_catalogue (L := L) (S₀ := S)
      (a := a) (beta := beta) (a' := a') h models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨hb3,adjacent_field_two_starred_quotients h hab ea eb (hK.trans hF.symm) hF⟩

/-- The full original 13.1(b) conclusion, with source 9.10's field orders discharged. -/
theorem reduced_critical_binary_full_parabolics_of_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex Γ,
      (graph Γ).Adj z a' → IsCriticalPair Γ z beta →
      ⁅Z Γ z,Z Γ beta⁆ = ⊥ →
      ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b Γ = 3 ∧ Nonempty ((graphLocalGroup Γ z ⧸
          pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,F)))
    (Mα : BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) :
    b Γ = 3 ∧
      ∃ e : ∀ i : Bool, (CommutingThreeProfile.ReducedLayer.star L S i ⧸
          pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2),
        commonBorel L S = S ∧ G₀ L S = generated L S ∧
        (∀ i : Bool, ∃ f : (parabolic L S (if i then 1 else 0) ⧸
            pCore 2 (parabolic L S (if i then 1 else 0))) ≃* SL(2,ZMod 2),
          (∀ x : L (if i then 1 else 0),
            f (QuotientGroup.mk (inclusion (show L (if i then 1 else 0) ≤
              parabolic L S (if i then 1 else 0) from le_sup_left.trans le_sup_left) x)) =
              e i (QuotientGroup.mk (CommutingThreeProfile.ReducedLayer.originalActor
                (L := L) (S := S) i x))) ∧
          starredParabolic L S (if i then 1 else 0) = parabolic L S (if i then 1 else 0) ∧
          Group.IsSolvable (parabolic L S (if i then 1 else 0))) ∧
        ∀ v : Vertex Γ,
          graphLocalGroup Γ v = stabilizer Γ v ∧
          Nonempty ((stabilizer Γ v ⧸ pCore 2 (stabilizer Γ v)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_of_catalogue (L := L) (S₀ := S)
      (a := a) (beta := beta) (a' := a') h models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨hb3,adjacent_field_two_full_parabolics h hab ea eb (hK.trans hF.symm) hF⟩

end Reduced

section Quintic
variable {G : Type u} [Group G] {P R S : Subgroup G}
local notation "Γ" => Reduction.reducedFamily ![P,R] S

/-- The actual original index five excludes the commuting-trivial source branch. -/
theorem no_reduced_critical_commuting_trivial_of_local_quintic
    (h : HypothesisF11 ![P,R] S) (hfive : S.relIndex P = 5)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex Γ,
      (graph Γ).Adj z a' → IsCriticalPair Γ z beta →
      ⁅Z Γ z,Z Γ beta⁆ = ⊥ →
      ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b Γ = 3 ∧ Nonempty ((graphLocalGroup Γ z ⧸
          pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,F)))
    (Mα : BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) : False := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_of_catalogue h models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact no_adjacent_field_two_of_local_quintic h hfive hab ea eb (hK.trans hF.symm) hF

end Quintic
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "Γ" => Reduction.reducedFamily ![L,R] (sourceS L H)

/-- The same selected generic pair excludes the original commuting-trivial branch. -/
theorem no_commuting_trivial_source_of_catalogue
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex Γ,
      (graph Γ).Adj z a' → IsCriticalPair Γ z beta →
      ⁅Z Γ z,Z Γ beta⁆ = ⊥ →
      ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b Γ = 3 ∧ Nonempty ((graphLocalGroup Γ z ⧸
          pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,F)))
    (Mα : BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) : False := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_of_catalogue (d.hypothesisF11 h hTH) models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact d.no_commuting_trivial_binary_fields h hTH hp hab ea eb (hK.trans hF.symm) hF

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B R : Subgroup G}
local notation "Γ" => Reduction.reducedFamily ![L,R] (Global.sourceS L H)

/-- The chosen-module application keeps its selected perfect R and derives
both binary field orders from the original source hypotheses. -/
theorem rankOne_no_commuting_trivial_source_of_catalogue
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅ChapterF.Source.DGS85.V Γ beta 1 ⊓ Q Γ a',ChapterF.Source.DGS85.V Γ a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex Γ,
      (graph Γ).Adj z a' → IsCriticalPair Γ z beta →
      ⁅Z Γ z,Z Γ beta⁆ = ⊥ →
      ⁅ChapterF.Source.DGS85.V Γ a' 1 ⊓ Q Γ beta,ChapterF.Source.DGS85.V Γ beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b Γ = 3 ∧ Nonempty ((graphLocalGroup Γ z ⧸
          pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,F)))
    (Mα : BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) : False := by
  exact d.no_commuting_trivial_source_of_catalogue
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
