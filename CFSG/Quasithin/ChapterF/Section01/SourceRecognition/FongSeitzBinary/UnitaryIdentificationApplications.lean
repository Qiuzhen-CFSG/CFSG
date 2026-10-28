module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCommutators

/-!
# Original unitary quotients in the source quadrangle and Chapter 12

The selected original factor supplies its actual SU3 or PSU3 quotient.
The canonical root-generated group is identified with that same carrier,
not with an independent local-model tag. On the special branch, the scalar
projection is retained in the square identifying the faithful local image.
This discharges the local unitary-model input of the quadrangle mixed
commutator theorem and supplies the literal selected Chapter 12 pair.

The (2B) remainder containment, reflection, original linear actor and
special-radical clauses remain explicit source inputs. The earlier finite
marked quotient and full-Borel amalgam marking belong to the apartment
producer; this does not assert the seven-row recognition assembly.
Source: Fong--Seitz I (5C), (6A)(c), pp.25--26,37;
DGS (11.8), pp.175--176; Aschbacher--Smith 12.2.2 and F.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The projective unitary branch of the actual selected perfect factor. -/
theorem prepared_projectiveUnitary_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      Nat.card (Panel Q 1) ≠ 9 ∧
      ¬ Group.IsSolvable (localGroup Q split 1) ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨MarkedLocal.originalProjectiveUnitaryRankOneEquiv Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ,
    MarkedLocal.projectiveUnitary_panel_card_ne_nine Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ,
    MarkedLocal.projectiveUnitary_local_not_isSolvable Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ, ?_⟩
  intro hV
  exact ⟨MarkedLocal.projectiveUnitaryLocalEquiv Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ hV,
    MarkedLocal.originalProjectiveUnitaryRankOneEquiv_projection Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ hV⟩

/-- The special unitary branch retains its actual scalar central cover. -/
theorem prepared_specialUnitary_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (R ⧸ pCore 2 R) ≃* J.specialSubgroup)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* J.specialSubgroup,
      Nat.card (Panel Q 1) ≠ 9 ∧
      ¬ Group.IsSolvable (localGroup Q split 1) ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          ∀ r, J.specialToProjective (a r) = b (MarkedLocal.originalRootProjection Q e split 1 r) := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨MarkedLocal.originalSpecialUnitaryRankOneEquiv Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ,
    MarkedLocal.specialUnitary_panel_card_ne_nine Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ,
    MarkedLocal.specialUnitary_local_not_isSolvable Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ, ?_⟩
  intro hV
  exact ⟨MarkedLocal.specialUnitaryLocalEquiv Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ hV,
    MarkedLocal.originalSpecialUnitaryRankOneEquiv_projection Q e hf split 1 hp T₁ hT₁ J hm hc hconj μ hV⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal selected Chapter 12 PSU3 branch, with no independent local tag. -/
theorem rankOne_global_projectiveUnitary_local_identification
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      Nat.card (Panel Q 1) ≠ 9 ∧
      ¬ Group.IsSolvable (localGroup Q split 1) ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_projectiveUnitary_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hp J hm hc hconj μ Q e split

/-- The literal selected Chapter 12 SU3 branch, preserving the scalar quotient. -/
theorem rankOne_global_specialUnitary_local_identification
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 0 < m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (R ⧸ pCore 2 R) ≃* J.specialSubgroup)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* J.specialSubgroup,
      Nat.card (Panel Q 1) ≠ 9 ∧
      ¬ Group.IsSolvable (localGroup Q split 1) ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          ∀ r, J.specialToProjective (a r) = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_specialUnitary_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hp J hm hc hconj μ Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open scoped MatrixGroups
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include h in
/-- Discharge the quadrangle's local PSU3 marking from the actual original
SU3 quotient, keeping the full SU3 root actor and its scalar projection. -/
theorem marked_unitary_commutators_of_special_factor
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (hp : Group.IsPerfect (L j))
    (ν : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ∃ a : rankOne Q split j ≃* J.specialSubgroup,
      ∃ b : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        (∀ r, J.specialToProjective (a r) = b (RootLocalCover.projection Q split j r)) ∧
        ∃ μ : rankOne Q split i ≃* SL(2,K),
          (∀ r : rankOne Q split i, ∃ x : (S ⊔ L i).subgroupOf (parabolic L S i),
            MarkedLocal.endpointMap Q e i x.val = r ∧ μ r = f x) ∧
          ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) ∧
          ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
            (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
          ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
            (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  let a := MarkedLocal.specialUnitaryRankOneEquiv Q e h split j hp T hT J hn hE hconj ν
  let b := MarkedLocal.specialUnitaryLocalEquiv Q e h split j hp T hT J hn hE hconj ν hVj
  refine ⟨a,b,?_,?_⟩
  · intro r
    rw [MarkedLocal.specialUnitaryLocalEquiv_projection,
      MarkedLocal.specialUnitaryRankOneEquiv_apply]
  · exact marked_unitary_commutators Q e h split J hn hK hE
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj) hJ
      hm i j hij hVi hVj s f hf hk b hderived hfrattini

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
