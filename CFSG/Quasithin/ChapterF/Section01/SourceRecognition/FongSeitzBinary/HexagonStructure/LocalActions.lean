module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.NonabelianRadicals

/-!
# Original and geometric applications of the source local actions

The original endpoint acts on the same finite quotient panel through its
given amalgam equivalence. Its kernel is the pullback of the actual K_i
under the original endpoint map. The group generating source L_i uses the
literal original S image and its conjugate. The earlier local-section
premise is stated on that same S image; it supplies both the faithful
R_i quotient comparison and the actual action on the canonical radical.

These applications also cover the universal/geometric marking: X is not
assumed finite and no map from that completion to the original ambient
generated group is introduced. Source: Fong--Seitz I Section 5, pp.25--28,
as used in (6C)--(6E), and DGS Theorem D, printed p.224. Construction of
the earlier local-section and source-reflection premises stays with the
source reduction; the local-type exclusions are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- The actual original endpoint permutation action under the supplied marking. -/
def originalEndpointAction (i : Fin 2) : parabolic L S i →* Equiv.Perm (Panel Q i) :=
  (endpointAction Q i).comp (MarkedLocal.endpoint Q e i).toMonoidHom

/-- Pulling K_i back through the original endpoint map gives exactly its action kernel. -/
theorem originalEndpointAction_ker (i : Fin 2) :
    (originalEndpointAction Q e i).ker =
      (localKernel Q i).comap (MarkedLocal.endpointMap Q e i) := by
  change (endpointAction Q i).ker.comap (MarkedLocal.endpoint Q e i).toMonoidHom =
    ((localKernel Q i).subgroupOf (Q.tits.standardParabolic {Q.simple i})).comap
      (MarkedLocal.endpoint Q e i).toMonoidHom
  rw [localKernel_subgroupOf, normalCore_eq_ker]
  rfl

/-- The numerator defining source L_i uses the same original Sylow image. -/
theorem marked_localClosure (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    localClosure Q split i = (MarkedLocal.sylowMap Q e h).range ⊔
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) := by
  rw [MarkedLocal.sylow_range Q e h split, localClosure,
    unipotentConjugate_eq split (Q.simple i) n hn]

/-- The source kernel premise is on the literal original radical, and gives
the canonical R_i/(R_i intersect K_i) comparison with the actual source L_i. -/
def marked_rankOneLocalEquiv (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i)
    (hK : (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) ≤ localKernel Q i) :
    rankOne Q split i ⧸ (rankOneAction Q split i).ker ≃* localGroup Q split i :=
  rankOneLocalEquiv Q split i ((marked_radical_eq h Q e split i n hn).symm ▸ hK)

/-- The quotient comparison preserves the literal permutation of every panel coset. -/
@[simp] theorem marked_rankOneLocalEquiv_apply (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i)
    (hK : (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) ≤ localKernel Q i)
    (r : rankOne Q split i) :
    (marked_rankOneLocalEquiv Q e h split i n hn hK (QuotientGroup.mk r) :
      Equiv.Perm (Panel Q i)) = rankOneAction Q split i r := by
  exact rankOneLocalEquiv_apply Q split i _ r

/-- The same earlier kernel premise constructs the actual source radical action. -/
def marked_radicalAction (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i)
    (hK : (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) ≤ localKernel Q i) :
    rankOne Q split i →* MulAut (simpleRemainder Q split i) :=
  radicalAction Q split i ((marked_radical_eq h Q e split i n hn).symm ▸ hK)

/-- Inverting the actor translates this action to Fong--Seitz right conjugation. -/
theorem marked_radicalAction_right_conjugation (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i)
    (hK : (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) ≤ localKernel Q i)
    (r : rankOne Q split i) (v : simpleRemainder Q split i) :
    (marked_radicalAction Q e h split i n hn hK r⁻¹ v : X ⧸ Q.D) =
      (r : X ⧸ Q.D)⁻¹*v*(r : X ⧸ Q.D) :=
  radicalAction_right_conjugation Q split i _ r v

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
