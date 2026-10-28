module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.NormalQuotients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.Irreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericNormalGeneration

/-!
# Irreducibility and normal quotients for the selected generic pair

The literal selected pair ![L,R], with S = O₂(N_G(L) ∩ H), gives an
irreducible finite quotient whose two marked parabolics are maximal and
have trivial normal cores. The existing perfect-factor normal-generation
argument further proves that every nontrivial normal subgroup supplements
the actual Borel and U, and has two-group quotient.

The original preparation supplies F.1.1, so local characteristic two is
not an extra recognition premise. Perfectness of the selected R is exactly
the premise in the Chapter12 generic comparison consumer. The marked
quotient and split inputs still belong to qt-dgs85-apartment-exchange;
full minimality and all seven regular Lie rows remain with this family.
The generic-global and DGS assembly owners retain all earlier premise
discharge and the independent exceptional and extension branches.

Source: DGS Theorem D, printed p.224 and its minimality caveat on pp.80–81;
Aschbacher–Smith 5.2.6, pp.650–651, and the Chapter12 use on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The selected-factor consumer supplies irreducibility and both faithful
maximal marked parabolics without extra hypotheses. -/
theorem prepared_quotient_irreducible
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    ¬ Commute (Q.simple 0) (Q.simple 1) ∧
      ∀ i, IsCoatom (Q.tits.standardParabolic {Q.simple i}) ∧
        (Q.tits.standardParabolic {Q.simple i}).normalCore = ⊥ := by
  have hh := d.hypothesisF11 h hTH
  exact ⟨quotient_simple_not_commute hh Q split, fun i =>
    ⟨Q.parabolic_isCoatom i, quotient_parabolic_normalCore_eq_bot hh Q split i⟩⟩

/-- Both original endpoint images are supplemented by every nontrivial
normal subgroup of the actual selected quotient. -/
theorem prepared_quotient_normal_subgroup_sup_parabolic
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits)
    (V : Subgroup ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D))
    [V.Normal] (hne : V ≠ ⊥) (i : Fin 2) :
    V ⊔ ((parabolic ![L,R] (Global.sourceS L H) i).subgroupOf
      (generated ![L,R] (Global.sourceS L H))).map Q.q = ⊤ :=
  quotient_normal_subgroup_sup_parabolic (d.hypothesisF11 h hTH) Q split V hne i
/-- On the actual perfect-factor branch, every nontrivial normal subgroup
supplements the original Borel and its specified U; its quotient is a
two-group. The previous consumer theorem discharges normal generation. -/
theorem prepared_quotient_normal_subgroup_structure
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits)
    (V : Subgroup ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D))
    [V.Normal] (hne : V ≠ ⊥) :
    V ⊔ Q.tits.B = ⊤ ∧ V ⊔ split.U = ⊤ ∧
      IsPGroup 2 (((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D) ⧸ V) := by
  have hc := quotient_parabolic_core_selfCentralizing (d.hypothesisF11 h hTH) Q
  have hgen : split.unipotentClosure = ⊤ :=
    (prepared_quotient_normal_generation d h hTH hR Q split).1
  exact ⟨Q.normal_subgroup_sup_borel split hc V hne,
    Q.normal_subgroup_sup_unipotent split hc hgen V hne,
    Q.quotient_isPGroup_of_ne_bot split hc hgen V hne⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
