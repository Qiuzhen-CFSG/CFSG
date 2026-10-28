module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MinimalNormal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericIrreducibility

/-!
# Minimal-normal reduction for the selected generic source pair

For the actual pair ![L,R] and S = O₂(N_G(L) ∩ H), identify the quotient's
two-residual with the join of the original two factor images. Perfectness
of L follows from local-family membership; perfectness of the selected R
is precisely the existing Chapter12 comparison premise. Thus the residual
is perfect, is the unique minimal normal subgroup, and has trivial ambient
centralizer. It is isomorphic to a positive power of a nonabelian simple
group, and the same original S image supplements it.

All endpoint and Borel markings remain those of the original SourceQuotient.
The earlier apartment and split inputs belong to qt-dgs85-apartment-exchange.
This removes perfectness and minimal-normal selection as additional premises
for the generic consumer, but does not prove that the simple power has one
factor or identify a Lie row. The full Fong–Seitz reduction and seven-row
recognition remain with this task; qt-dgs85-source-assembly and the original
generic-global owner retain every earlier premise discharge and the other
exceptional and extension branches.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D on p.224;
Aschbacher–Smith 5.2.6, pp.650–651, and its Chapter12 application, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The existing selected-factor premises supply a perfect two-residual,
with its literal two original factor images retained. -/
theorem prepared_quotient_perfect_residual
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) :
    pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D) =
      (L.subgroupOf (generated ![L,R] (Global.sourceS L H))).map Q.q ⊔
        (R.subgroupOf (generated ![L,R] (Global.sourceS L H))).map Q.q ∧
      Group.IsPerfect (pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D)) := by
  apply quotient_perfect_residual (d.hypothesisF11 h hTH)
  intro i
  fin_cases i
  · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
  · exact hR

/-- The unique minimal normal subgroup is the literal two-residual. Its
quotient is a two-group and the original S image is a supplement. -/
theorem prepared_quotient_minimal_normal
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    let Y := (generated ![L,R] (Global.sourceS L H)) ⧸ Q.D
    let K := pResidual 2 Y
    K ≠ ⊥ ∧ Group.IsPerfect K ∧
      (∀ V : Subgroup Y, V.Normal → V ≠ ⊥ → K ≤ V) ∧
      centralizer (K : Set Y) = ⊥ ∧ IsPGroup 2 (Y ⧸ K) ∧
      K ⊔ ((Global.sourceS L H).subgroupOf
        (generated ![L,R] (Global.sourceS L H))).map Q.q = ⊤ := by
  dsimp only
  have hc := quotient_parabolic_core_selfCentralizing (d.hypothesisF11 h hTH) Q
  have hgen : split.unipotentClosure = ⊤ :=
    (prepared_quotient_normal_generation d h hTH hR Q split).1
  have hp := (prepared_quotient_perfect_residual d h hTH hR Q).2
  have hne := Q.twoResidual_ne_bot split
  refine ⟨hne, hp, ?_, Q.twoResidual_centralizer_eq_bot split hc hgen hp,
    isPGroup_quotient_pResidual 2, ?_⟩
  · intro V hV hn
    let := hV
    exact Q.twoResidual_le_normal split hc hgen V hn
  · rw [prepared_quotient_sourceS_image_eq_unipotent d h hTH Q split]
    exact Q.normal_subgroup_sup_unipotent split hc hgen _ hne

/-- The actual source quotient's residual is a positive direct power of a
perfect simple subgroup, through an explicit multiplicative equivalence. -/
theorem prepared_quotient_simple_power
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    ∃ C : Subgroup (pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D)),
      IsSimpleGroup C ∧ Group.IsPerfect C ∧ ∃ k : ℕ, 0 < k ∧
        Nonempty (pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D) ≃*
          (Fin k → C)) :=
  Q.twoResidual_simple_power split
    (quotient_parabolic_core_selfCentralizing (d.hypothesisF11 h hTH) Q)
    (prepared_quotient_normal_generation d h hTH hR Q split).1
    (prepared_quotient_perfect_residual d h hTH hR Q).2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
