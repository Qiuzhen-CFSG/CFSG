module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuotientReduction

/-!
# Irreducibility of the original marked source quotient

Transport the self-centralizing two-core condition from each original
F.1.1 parabolic through its literal restricted quotient equivalence. This
proves that the marked quotient parabolics have trivial ambient normal
cores and that their simple reflections do not commute. Every nontrivial
normal subgroup supplements both original parabolic images.

Source: Aschbacher–Smith F.1.1(f), F.1.9–11, printed pp.259–262, and the
split-quotient argument in DGS, Groups and Graphs, Part II, p.224. This
discharges irreducibility for the finite quotient; neither the full
minimal-configuration reduction omitted on pp.80–81 nor seven-row
recognition is asserted. The marked quotient and split data retain their
earlier apartment/exchange producer qt-dgs85-apartment-exchange. Only the
quotient is finite; both endpoint equivalences use the same original map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original local characteristic-two hypothesis passes to the marked
standard parabolic through its restricted quotient isomorphism. -/
theorem quotient_parabolic_core_selfCentralizing (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (i : Fin 2) :
    centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}) := by
  let := h.finite_parabolic i
  let e : parabolic L S i ≃* Q.tits.standardParabolic {Q.simple i} :=
    (subgroupOfEquivOfLe (parabolic_le_generated (L := L) (S := S) i)).symm.trans
      (Q.endpointEquiv i)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i))

/-- The quotient acts faithfully on each of its two vertex types. -/
theorem quotient_parabolic_normalCore_eq_bot (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).normalCore = ⊥ :=
  Q.parabolic_normalCore_eq_bot split i (quotient_parabolic_core_selfCentralizing h Q i)

/-- The source rank-two diagram is irreducible with its original markings. -/
theorem quotient_simple_not_commute (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) :
    ¬ Commute (Q.simple 0) (Q.simple 1) :=
  Q.simple_not_commute split (quotient_parabolic_core_selfCentralizing h Q)

/-- Every nontrivial normal subgroup supplements the images of both
original endpoints under the same quotient map. -/
theorem quotient_normal_subgroup_sup_parabolic (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (V : Subgroup ((generated L S) ⧸ Q.D)) [V.Normal] (hne : V ≠ ⊥) (i : Fin 2) :
    V ⊔ ((parabolic L S i).subgroupOf (generated L S)).map Q.q = ⊤ := by
  rw [Q.parabolic_image]
  exact Q.normal_subgroup_sup_parabolic split i
    (quotient_parabolic_core_selfCentralizing h Q i) V hne

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
