module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction

/-!
# Normal elementary subgroups in the maximal J₄ Sylow-overgroup argument

The source classification has three relevant local branches. Their normal
elementary subgroups have orders two, eight, and 2048. These contracts separate
the existence of such a subgroup from recognition of the order-eight branch.
The order-two and order-2048 branches can instead use the already certified
involution centralizer and Mathieu kernel, respectively.

Neither contract is asserted here. In particular, the existence contract is
not a consequence of introducing the three ATLAS carriers. Its proof requires
the Sylow-overgroup analysis cited by Aschbacher–Smith, A.3.12, printed
pp.47–48: Aschbacher, *Overgroups of Sylow subgroups in sporadic groups*,
Memoirs AMS 60 (1986), no.343. GLS3 Table 5.3i supplies local descriptions,
but not exhaustive coverage. All normality below is relative to M.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

/-- The structural existence step for arbitrary maximal Sylow overgroups.
This is an unproved source input, without ambient simplicity assumptions. -/
@[expose] def NormalElementaryStructure : Prop :=
  ∀ (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M →
    ∃ E : Subgroup M, E.Normal ∧ IsElementaryAbelian 2 E ∧
      (Nat.card E = 2 ∨ Nat.card E = 8 ∨ Nat.card E = 2048)

/-- Recognition of the order-eight branch must construct an isomorphism
with the literal ATLAS max4 word subgroup, not merely an extension label. -/
@[expose] def NormalEightRecognition : Prop :=
  ∀ (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M →
    ∀ E : Subgroup M, E.Normal → IsElementaryAbelian 2 E → Nat.card E = 8 →
      Nonempty (M ≃* Janko4.LocalStructure.SymmetricLinear.max4Subgroup)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
