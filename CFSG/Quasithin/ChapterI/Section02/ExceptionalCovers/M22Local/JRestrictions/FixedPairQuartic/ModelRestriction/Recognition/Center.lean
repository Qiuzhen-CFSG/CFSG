module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.ModelRestriction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center

/-!
# Center recognition for the literal fixed-pair core

The native pair core has order 64 and its squares lie in the literal sign layer
of the intrinsic signed extension. Applying the concrete counting reduction
therefore identifies its center. The trivial-actor branch is also supplied
separately.

The earlier hexad `Recognition` is the existing source input retained by the
quartic-hexad assembly. Source: Aschbacher–Smith, combined manuscript
(1 March 2004), I.2.2(6a), printed pp.410 and 412 (PDF pp.421 and 423).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open EvenCliffordSix.SplitExtension.ElementaryRestrictions
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K] [Finite K] [IsCyclic (center K)]
variable (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
variable (rec : Recognition e m22Hexad234_mem)

/-- The literal core image satisfies the center reduction with explicit
counting premises. This wrapper is retained for callers that provide those
estimates directly. -/
theorem coreImage_center_of_counts
    (hnonrad : ∀ x : EvenCliffordSix.SplitExtension,
      x ^ 2 ∈ EvenCliffordSix.SplitExtension.sign → x.right ≠ 1 →
      Nat.card (squareCommutants x) < 64)
    (hrad : ∀ (m : EvenCliffordSix.Model) (x : EvenCliffordSix.SplitExtension),
      m ∉ center EvenCliffordSix.Model →
      x ^ 2 ∈ EvenCliffordSix.SplitExtension.sign → x.right ≠ 1 →
      Commute (EvenCliffordSix.SplitExtension.radicalEmbedding m) x →
      Nat.card (mixedCandidates m x) < 64) :
    center (coreImage e hZ rec) = centralIn (coreImage e hZ rec) :=
  center_eq_centralIn_of_counts hnonrad hrad _
    (coreImage_card e hZ rec) (coreImage_square e hZ rec)

/-- The literal core image has the intrinsic center calculation. -/
theorem coreImage_center :
    center (coreImage e hZ rec) = centralIn (coreImage e hZ rec) :=
  center_eq_centralIn _ (coreImage_contains_central e hZ rec)
    (coreImage_card e hZ rec) (coreImage_square e hZ rec)

omit [IsCyclic (center K)] in
/-- The trivial-actor case of the actual fixed-pair core. -/
theorem coreImage_center_of_actor_trivial
    (hact : ∀ x ∈ coreImage e hZ rec, x.right = 1) :
    center (coreImage e hZ rec) = centralIn (coreImage e hZ rec) :=
  center_eq_centralIn_of_actor_trivial _ (coreImage_card e hZ rec) hact

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
