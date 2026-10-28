module

public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# The Suzuki covering step in general FF recognition

A finite perfect group with trivial two-core whose central quotient is an
actual Suzuki matrix group is itself isomorphic to that same group. Apply
cyclic odd-Sylow transfer to the composite of the central projection and
the specified model equivalence. The resulting equivalence agrees with
this composite on every element, so it identifies the original component.

Source: Aschbacher–Smith, B.1.13, printed p.73, and I.1.2, printed p.407.
The Suzuki parameter is retained exactly: the field order is 2^(2m+1),
with m ≥ 1. This family needs no FF classification to prove the required
Lie-type conclusion.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional

variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

/-- The literal central projection, followed by the given Suzuki identification. -/
noncomputable def suzukiCover {m : ℕ} (e : L ⧸ center L ≃* SuzukiMatrixGroup m) :
    PerfectCentralCovering.Cover L (SuzukiMatrixGroup m) where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact (show e (QuotientGroup.mk x) = 1 from hx).trans (map_one e).symm

/-- All central kernels disappear: the original group is the concrete Suzuki group. -/
noncomputable def suzukiEquiv (hc : pCore 2 L = ⊥) {m : ℕ} (hm : 1 ≤ m)
    (e : L ⧸ center L ≃* SuzukiMatrixGroup m) : L ≃* SuzukiMatrixGroup m :=
  (suzukiCover e).equivOfPCoreEqBotOfCyclicSylow hc fun p hp hp2 P => by
    let : Fact p.Prime := ⟨hp⟩
    exact suzukiSylow_isCyclic_of_ne_two (by omega) hp2 P

/-- The equivalence retains the exact original quotient and model map. -/
@[simp] theorem suzukiEquiv_apply (hc : pCore 2 L = ⊥) {m : ℕ} (hm : 1 ≤ m)
    (e : L ⧸ center L ≃* SuzukiMatrixGroup m) (x : L) :
    suzukiEquiv hc hm e x = e (QuotientGroup.mk x) := by
  unfold suzukiEquiv
  rw [PerfectCentralCovering.Cover.equivOfPCoreEqBotOfCyclicSylow_apply]
  rfl

/-- Consumer of the catalogue's complete Suzuki clause, with its parameter bound. -/
theorem suzuki_recognition (hc : pCore 2 L = ⊥)
    (h : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (L ⧸ center L ≃* SuzukiMatrixGroup m)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (L ≃* SuzukiMatrixGroup m) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h
  exact ⟨m, hm, ⟨suzukiEquiv hc hm e⟩⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
