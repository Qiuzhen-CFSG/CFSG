module

public import Stellmacher.Recognition.NormalEightTerminalCoreSetup
public import Stellmacher.Recognition.NormalEightTerminalCoreOrbit
public import Stellmacher.Recognition.NormalEightTerminalOutsideAffine
public import Stellmacher.Recognition.NormalFourNonnormalCoreInvolutionFusion
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.NormalFourFusion
public import Theory.SpecificGroups.AffineEight.Basic

/-!
# Assembling the terminal fusion-or-affine alternative

Z-star supplies a distinct Sylow conjugate of the central involution. An
inside-core conjugate fuses into the noncentral part of the normal four;
the two noncentral elements are already Sylow-conjugate. The outside-core
branch instead uses the affine-eight identification.

The conditional assembly first isolates these two geometric inputs. The final
theorem discharges both using the order-sixteen core geometry and the
outside-core affine identification. Its elementary-subgroup hypothesis excludes
normal elementary eights. Source: Janko–Thompson (1970), Lemma 4.1, printed
p.393, final two paragraphs.
-/

namespace Stellmacher.Recognition.NormalEightTerminalFusionAlternative

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Assemble the normal-only alternative from the quotient involution orbit
and the outside-core affine identification. -/
public theorem fusion_or_affine_of_core_geometry [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hinside : ∀ t : S, orderOf t = 2 → t ∈ omegaCorePreimage S →
      ∃ v ∈ fourImage S W, IsConj (omegaQuotientHom S t) v)
    (houtside : ∀ z : W, orderOf (z : S) = 2 → (z : S) ∈ center S →
      ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
        IsConj ((z : S) : G) (t : G) → Nonempty (S ≃* AffineEight.Model)) :
    (∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) ∨
      Nonempty (S ≃* AffineEight.Model) := by
  obtain ⟨z, hz, hzc⟩ :=
    NormalEightTerminalCoreSetup.exists_central_involution_in_four S hZ W hW hno
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S (z : S) hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq ((z : S) : G)).trans
      ((orderOf_coe (z : S)).trans hz)
  by_cases htcore : t ∈ omegaCorePreimage S
  · obtain ⟨u, hu, huz, htu⟩ := noncentral_four_ambient_fusion_of_quotient_orbit
      S hZ W z hz hzc t ht htz (hinside t ht htcore)
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    exact Or.inl (normal_four_fusion_of_central_isConj W hW
      (four_not_le_center_of_card_omega_one_center_eq_two hZ W hW)
      z hzc hz1 (S : Subgroup G).subtype u hu huz (hzt.trans htu))
  · exact Or.inr (houtside z hz hzc t ht htcore hzt)

/-- In the terminal order-thirty-two case, the nonidentity elements of the
normal four fuse in the ambient simple group, or the Sylow subgroup is affine
cyclic-eight. All core geometry follows from the absence of normal elementary
eights and the actual quotient-core hypotheses. -/
public theorem fusion_or_affine [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2) :
    (∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) ∨
      Nonempty (S ≃* AffineEight.Model) := by
  exact fusion_or_affine_of_core_geometry hns S hZ W hW hno
    (NormalEightTerminalCoreOrbit.core_involution_quotient_orbit
      hN S hZ W hW hno hunique hnormal hcore)
    (NormalEightTerminalOutsideAffine.nonempty_mulEquiv_affineEight_of_outside_core_isConj
      hN S hS hZ W hW hno hunique hnormal hcore hindex
      (NormalEightTerminalCoreOrbit.omegaCorePreimage_center_card
        hN S hZ W hW hno hunique hnormal hcore)
      (NormalEightTerminalCoreOrbit.omegaCorePreimage_elementary_card_lt_eight
        hN S hZ W hW hno hunique hnormal hcore))

end Stellmacher.Recognition.NormalEightTerminalFusionAlternative
