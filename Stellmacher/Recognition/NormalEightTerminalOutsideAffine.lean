module

public import Stellmacher.Recognition.NormalEightTerminalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalOutsideCore
public import Theory.GroupTheory.PGroup.OutsideInvolutionAffineGenerators
public import Theory.SpecificGroups.AffineEight.RootInvertingRecognition

/-!
# The affine identification from an outside-core conjugate

Let H be the actual Sylow preimage of the two-core in the odd-core quotient
of the central-omega normalizer. If a conjugate of the central involution
lies outside H, that involution cannot have a square root in the Sylow
center. The cyclic center of H nevertheless supplies a fourth root. The
outside involution must invert it. A second core-normal four and the rank
bound inside H supply an involution whose outside conjugate does not
commute with it. Their product squares to the central involution.

These explicit relations identify the Sylow group with the affine group
of the cyclic group of order eight. The core-center cardinality and the
rank bound inside H are separate geometric inputs; no bound on arbitrary
elementary subgroups of the Sylow group is used.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1, printed p.393,
penultimate paragraph. The quotient and core are the actual objects from
NormalFourCentralOmegaTwo throughout.
-/

namespace Stellmacher.Recognition.NormalEightTerminalOutsideAffine

open Subgroup NormalFourCentralOmegaTwo

/-- An outside-core conjugate of the central involution identifies the Sylow
subgroup with the affine cyclic-eight group, using rank only inside the core. -/
public theorem nonempty_mulEquiv_affineEight_of_outside_core_isConj
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (hcenter : Nat.card (center (omegaCorePreimage S)) = 4)
    (hrankH : ∀ U : Subgroup (omegaCorePreimage S), IsElementaryAbelian 2 U → Nat.card U < 8)
    (z : W) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj ((z : S) : G) (t : G)) : Nonempty (S ≃* AffineEight.Model) := by
  let H := omegaCorePreimage S
  have hWH : W ≤ H := NormalEightNonnormalImage.four_le_omegaCorePreimage hN S hZ W hW hno
  obtain ⟨F, hFe, hF, hFH, hFn, hFW⟩ :=
    NormalEightTerminalCoreSetup.core_distinct_four S W hW hWH hunique hnormal
  let : IsElementaryAbelian 2 F := hFe
  let : IsCyclic (center H) :=
    NormalEightTerminalCoreSetup.omegaCorePreimage_center_isCyclic S hno W hunique hnormal
  have hnoroot : ¬ ∃ r : S, r ∈ center S ∧ r ^ 2 = z := by
    rintro ⟨r, hrc, hrz⟩
    exact hout (mem_omegaCorePreimage_of_isConj_of_central_square
      S hZ hindex z hz hzc r hrc hrz t hconj)
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  obtain ⟨r, x, hro, hrz, hx, hrx, htr, hxt⟩ :=
    exists_affine_generators_of_order_sixteen_core H W F hrankH
      ((card_omegaCorePreimage S).trans hcore) hcenter
      ((index_omegaCorePreimage S).trans hindex) hW hF hWH hFH hFn hFW hunique
      z t z.property hz hzc ht2 hout hnoroot
  exact AffineEight.nonempty_mulEquiv_of_root_inverting_involution hS r x t hro hx ht2
    hrx htr (hxt.trans hrz.symm)

end Stellmacher.Recognition.NormalEightTerminalOutsideAffine
