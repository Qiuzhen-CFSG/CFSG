module

public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexRankTwo
public import Theory.GroupTheory.PGroup.CyclicFourSectionSquareRoot

/-!
# Bare sections over the actual rank-two extraspecial core

The actual quotient core is isomorphic to its preimage in the Sylow group,
and its self-centrality makes the preimage self-centralizing. Consequently,
the intrinsic square-action calculation on that preimage supplies a
cyclic-four section with central kernel and identifies the fixed core with
the unique normal four. No rank bound on the ambient Sylow group is used.

The square-action calculation is explicit in this adapter: the fixed points
must form an elementary four, and an inner correction of the quotient
lift's action must square to the prescribed involution action. The generic
transfer and section construction are proved in the imported Theory module.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A verified intrinsic square-action calculation suffices for the bare section.
The quotient is explicitly cyclic of order four; its classification is separate. -/
public theorem large_core_rank_two_bare_section_of_square_action
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hindex : (omegaCorePreimage S).index = 4)
    [IsCyclic (S ⧸ omegaCorePreimage S)]
    (hcalc : ∀ (a b : MulAut (omegaCorePreimage S))
      (p : omegaCorePreimage S) (n : ℕ),
      b ^ (2 ^ n) = 1 → a = MulAut.conj p * b ^ 2 → a ^ 2 = 1 →
      (¬ ∃ x : omegaCorePreimage S, a = MulAut.conj x) →
      IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id (omegaCorePreimage S))) ∧
      Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id (omegaCorePreimage S))) = 4 ∧
      ∃ x : omegaCorePreimage S, (MulAut.conj x * b) ^ 2 = a)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S) :
    ∃ (K : Subgroup S) (Z : Subgroup K) (_ : Z.Normal),
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center S).comap K.subtype ∧ t ∈ K ∧
      omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hself : centralizer (H : Set S) ≤ H := by
    intro s hs
    apply omegaQuotient_centralizer_pCore_le hN S hZ
    intro x hx
    rw [← omegaCorePreimage_map S] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa only [map_mul] using congrArg (omegaQuotientHom S) (hs k hk)
  obtain ⟨K, Z, hZn, hcyclic, hquot, hZc, htK, hfixed⟩ :=
    bare_section_of_extraspecial_square_action S.isPGroup' H W hself
      hindex hunique hcalc t ht hout
  exact ⟨K, Z, hZn, hcyclic, hquot, hZc, htK, hfixed.le⟩

end Stellmacher.Recognition.NormalEightNonnormalImage
