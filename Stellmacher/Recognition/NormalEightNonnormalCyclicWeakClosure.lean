module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalFourNonnormalCyclicWeakClosure
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Large cyclic tails under a normal-only elementary bound

A nontrivial cyclic Hall tail is the center of the quotient two-core.
Its extraspecial-eight presentation bounds the core index by two and puts
all Sylow fourth powers in that cyclic center. A central involution belongs
to the normal four because central omega does, using only the absence of
normal elementary eights. The fourth-root fusion argument therefore proves
weak closure inside the core preimage. Simplicity supplies an outside
conjugate.

The later elementary-centralizer and automizer steps are separate: an
arbitrary elementary eight is permitted by these hypotheses.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393.
The center and fourth-power arguments adapt `NormalFourNonnormalCyclicWeakClosure`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The actual core preimage has cyclic center of the same order as its
nontrivial cyclic Hall factor. -/
public theorem omegaCorePreimage_center_cyclic_tail
    (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) :
    IsCyclic (center (omegaCorePreimage S)) ∧
      Nat.card (center (omegaCorePreimage S)) = Nat.card D := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno E hunique hnormal
  have hcenter := center_eq_cyclic_factor_of_extraspecial_of_cyclic_center
    pCore_isPGroup A D hD hc hgen
  let e := centerCongr (omegaCorePreimageEquiv S)
  refine ⟨e.isCyclic.mpr inferInstance, ?_⟩
  exact (Nat.card_congr e.toEquiv).trans (congrArg (fun U : Subgroup (pCore 2 (OmegaQuotient S)) => Nat.card U) hcenter)

/-- A central Sylow involution lies in the core preimage under the normal-only bound. -/
public theorem central_involution_mem_omegaCorePreimage
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) :
    z ∈ omegaCorePreimage S := by
  have hzO : (⟨z, hzC⟩ : center S) ∈ omega₁ (center S) (p := 2) := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one, hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (mem_map_of_mem (center S).subtype hzO)
  exact four_le_omegaCorePreimage hN S hZ W hW hno hzW

/-- Fourth roots in the cyclic core center give ambient weak closure in the core,
without a bound on nonnormal elementary subgroups. -/
public theorem omegaCorePreimage_weakly_closed_of_large_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  have hD : D ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hlarge
    omega
  obtain ⟨hcyc, hcard⟩ :=
    omegaCorePreimage_center_cyclic_tail S hno W hunique hnormal B D hD hc hgen
  let : IsCyclic (center (omegaCorePreimage S)) := hcyc
  intro z t hzC hz ht hconj
  exact S.eq_of_isConj_of_fourth_powers_in_cyclic_center (omegaCorePreimage S)
    (hcard ▸ hlarge)
    (NormalFourCentralOmegaTwo.omegaCorePreimage_fourth_power_mem_center_of_cyclic_tail
      hN S hZ B D hB hc hgen) z hzC hz
    (central_involution_mem_omegaCorePreimage hN S hZ W hW hno z hzC hz) t ht hconj

/-- A large cyclic tail forces a conjugate of the central involution outside the core. -/
public theorem exists_conjugate_outside_core_of_large_cyclic_tail
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) :
    ∃ t : S, t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) := by
  obtain ⟨t, hne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  refine ⟨t, ?_, hconj⟩
  intro ht
  exact hne (omegaCorePreimage_weakly_closed_of_large_cyclic_tail
    hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge z t hzC hz ht hconj)

/-- The extraspecial-eight/cyclic presentation forces the core preimage to have index two. -/
public theorem omegaCorePreimage_index_two_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hgen : B ⊔ D = ⊤) : (omegaCorePreimage S).index = 2 := by
  let : Group.IsSolvable (OmegaQuotient S) := omegaQuotient_solvable hN S hZ
  have hdim := card_frattini_quotient_le_eight_of_extraspecial_eight_cyclic
    pCore_isPGroup B D hB hgen
  have hle := (omegaQuotientSylow S).relIndex_pCore_le_two_of_frattini_card_le_eight
    (omegaQuotient_centralizer_pCore_le hN S hZ) hdim
  rw [← index_omegaCorePreimage] at hle
  have hpos := (omegaCorePreimage S).index_ne_zero_of_finite
  have hne : (omegaCorePreimage S).index ≠ 1 := by
    intro hi
    rw [index_omegaCorePreimage] at hi
    have heq : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) =
        pCore 2 (OmegaQuotient S) := le_antisymm (relIndex_eq_one.mp hi)
          (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S))
    apply omegaQuotientSylow_not_normal S W hW hunique hnormal
    rw [heq]
    infer_instance
  omega

/-- The original Sylow has eight times the order of a nontrivial cyclic Hall tail. -/
public theorem card_sylow_eq_eight_mul_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8) (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) : Nat.card S = 8 * Nat.card D := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hcprod := card_mul_two_eq_of_extraspecial_of_cyclic_center
    pCore_isPGroup B D hD hc hgen
  rw [hB, ← card_omegaCorePreimage] at hcprod
  have hi := omegaCorePreimage_index_two_of_cyclic_tail hN S hZ W hW hunique hnormal B D hB hgen
  have hcard := (omegaCorePreimage S).card_mul_index
  rw [hi] at hcard
  omega

end Stellmacher.Recognition.NormalEightNonnormalImage

