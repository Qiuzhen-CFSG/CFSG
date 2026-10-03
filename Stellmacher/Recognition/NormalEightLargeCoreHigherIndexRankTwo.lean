module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.CyclicFourSectionFixedPoints

/-!
# The higher-index quaternion–dihedral core under normal-only bounds

The rank bound here concerns only the actual quotient core and its isomorphic
preimage in the Sylow subgroup. It gives the quaternion–dihedral factors,
without imposing an elementary rank bound on the ambient Sylow or group.

The terminal exclusion is proved from the source's cyclic-four normalizer
section: its involution cannot have fixed core subgroup contained in the
normal four, by the normal-subgroup-chain lemma. Fusion inside the core and
the construction of that section remain separate ambient inputs. Z-star
supplies an outside conjugate once inside-core fusion has been excluded.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–390.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Core-local elementary rank transfers to the genuine core preimage. -/
public theorem omegaCorePreimage_elementary_card_lt_eight
    (S : Sylow 2 G)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (E : Subgroup (omegaCorePreimage S)) [IsElementaryAbelian 2 E] :
    Nat.card E < 8 := by
  let e := omegaCorePreimageEquiv S
  have hb := hcoreRank (E.map e.toMonoidHom) (IsElementaryAbelian.map _)
  rwa [card_map_of_injective e.injective] at hb

/-- The actual core preimage has quaternion–dihedral factors from core rank alone. -/
public theorem omegaCorePreimage_dihedral_quaternion_of_core_rank
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8) :
    ∃ U V : Subgroup (omegaCorePreimage S),
      Nonempty (U ≃* QuaternionGroup 2) ∧ Nonempty (V ≃* DihedralGroup 4) ∧
      V ≤ centralizer (U : Set (omegaCorePreimage S)) ∧
      U ⊔ V = ⊤ ∧ Nat.card (U ⊓ V : Subgroup (omegaCorePreimage S)) = 2 := by
  let : IsExtraspecial 2 (omegaCorePreimage S) :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  exact IsExtraspecial.dihedral_quaternion_factors_of_card_thirty_two
    (fun E hE => @omegaCorePreimage_elementary_card_lt_eight G _ _ S hcoreRank E hE)
    ((card_omegaCorePreimage S).trans hH)

/-- Inside-core weak closure leaves an outside fused involution, without any
rank assumption on elementary subgroups of the ambient group. -/
public theorem large_core_rank_two_outside_conjugate_of_core_fusion [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z) :
    ∃ z t : S, orderOf z = 2 ∧ z ∈ center S ∧ orderOf t = 2 ∧
      t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 :=
    (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzc : z ∈ center S := (w : center S).property
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq (z : G)).trans ((orderOf_coe z).trans hz)
  exact ⟨z, t, hz, hzc, ht, fun hin => htz (hinside z t hz hzc ht hin hzt), hzt⟩

/-- The cyclic-four normalizer section completes the large-core exclusion.
Only normal elementary subgroups are bounded; no arbitrary elementary eight
is treated as a contradiction. -/
public theorem large_core_rank_two_false_of_centralizing_section
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (K : Subgroup S) (Z : Subgroup K) [Z.Normal] [IsCyclic (K ⧸ Z)]
    (hquot : Nat.card (K ⧸ Z) = 4)
    (hZK : Z ≤ (center S).comap K.subtype)
    (hKW : K ≤ centralizer (W : Set S))
    (t : K) (ht : t ^ 2 = 1)
    (hfixed : omegaCorePreimage S ⊓ centralizer ({(t : S)} : Set S) ≤ W) : False := by
  have hWH : W < omegaCorePreimage S := by
    apply lt_of_le_of_ne (four_le_omegaCorePreimage hN S hZ W hW hno)
    intro heq
    have hc := card_omegaCorePreimage S
    rw [← heq, hW, hH] at hc
    contradiction
  exact fixed_not_le_of_centralizing_cyclic_four_section S.isPGroup' W
    (omegaCorePreimage S) hWH K Z hquot hZK hKW t ht hfixed

end Stellmacher.Recognition.NormalEightNonnormalImage
