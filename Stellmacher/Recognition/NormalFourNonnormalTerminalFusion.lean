module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalCoreInvolutionFusion
public import Stellmacher.Recognition.NormalFourNonnormalOutsideCore
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.NormalFourFusion

/-!
# Terminal fusion for the nonnormal quotient four

The two noncentral elements of the normal four are already Sylow-conjugate.
Z-star supplies a distinct ambient conjugate of the central involution. Thus
it remains to move a conjugate in the quotient-core preimage into the four,
and to rule out a conjugate outside that preimage.

For the latter step our elementary rank bound permits a shorter stopping
point than the affine-eight identification: an outside involution cannot
centralize any elementary four lying inside the core preimage. Otherwise it
would itself belong to that four by the rank bound.

The final theorem discharges these geometric inputs using the inside-core
involution orbit calculation and the outside-core central-square obstruction.
Thus all three nonidentity elements of the four fuse in the ambient group,
without needing the affine-eight alternative.
Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1, final two paragraphs,
printed p.393. In particular the displayed centralizer in the penultimate
paragraph already contains an elementary eight, excluded here by hypothesis.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The unique central involution is an actual element of the chosen four. -/
public theorem exists_central_involution_in_four
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    ∃ z : E, orderOf (z : S) = 2 ∧ (z : S) ∈ center S := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  have hmem : ((w : center S) : S) ∈ E :=
    omega_one_center_le_four_of_elementary_card_lt_eight
      (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
      (mem_map.mpr ⟨w, w.property, rfl⟩)
  exact ⟨⟨w, hmem⟩, (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw),
    (w : center S).property⟩

/-- A distinct conjugate in the four joins the central involution to the
Sylow-conjugate pair and therefore fuses all three nonidentity elements. -/
public theorem four_fusion_of_central_conjugate
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (z u : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (hu : u ≠ 1) (huz : u ≠ z) (hconj : IsConj ((z : S) : G) ((u : S) : G)) :
    ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  exact normal_four_fusion_of_central_isConj E hE
    (four_not_le_center_of_card_omega_one_center_eq_two hZ E hE)
    z hzc hz1 (S : Subgroup G).subtype u hu huz hconj

/-- An involution outside the core preimage cannot centralize an elementary
four inside it. This is the rank obstruction to the source's outside case. -/
public theorem no_four_centralized_by_involution_outside_core
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (F : Subgroup S) [IsElementaryAbelian 2 F] (hF : Nat.card F = 4)
    (hcore : F ≤ omegaCorePreimage S) : t ∉ centralizer (F : Set S) := by
  intro htc
  apply hout
  apply hcore
  exact mem_four_of_square_eq_one_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) F hF
    (by simpa only [ht] using pow_orderOf_eq_one t) htc

/-- Assemble terminal fusion from the two local core-geometry inputs.
The first handles involutions inside the actual core preimage; the second
is the centralizing-four conclusion of the outside-conjugate calculation. -/
public theorem terminal_fusion_of_core_geometry [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hinside : ∀ (z : E), orderOf (z : S) = 2 → (z : S) ∈ center S →
      ∀ t : S, orderOf t = 2 → t ≠ z → t ∈ omegaCorePreimage S →
        ∃ u : E, u ≠ 1 ∧ u ≠ z ∧ IsConj (t : G) ((u : S) : G))
    (houtside : ∀ (z : E), orderOf (z : S) = 2 → (z : S) ∈ center S →
      ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
        IsConj ((z : S) : G) (t : G) →
        ∃ F : Subgroup S, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
          F ≤ omegaCorePreimage S ∧ t ∈ centralizer (F : Set S)) :
    ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  obtain ⟨z, hz, hzc⟩ := exists_central_involution_in_four hrank S hZ E hE
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S (z : S) hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq ((z : S) : G)).trans
      ((orderOf_coe (z : S)).trans hz)
  by_cases htcore : t ∈ omegaCorePreimage S
  · obtain ⟨u, hu, huz, htu⟩ := hinside z hz hzc t ht htz htcore
    exact four_fusion_of_central_conjugate S hZ E hE z u hz hzc hu huz (hzt.trans htu)
  · obtain ⟨F, hFe, hF, hcore, htc⟩ := houtside z hz hzc t ht htcore hzt
    let : IsElementaryAbelian 2 F := hFe
    exact (no_four_centralized_by_involution_outside_core hrank S t ht htcore
      F hF hcore htc).elim

/-- In the nonnormal quotient-image branch, a core of order sixteen and
relative Sylow index two force ambient fusion of the normal four's three
nonidentity elements. The local orbit and outside-core calculations discharge
both geometric inputs to terminal fusion. -/
public theorem terminal_fusion_of_core_order_index [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2) :
    ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  exact terminal_fusion_of_core_geometry hns hrank S hZ E hE
    (noncentral_core_involution_four_ambient_fusion hN hrank S hZ E hE
      hunique hnormal hcore)
    (exists_four_centralized_of_outside_core_isConj hN hrank S hZ E hE
      hunique hnormal hcore hindex)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
