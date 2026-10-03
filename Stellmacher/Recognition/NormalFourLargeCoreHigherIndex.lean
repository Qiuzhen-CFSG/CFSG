module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Stellmacher.Recognition.NormalFourLargeCoreInsideFusion
public import Theory.GroupTheory.NormalFourCyclicSection
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.NormalFourExtraspecialCentralizer
public import Theory.GroupTheory.PGroup.ThreeInvolutionSmallSquareSubgroup

/-!
# The higher-index large-core reduction

Work throughout with the literal quotient of the central-omega normalizer
by its odd core. An extraspecial core of order thirty-two has the
quaternion-dihedral model, and the quotient by that core acts faithfully on
its elementary Frattini quotient of order sixteen.

The cyclic-four quotient case is excluded by the stronger weak closure
theorem: the central involution has no distinct ambient conjugate anywhere
in the Sylow, contradicting Z-star. It therefore suffices to construct an
action with kernel the actual core whose range has cyclic Sylow two-subgroups
of order at most four. The final transfer and fusion assembly are proved
below. A second route uses the normal four centralizer: fusion makes its
three central involutions automorphism-transitive, whereas intersection with
the extraspecial core gives an order-sixteen subgroup with only two square
values. The intrinsic square-subgroup obstruction proves these data
incompatible, completing the exclusion. This route needs no outer-action
classification or core-index bound and is independent of the index-two branch.
The earlier, more general assembly through outside cyclic sections is retained.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–390,
the quaternion-dihedral case. Under the stronger elementary rank bound,
the argument stops as soon as the outside involution centralizes a four.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The cyclic-four quotient conclusion alone contradicts ambient simplicity;
no transitivity or outside-involution section calculation is required. -/
public theorem large_core_false_of_cyclic_four_quotient [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4)
    (hcyclic : IsCyclic (S ⧸ omegaCorePreimage S)) : False := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 :=
    (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact htz (omegaCorePreimage_large_core_weak_closure hN hrank S hZ E hE hunique
    hH hindex hcyclic z hz (w : center S).property t hzt)

/-- A core-kernel action with cyclic Sylow range of order at most four
excludes the whole higher-index branch. -/
public theorem large_core_false_of_cyclic_sylow_action [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    {A : Type*} [Group A] (f : OmegaQuotient S →* A)
    (hker : f.ker = pCore 2 (OmegaQuotient S))
    (haction : ∀ R : Sylow 2 f.range, IsCyclic R ∧ Nat.card R ≤ 4) : False := by
  obtain ⟨R, ⟨e⟩⟩ := omegaCorePreimage_quotient_equiv_sylow_range S f hker
  obtain ⟨hcyc, hcard⟩ := haction R
  let : IsCyclic R := hcyc
  have hcyclic : IsCyclic (S ⧸ omegaCorePreimage S) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  have hcard' : (omegaCorePreimage S).index = Nat.card R :=
    (index_eq_card _).trans (Nat.card_congr e.toEquiv)
  have hfour : (omegaCorePreimage S).index = 4 := by omega
  exact large_core_false_of_cyclic_four_quotient hns hN hrank S hZ E hE hunique
    hH hfour hcyclic

/-- Once fusion inside the core is excluded, Z-star supplies an outside
involution conjugate to a central involution of the Sylow. -/
public theorem large_core_exists_outside_conjugate_of_core_fusion [IsSimpleGroup G]
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

/-- Assemble the large-core contradiction from the two precise local inputs.
The outside calculation need only handle conjugates of the central involution. -/
public theorem large_core_false_of_involution_geometry [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (houtside : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) →
        ∃ F : Subgroup S, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
          F ≤ omegaCorePreimage S ∧ t ∈ centralizer (F : Set S)) : False := by
  obtain ⟨z, t, hz, hzc, ht, hout, hzt⟩ :=
    large_core_exists_outside_conjugate_of_core_fusion hns S hZ hinside
  obtain ⟨F, hFe, hF, hFH, htc⟩ := houtside z t hz hzc ht hout hzt
  let : IsElementaryAbelian 2 F := hFe
  apply hout
  apply hFH
  exact mem_four_of_square_eq_one_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) F hF
    (by simpa only [ht] using pow_orderOf_eq_one t) htc

/-- The source's cyclic-four normalizer sections supply the entire outside
input: their central kernels and squares act trivially on the normal four. -/
public theorem large_core_false_of_core_fusion_and_cyclic_sections [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (hsections : ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
      ∃ (A : Subgroup S) (Z : Subgroup A) (_ : Z.Normal),
        t ∈ A ∧ IsCyclic (A ⧸ Z) ∧ Nat.card (A ⧸ Z) = 4 ∧
          Z ≤ (center S).comap A.subtype) : False := by
  apply large_core_false_of_involution_geometry hns hrank S hZ hinside
  intro _ t _ _ ht hout _
  obtain ⟨A, Z, hZn, htA, hcyc, hcard, hZc⟩ := hsections t ht hout
  let : Z.Normal := hZn
  let : IsCyclic (A ⧸ Z) := hcyc
  refine ⟨E, inferInstance, hE, four_le_omegaCorePreimage hN hrank S hZ E hE, ?_⟩
  exact involution_centralizes_normal_four_of_cyclic_four_section S.isPGroup' E hE
    A Z hcard (hZc.trans (comap_mono (center_le_centralizer _))) ⟨t, htA⟩
      (by
        apply Subtype.ext
        change t ^ 2 = 1
        simpa only [ht] using pow_orderOf_eq_one t)

/-- The remaining local obstruction can be supplied intrinsically: the normal
four centralizer has three central involutions and contains an order-sixteen
subgroup with only two square values. If those data prevent transitivity on
involutions, the central Sylow involution is weakly closed, contradicting Z-star.
This reduction needs no bound on the Sylow index of the extraspecial core. -/
public theorem large_core_false_of_centralizer_square_obstruction [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hobstruction :
      let C := centralizer (E : Set S)
      IsPGroup 2 C → ¬ IsMulCommutative C →
      (∀ x : C, x ^ 2 = 1 → x ∈ center C) →
      Nat.card {x : C // orderOf x = 2} = 3 →
      (∀ x y : C, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut C, a x = y) →
      ∀ A : Subgroup C, Nat.card A = 16 →
        (∀ x : C, x ^ 2 = 1 → x ∈ A) →
        (∃ z : C, ∀ a : A, (a : C) ^ 2 = 1 ∨ (a : C) ^ 2 = z) → False) : False := by
  have hr := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  obtain ⟨hExtra, hcard⟩ := omegaCorePreimage_large_core_structure S hH
  let : IsExtraspecial 2 (omegaCorePreimage S) := hExtra
  obtain ⟨hnonab, A, hA, hAI, hsq⟩ :=
    normal_four_centralizer_large_extraspecial_data S.isPGroup' hZ hr E hE
      (omegaCorePreimage S) hcard (four_le_omegaCorePreimage hN hrank S hZ E hE)
  obtain ⟨hcentral, hthree⟩ := centralizer_three_involutions_of_rank_two hr E hE
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 :=
    (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzc : z ∈ center S := (w : center S).property
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    hr E hE (by simpa only [hz] using pow_orderOf_eq_one z)
      (center_le_centralizer _ hzc)
  have hweak (t : S) (ht : t ∈ E) (hzt : IsConj (z : G) (t : G)) : t = z := by
    by_contra hne
    have ht1 : t ≠ 1 := by
      intro he
      have hz1 : (z : G) = 1 := isConj_one_left.mp (by simpa [he] using hzt)
      have : z = 1 := Subtype.ext hz1
      simp [this] at hz
    have hfusion := normal_four_fusion_of_central_isConj E hE
      (four_not_le_center_of_card_omega_one_center_eq_two hZ E hE)
      (⟨z, hzE⟩ : E) hzc
      (fun he => (orderOf_eq_prime_iff.mp hz).2 (congrArg Subtype.val he))
      (S : Subgroup G).subtype (⟨t, ht⟩ : E)
      (fun he => ht1 (congrArg Subtype.val he))
      (fun he => hne (congrArg Subtype.val he)) hzt
    have htrans := S.centralizer_involutions_automorphism_transitive_of_four_fusion
      hr hZ E hE hunique z hz hzc hfusion
    exact hobstruction (S.isPGroup'.to_subgroup _) hnonab hcentral hthree htrans A hA hAI hsq
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact htz (S.eq_of_isConj_of_weakly_closed_in_unique_normal_four hrank E hE hunique
    z hzc hz hweak t hzt)

/-- An extraspecial actual core of order thirty-two is impossible: fusion in
the unique normal four forces transitivity on the three involutions of its
centralizer, contradicting the order-sixteen two-square subgroup supplied by
the core. No core-index or outer-action hypothesis is needed. -/
public theorem normal_four_large_core_false [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32) : False := by
  apply large_core_false_of_centralizer_square_obstruction hns hN hrank S hZ E hE
    hunique hH
  dsimp only
  intro hP hnonab hcentral hthree htrans A hA hAI hsq
  exact hP.no_small_square_subgroup_of_transitive_three_involutions
    hnonab hcentral hthree htrans A hA hAI hsq

/-- The higher-index extraspecial large-core branch is impossible in the
normal-four setup. The full branch interface is retained for final assembly. -/
public theorem normal_four_large_core_higher_index_false [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (_hnormal : ¬ (fourImage S E).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (_hindex : 4 ≤ (omegaCorePreimage S).index) : False := by
  exact normal_four_large_core_false hns hN hrank S hZ E hE hunique hH

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
