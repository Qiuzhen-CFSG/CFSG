module

public import Theory.GroupTheory.PGroup.NormalEightCriticalExtension
public import Theory.GroupTheory.WeakClosureFusion
public import Theory.GroupTheory.CentralInvolutionSquareFusion
public import Theory.GroupTheory.QuaternionCentralFactorRoots
public import Theory.GroupTheory.PGroup.NormalEightQuaternionFactorSquares
public import Stellmacher.Recognition.NormalEightCriticalQuaternionFactor
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Weak closure and the center of a nonabelian critical subgroup

A weakly closed central four in a Sylow two-subgroup of a nonsolvable simple
finite group has its three involutions fused. Its normalizer controls fusion
in the Sylow subgroup, so Z-star supplies a second conjugate within the four
for each involution. Two distinct conjugacy classes would require at least
four nonidentity elements in that four.

For a Sylow subgroup with central omega of order four and no normal elementary
eight, this proves that weak closure of the central four forces the center of
each nonabelian critical subgroup to be elementary. Conversely an elementary
critical center forces all Sylow involutions to be central, and hence makes
the central four weakly closed. Weak closure remains an explicit ambient
hypothesis here; the nontrivial Sylow automizer alone is not identified with
nontrivial action on the four.

There is also a second reduction, following MacWilliams §3(iv): a central
involution fixed by the Sylow normalizer cannot have a commuting square root
in every involution centralizer if all involution squares are Sylow-central.
This separates the intrinsic square calculation from the ambient Z-star
contradiction. The structural witnesses remain explicit hypotheses.

Sources: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 2.1(ii); the Z-star theorem; the setting of MacWilliams's theorem quoted
in Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCenter

/-- Z-star excludes a normalizer-fixed involution with commuting roots
when all involution squares are central. -/
public theorem false_of_fixed_involution_square_data
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hN : normalizer (S : Set G) ≤ centralizer ({(z : G)} : Set G))
    (hsquares : ∀ v : S, v ^ 4 = 1 → v ^ 2 ∈ center S)
    (hroots : ∀ t : S, orderOf t = 2 → ∃ x : S, x ^ 2 = z ∧ Commute x t) :
    False := by
  obtain ⟨t, htne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq (z : G)).trans
      ((orderOf_coe z).trans hz)
  obtain ⟨x, hx, hxt⟩ := hroots t ht
  exact htne (S.eq_of_isConj_of_central_involution_squares z
    (by simpa only [hz] using pow_orderOf_eq_one z) hzc hN hsquares t x hx hxt hconj)

/-- A quaternion central factor supplies the commuting roots in the square
obstruction. Its involution must still be fixed by the Sylow normalizer. -/
public theorem false_of_quaternion_central_factor_of_fixed_involution
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (Q : Subgroup S) (e : Q ≃* QuaternionGroup 2)
    (hgen : Q ⊔ centralizer (Q : Set S) = ⊤)
    (z : Q) (hz : orderOf z = 2)
    (hN : normalizer (S : Set G) ≤ centralizer ({((z : S) : G)} : Set G))
    (hsquares : ∀ v : S, v ^ 4 = 1 → v ^ 2 ∈ center S) : False := by
  obtain ⟨hzc, hroots⟩ := Q.quaternion_central_factor_involution_roots e hgen z hz
  apply false_of_fixed_involution_square_data hns S z ((orderOf_coe z).trans hz)
    hzc hN hsquares
  intro t _
  obtain ⟨x, hx, hxt⟩ := hroots t
  exact ⟨x, hx, hxt⟩

/-- A nonabelian critical subgroup has elementary center under the ambient
normalizer hypothesis.  A nonelementary center yields a quaternion central
factor with a normalizer-fixed involution; the intrinsic square bound for that
factor then contradicts the Z-star theorem. -/
public theorem elementary_center_of_nonabelian_critical
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 4)
    (hnorm : Subgroup.normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G))
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hCnonab : ¬ IsMulCommutative C) :
    IsElementaryAbelian 2 (Subgroup.center C) := by
  by_contra hbad
  obtain ⟨Q, ⟨e⟩, hgen, z, hz, hN⟩ :=
    S.quaternion_factor_of_nonelementary_critical_center hno hZ hnorm hC hCnonab hbad
  have hsquares := Subgroup.quaternion_factor_squares_central
    S.isPGroup' hno hZ Q e hgen
  exact false_of_quaternion_central_factor_of_fixed_involution
    hns S Q e hgen z hz hN hsquares

/-- Weak closure of a central four forces fusion of its three involutions. -/
public theorem four_involutions_fused_of_weakly_closed
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (W : Subgroup S) (hW : Nat.card W = 4) (hWc : W ≤ center S)
    (hweak : ∀ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      g ∈ normalizer (W.map (S : Subgroup G).subtype : Set G))
    (z t : S) (hzW : z ∈ W) (htW : t ∈ W)
    (hz : orderOf z = 2) (ht : orderOf t = 2) :
    IsConj (z : G) (t : G) := by
  classical
  let A := W.map (S : Subgroup G).subtype
  have hSC : (S : Subgroup G) ≤ centralizer (A : Set G) := by
    intro s hs
    rintro _ ⟨w, hw, rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp (hWc hw) (⟨s, hs⟩ : S))).symm
  have hmem (a b : S) (ha : a ∈ W) (hc : IsConj (a : G) (b : G)) : b ∈ W := by
    obtain ⟨n, hn, he⟩ := S.weakly_closed_normalizer_controls_fusion A
      (map_subtype_le W) hSC hweak a.property b.property hc
    have hb : (b : G) ∈ A := by
      rw [← he]
      exact (mem_normalizer_iff.mp hn (a : G)).mp (mem_map_of_mem _ ha)
    obtain ⟨v, hv, heq⟩ := hb
    exact (Subtype.ext heq : v = b) ▸ hv
  have hne (a b : S) (ha : orderOf a = 2) (hc : IsConj (a : G) (b : G)) : b ≠ 1 := by
    intro hb
    have ha1 : a = 1 := Subtype.ext (isConj_one_left.mp (by simpa [hb] using hc))
    simp [ha1] at ha
  by_contra hn
  obtain ⟨u, huz, hzu⟩ := exists_distinct_isConj_in_sylow hns S z hz
  obtain ⟨v, hvt, htv⟩ := exists_distinct_isConj_in_sylow hns S t ht
  have hz1 := hne z z hz (IsConj.refl _)
  have ht1 := hne t t ht (IsConj.refl _)
  have hu1 := hne z u hz hzu
  have hv1 := hne t v ht htv
  have hzt : z ≠ t := fun he => hn (he ▸ IsConj.refl (z : G))
  have hzv : z ≠ v := fun he => hn ((he ▸ htv).symm)
  have htu : t ≠ u := fun he => hn (he ▸ hzu)
  have huv : u ≠ v := fun he => hn (hzu.trans (he ▸ htv.symm))
  let : Fintype W := Fintype.ofFinite W
  let a : W := ⟨z, hzW⟩
  let b : W := ⟨t, htW⟩
  let c : W := ⟨u, hmem z u hzW hzu⟩
  let d : W := ⟨v, hmem t v htW htv⟩
  have hcard := Finset.card_le_univ ({1, a, b, c, d} : Finset W)
  have hnat : Fintype.card W = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hfive : ({1, a, b, c, d} : Finset W).card = 5 := by
    simp [a, b, c, d, Subtype.ext_iff, hzt, Ne.symm huz, hzv, htu,
      Ne.symm hvt, huv, Ne.symm hz1, Ne.symm ht1, Ne.symm hu1, Ne.symm hv1]
  omega

/-- Weak closure of the central omega four suffices for an elementary
center of a nonabelian critical subgroup. -/
public theorem elementary_center_of_weakly_closed
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hCnonab : ¬ IsMulCommutative C)
    (hweak : ∀ g : G,
      (((omega₁ (center S) (p := 2)).map (center S).subtype).map
        (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
          (S : Subgroup G) →
      g ∈ normalizer (((omega₁ (center S) (p := 2)).map (center S).subtype).map
        (S : Subgroup G).subtype : Set G)) :
    IsElementaryAbelian 2 (center C) := by
  let W := (omega₁ (center S) (p := 2)).map (center S).subtype
  have hW : Nat.card W = 4 := by
    rwa [card_map_of_injective (center S).subtype_injective]
  have hmem (x : S) (hx : x ∈ center S) (hx2 : orderOf x = 2) : x ∈ W := by
    refine ⟨⟨x, hx⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    simpa [hx2] using pow_orderOf_eq_one x
  have hfuse : ∀ x y : S, x ∈ center S → y ∈ center S →
      orderOf x = 2 → orderOf y = 2 → IsConj (x : G) (y : G) := by
    intro x y hx hy hx2 hy2
    exact four_involutions_fused_of_weakly_closed hns S W hW (map_subtype_le _)
      hweak x y (hmem x hx hx2) (hmem y hy hy2) hx2 hy2
  have htrans := S.critical_involutions_transitive_of_central_fusion hno hZ hC hfuse
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  have hclass : commutator C ≤ center C :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcentral := hC.square_one_mem_center hno hZ
  have hexp := (S.isPGroup'.to_subgroup C).exponent_four_of_class_two_of_transitive_three_involutions
    hCnonab hcentral (hC.card_involutions_eq_three hno hZ) htrans hclass
  exact ((S.isPGroup'.to_subgroup C).special_of_exponent_four_of_transitive_involutions
    hCnonab hcentral htrans hexp).2.2.1

/-- Conversely, an elementary critical center makes the central omega four
weakly closed. This direction does not require simplicity or nonabelianness. -/
public theorem weakly_closed_of_elementary_center
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    [IsElementaryAbelian 2 (center C)] :
    ∀ g : G,
      (((omega₁ (center S) (p := 2)).map (center S).subtype).map
        (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
          (S : Subgroup G) →
      g ∈ normalizer (((omega₁ (center S) (p := 2)).map (center S).subtype).map
        (S : Subgroup G).subtype : Set G) := by
  intro g hB
  let O := omega₁ (center S) (p := 2)
  let W := O.map (center S).subtype
  let A := W.map (S : Subgroup G).subtype
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (B.subgroupOf (S : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf hB
  have hc := hC.involutions_central_of_elementary_center hno hZ
  have hBW := elementary_le_omega_center_of_involutions_central
    (B.subgroupOf (S : Subgroup G))
    (fun x hx => hc x (by simpa only [hx] using pow_orderOf_eq_one x))
  have hBA : B ≤ A := by
    intro b hb
    exact ⟨⟨b, hB hb⟩, hBW (show (⟨b, hB hb⟩ : S) ∈
      B.subgroupOf (S : Subgroup G) from hb), rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hBA
    (card_map_of_injective (MulAut.conj g).injective).ge

end Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCenter
