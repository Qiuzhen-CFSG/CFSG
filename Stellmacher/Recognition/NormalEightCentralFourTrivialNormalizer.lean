module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Theory.GroupTheory.WeakClosureFusion
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Stellmacher.Recognition.NormalEightCentralFourLocalControl
public import Theory.GroupTheory.PGroup.NormalEightElementaryBound
public import Theory.GroupTheory.PGroup.CentralFourNormalizerTower
public import Theory.GroupTheory.FourGroupCrossActionFusion

/-!
# Excluding the trivial Sylow-normalizer action in the central-four case

Let the central first omega subgroup of a Sylow two-subgroup have order four,
and suppose there is no normal elementary eight. The normal four is then
central. If it were weakly closed, its normalizer would control fusion in the
Sylow subgroup. Z-star and Burnside separation therefore give a distinct
returning conjugate of this four when the Sylow normalizer is the product of
the Sylow subgroup and its centralizer.

The N₂ hypothesis supplies local centralizer control for each conjugate four.
The MacWilliams–Sah elementary order bound and the normalizer-tower theorem
then construct the symmetric four-group cross-action configuration. Its fusion
theorem makes all nonidentity elements of the original four conjugate,
contradicting Burnside separation.

This assembles Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.394,
using 1.1 and Lemma 2.1, pp.385–387, and Z-star in place of Wielandt transfer.
Source:
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightCentralFour

open Subgroup

/-- The normal four has a distinct ambient conjugate contained in the Sylow
subgroup. No elementary rank bound or local-solvability assumption is used. -/
public theorem exists_distinct_conjugate_four_of_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        W.map (S : Subgroup G).subtype := by
  classical
  have hWC : W ≤ center S :=
    (normal_elementary_le_omega_center_of_no_normal_eight hno hZ W).trans
      (map_subtype_le _)
  let A := W.map (S : Subgroup G).subtype
  have hAS : A ≤ (S : Subgroup G) := map_subtype_le W
  have hSC : (S : Subgroup G) ≤ centralizer (A : Set G) := by
    intro s hs
    rintro _ ⟨w, hw, rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp (hWC hw) (⟨s, hs⟩ : S))).symm
  by_contra hnone
  have hweak (g : G) (hg : A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G)) :
      g ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hne
    exact hnone ⟨g, hg, hne⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (by rw [hW]; decide)
  let z : S := w
  have hz : orderOf z = 2 := (orderOf_coe w).trans hw
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  obtain ⟨n, hn, hnt⟩ := S.weakly_closed_normalizer_controls_fusion A hAS hSC hweak
    z.property t.property hzt
  have hzA : (z : G) ∈ A := mem_map_of_mem _ w.property
  have htA : (t : G) ∈ A := by
    rw [← hnt]
    exact (mem_normalizer_iff.mp hn (z : G)).mp hzA
  have htW : t ∈ W := by
    obtain ⟨u, hu, he⟩ := htA
    exact (Subtype.ext he : u = t) ▸ hu
  exact htz (S.eq_of_isConj_of_mem_center_of_normalizer_eq hnorm z t
    (hWC w.property) (hWC htW) hzt).symm

/-- The trivial Sylow-normalizer action is impossible in the central-four case. -/
public theorem false_of_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN2 : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    False := by
  have hWc : W ≤ center S :=
    (normal_elementary_le_omega_center_of_no_normal_eight hno hZ W).trans
      (map_subtype_le _)
  have hrank := S.isPGroup'.elementary_card_le_sixteen_of_no_normal_eight_of_center_four
    hno hZ
  have hcontrol (k : G) : TwoSubgroupCentralizerControl
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom) :=
    NormalEightCentralFourLocalControl.centralizes_conjugate_four hN2 S hZ hno W hW k
  obtain ⟨g, hBS, hne⟩ :=
    exists_distinct_conjugate_four_of_normalizer_eq hns S hZ hno W hW hnorm
  obtain ⟨hdisj, V, V₁, hVe, hV, hV₁e, hV₁, hn, hVC, hV₁C, hfree, hfree₁⟩ :=
    S.exists_central_four_normalizer_configuration hno W hW hWc hrank hcontrol g hBS hne
  let A := W.map (S : Subgroup G).subtype
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := hVe
  let : IsElementaryAbelian 2 V₁ := hV₁e
  have hA : Nat.card A = 4 :=
    (card_map_of_injective (S : Subgroup G).subtype_injective).trans hW
  have hB : Nat.card B = 4 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hA
  have hAB : A ≤ centralizer (B : Set G) := by
    rintro a ⟨w, hw, rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp (hWc hw) (⟨b, hBS hb⟩ : S))
  have hunique (x y : W) (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
    have hc : IsConj ((x : S) : G) ((y : S) : G) :=
      isConj_of_four_group_cross_action V V₁ A B hV hV₁ hA hB hn hVC hV₁C
        hAB hdisj hfree hfree₁ x y
        (mem_map_of_mem _ x.property) (mem_map_of_mem _ y.property)
        (fun h => hx (Subtype.ext (Subtype.ext h)))
        (fun h => hy (Subtype.ext (Subtype.ext h)))
    exact Subtype.ext (S.eq_of_isConj_of_mem_center_of_normalizer_eq hnorm x y
      (hWc x.property) (hWc y.property) hc)
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW]; decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : W)
  have htwo : Nat.card W = 2 := (Nat.card_eq_two_iff' (1 : W)).mpr
    ⟨x, hx, fun y hy => hunique y x hy hx⟩
  omega

end Stellmacher.Recognition.NormalEightCentralFour
