module

public import Stellmacher.Recognition.NormalEightNormalImageTransport
public import Stellmacher.Recognition.NormalEightInvolutionFusion
public import Stellmacher.Recognition.NormalEightFusedWeakClosure
public import Theory.GroupTheory.FusedFourTransport

/-!
# Geometry of the fused moving-four conclusion

Under the no-normal-eight hypotheses and normality of the actual odd-core
quotient image, a distinct returning conjugate of the unique normal four
is disjoint from it and centralizes it. The separated cross-action argument
fuses its involutions, and Hall transfer supplies a distinct returning conjugate.

Choose the central involution from central omega. The quotient-image
transport theorem identifies every returning conjugate containing this
involution. The general fused-four transport theorem then proves both
trivial intersection and commutation.

Source: Janko–Thompson, Math. Z. 113 (1970), §§3 and 6, pp.387–389 and 395;
the separated cross-action argument uses Lemma 2.1. No bound on arbitrary
elementary subgroups is used.
-/

namespace Stellmacher.Recognition.NormalEightNormalFusion
open Subgroup NormalFourCentralOmegaTwo

/-- Once the four is fused, every distinct returning conjugate is disjoint
from it and centralizes it. -/
public theorem disjoint_commuting_of_fused_of_distinct
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hne : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
      W.map (S : Subgroup G).subtype) :
    Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ∧
    (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (mem_map_of_mem (center S).subtype w.property)
  have hzO : (z : G) ∈ centralOmega S := mem_map_of_mem (S : Subgroup G).subtype
    (mem_map_of_mem (center S).subtype w.property)
  have hzgen : zpowers (z : G) = centralOmega S := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzO)
    rw [Nat.card_zpowers, orderOf_coe, hz, card_centralOmega, hZ]
  apply S.disjoint_commuting_conjugate_of_fusion_control W z hzC ?_ ?_ hW g hVS hne
  · intro k hk hkz
    apply NormalEightNormalImage.conjugate_four_eq_of_centralOmega_le S hno hZ W hW hunique k hk
    rw [← hzgen]
    exact zpowers_le.mpr hkz
  · intro x hx hx1
    exact hfused x z hx hzW
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1) hz

/-- Assemble the geometric conclusion from involution fusion and a moving
conjugate. The ambient fusion and weak-closure arguments supply these inputs. -/
public theorem exists_disjoint_commuting_conjugate_of_fused_of_moving
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (hmove : ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        W.map (S : Subgroup G).subtype) :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) ∧
      Disjoint (W.map (S : Subgroup G).subtype)
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  obtain ⟨g, hg, hne⟩ := hmove
  exact ⟨g, hg, disjoint_commuting_of_fused_of_distinct S hno hZ W hW hunique hfused g hg hne⟩

/-- All involutions of the unique normal four are conjugate in the ambient
simple N₂-group under the no-normal-eight hypotheses. -/
public theorem involutions_fused
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal] :
    ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G) :=
  NormalEightInvolutionFusion.involutions_fused hns hN S A hA hnonab hZ hno W hW hunique

/-- The unique normal four has a disjoint commuting ambient conjugate inside
the Sylow subgroup. Fusion and failure of weak closure are discharged here. -/
public theorem exists_disjoint_commuting_conjugate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal] :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) ∧
      Disjoint (W.map (S : Subgroup G).subtype)
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  have hfused := involutions_fused hns hN S A hA hnonab hZ hno W hW hunique
  exact exists_disjoint_commuting_conjugate_of_fused_of_moving S hno hZ W hW hunique
    hfused (NormalEightFusedWeakClosure.exists_distinct_conjugate_four
      hns S A hA hZ hno W hW hfused)

end Stellmacher.Recognition.NormalEightNormalFusion
