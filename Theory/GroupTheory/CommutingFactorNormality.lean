module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal factors from a commuting factorization

Suppose a normal subgroup `Q` of an arbitrary group `G` factors as `D U`,
`Q F = G`, and `D` centralizes both `U` and `F`. Then `D`, `U Z(G)`,
and `F U Z(G)` are normal in `G`. No finiteness is needed.

Set `H = F ⊔ U`. Since `D` and `H` commute and generate `G`, each is
normal and `D ∩ H` is central. Decomposing an element of `Q ∩ H` as `du`
shows that its `D` component also belongs to `H`. Consequently
`(Q ∩ H) Z(G) = U Z(G)`, establishing the remaining normality assertions.

This supplies the elementary normality argument in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), proof of (3.3), assertion (4), p.15.
-/

namespace Subgroup

private theorem normal_of_commuting_cover {G : Type*} [Group G]
    (A B : Subgroup G) (hAB : A ⊔ B = ⊤) (hc : B ≤ centralizer A) : A.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hAB]
  exact sup_le A.le_normalizer (hc.trans (centralizer_le_normalizer (A : Set G)))

/-- In a normal factorization, a factor centralized by both the other factor
and a supplement is normal; adjoining the center normalizes the other factors. -/
public theorem normal_sup_center_of_commuting_factorization
    {G : Type*} [Group G] (Q D U F : Subgroup G) [Q.Normal]
    (hQ : Q = D ⊔ U) (hG : Q ⊔ F = ⊤)
    (hDU : ⁅D, U⁆ = ⊥) (hDF : ⁅D, F⁆ = ⊥) :
    D.Normal ∧ (U ⊔ center G).Normal ∧ (F ⊔ U ⊔ center G).Normal := by
  let H := F ⊔ U
  have hHD : H ≤ centralizer D := sup_le
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDF))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDU))
  have hDH : D ≤ centralizer H := le_centralizer_iff.mp hHD
  have hcover : D ⊔ H = ⊤ := by
    simpa only [hQ, H, sup_assoc, sup_comm U F] using hG
  have hDn : D.Normal := normal_of_commuting_cover D H hcover hHD
  have hHn : H.Normal := normal_of_commuting_cover H D (sup_comm D H ▸ hcover) hDH
  let := hDn
  let := hHn
  have hcentral : D ⊓ H ≤ center G := by
    have hc : D ⊔ H ≤ centralizer (D ⊓ H) := sup_le
      (hDH.trans (centralizer_le (show (D ⊓ H : Subgroup G) ≤ H from inf_le_right)))
      (hHD.trans (centralizer_le (show (D ⊓ H : Subgroup G) ≤ D from inf_le_left)))
    have hh : D ⊓ H ≤ centralizer (⊤ : Subgroup G) :=
      le_centralizer_iff.mp (hcover ▸ hc)
    simpa only [coe_top, centralizer_univ] using hh
  have hintersection : Q ⊓ H ≤ U ⊔ center G := by
    intro x hx
    obtain ⟨d, hd, u, hu, hdu⟩ := mem_sup_of_normal_left.mp (hQ ▸ hx.1)
    have huH : u ∈ H := (show U ≤ H from le_sup_right) hu
    have hdH : d ∈ H := by
      have hm := H.mul_mem hx.2 (H.inv_mem huH)
      rw [← hdu] at hm
      simpa only [mul_inv_cancel_right] using hm
    rw [← hdu]
    exact (U ⊔ center G).mul_mem
      ((show center G ≤ U ⊔ center G from le_sup_right) (hcentral ⟨hd, hdH⟩))
      ((show U ≤ U ⊔ center G from le_sup_left) hu)
  have hEq : (Q ⊓ H) ⊔ center G = U ⊔ center G := by
    apply le_antisymm (sup_le hintersection le_sup_right)
    apply sup_le _ le_sup_right
    apply le_trans (le_inf _ (show U ≤ H from le_sup_right)) le_sup_left
    rw [hQ]
    exact le_sup_right
  have hUn : (U ⊔ center G).Normal := hEq ▸ inferInstance
  exact ⟨hDn, hUn, inferInstanceAs (H ⊔ center G).Normal⟩

end Subgroup
