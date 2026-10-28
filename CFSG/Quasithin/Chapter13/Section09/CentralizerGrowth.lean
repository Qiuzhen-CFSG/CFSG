module

public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.Transfer
public import Theory.GroupTheory.WreathDiagonalCentralizer

/-!
# Centralizer growth in Lemma 13.9.5: transfer and final assembly

The actual marked `S₄ wr C₂` isomorphism puts the diagonal involution `z`
in `O²(C_M(s))`, while a diagonal three-cycle shows that `C_M(s)` is not
a two-group. If `C_G(z)=T`, the latter fact separates the `s` and `z`
classes. Thompson transfer then fuses `s` to `t`, once the two classes
in `J(T)` are known. Transport of local residuals contradicts the claim
that every involution of `O²(C_G(t))` is in the `t`-class.

The final theorem assembles both desired centralizer conclusions, with
the normalizer and residual fusion analyses explicitly conditional on
`C_G(z)=T`. Those analyses, their recognition step, and the local marked
centralizer equality still require discharge. This module does not yet
assert the unconditional source Lemma 13.9.5. Its transfer descendant also
proves the weakly-closed branch from the earlier marked local classes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth
open Theory.GroupTheory.WreathDiagonal

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The swapping involution has a local centralizer containing a three-cycle,
so cannot fuse to `z` when the latter has centralizer `T`. -/
theorem not_isConj_z_swap (d : Configuration G) (e : d.M ≃* WreathModel)
    (s z : d.M) (q : Multiplicative (ZMod 2))
    (hs : e s = RegularWreathProduct.inl q)
    (hC : centralizer ({(z : G)} : Set G) = (d.T : Subgroup G)) :
    ¬ IsConj (z : G) (s : G) := by
  have hp : IsPGroup 2 (centralizer ({(z : G)} : Set G)) := by
    rw [hC]
    exact d.T.isPGroup'
  exact Theory.GroupTheory.not_isConj_of_non_pGroup_centralized
    (d.M ⊓ centralizer ({(s : G)} : Set G)) hp
    (local_centralizer_not_twoGroup d.M e s q hs) inf_le_right

/-- The source endgame applied to the actual marked wreath isomorphism. The
local residual witness is proved from diagonal three-cycles. Only the two
ambient fusion conclusions of the preceding analysis remain explicit. -/
theorem false_of_marked_wreath_analysis
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (e : d.M ≃* WreathModel) (J : Subgroup G)
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    (s z : d.M) (t : G) (q : Multiplicative (ZMod 2))
    (hs : e s = RegularWreathProduct.inl q)
    (hz : e z = diagonal doubleTransposition)
    (hsorder : orderOf (s : G) = 2)
    (htz : ¬ IsConj t (z : G))
    (hC : centralizer ({(z : G)} : Set G) = (d.T : Subgroup G))
    (hclasses : ∀ x ∈ J, orderOf x = 2 → IsConj t x ∨ IsConj (z : G) x)
    (hresidual : ∀ x ∈ (pResidual 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype, orderOf x = 2 → IsConj t x) : False := by
  have hsT : (s : G) ∈ (d.T : Subgroup G) := by
    rw [← hC, mem_centralizer_singleton_iff]
    have hcomm : s * z = z * s := by
      apply e.injective
      simpa only [map_mul, hs, hz] using (diagonal_commutes doubleTransposition q).symm.eq
    exact congrArg (fun x : d.M => (x : G)) hcomm
  have hzorder : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq z, hz]
    exact (orderOf_injective diagonal diagonal_injective doubleTransposition).trans
      doubleTransposition_order
  exact false_of_centralizer_residual_fusion hG d J hindex hsT hsorder htz
    (not_isConj_z_swap d e s z q hs hC) hclasses
    ⟨z, marked_involution_mem_local_residual d.M e s z q hs hz, hzorder, IsConj.refl _⟩
    hresidual

/-- Conditional assembly of both conclusions of 13.9.5. The marked local
centralizer is `T`; the unresolved normalizer/residual analysis must prove
`hclasses` and `hresidual` under the contrary centralizer equality. This is
not the unconditional source lemma. -/
theorem centralizer_growth_of_fusion_analysis
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (e : d.M ≃* WreathModel) (J : Subgroup G)
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    (s z : d.M) (t : G) (q : Multiplicative (ZMod 2))
    (hs : e s = RegularWreathProduct.inl q)
    (hz : e z = diagonal doubleTransposition)
    (hsorder : orderOf (s : G) = 2)
    (htz : ¬ IsConj t (z : G))
    (hlocal : d.M ⊓ centralizer ({(z : G)} : Set G) = (d.T : Subgroup G))
    (hclasses : centralizer ({(z : G)} : Set G) = (d.T : Subgroup G) →
      ∀ x ∈ J, orderOf x = 2 → IsConj t x ∨ IsConj (z : G) x)
    (hresidual : centralizer ({(z : G)} : Set G) = (d.T : Subgroup G) →
      ∀ x ∈ (pResidual 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype, orderOf x = 2 → IsConj t x) :
    (d.T : Subgroup G) < centralizer ({(z : G)} : Set G) ∧
      ¬ centralizer ({(z : G)} : Set G) ≤ d.M := by
  have hTC : (d.T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    rw [← hlocal]
    exact inf_le_right
  have hne : (d.T : Subgroup G) ≠ centralizer ({(z : G)} : Set G) := by
    intro he
    exact false_of_marked_wreath_analysis hG d e J hindex s z t q hs hz
      hsorder htz he.symm (hclasses he.symm) (hresidual he.symm)
  have hlt := lt_of_le_of_ne hTC hne
  refine ⟨hlt, ?_⟩
  intro hCM
  exact (not_le_of_gt hlt) (hlocal ▸ le_inf hCM le_rfl)

end CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth
