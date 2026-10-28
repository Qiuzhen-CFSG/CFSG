module

public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoSetup
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoTransport

/-!
# Transport of inside-core involution fusion into the normal four

The preimage of the quotient two-core is stable under conjugacy in the
central-omega normalizer. With central omega of order two, that normalizer
is the central involution centralizer. The extraspecial index-two transport
criterion therefore applies and places a conjugate of every distinct fused
inside-core involution in the unique normal four.

This supplies the transport input for the inside-core nonfusion assembly.
It uses no bound on arbitrary elementary subgroups and covers both
extraspecial groups of order thirty-two. Simplicity, nonsolvability and the
nonnormality of the four's quotient image are not needed for this step.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389, first half
of the paragraph beginning “Suppose |T:H|=2”.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A distinct inside-core conjugate of the central involution fuses to a
noncentral element of the unique normal four. -/
public theorem large_core_index_two_transport
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t ≠ z →
      ∃ u : S, u ∈ W ∧ u ≠ z ∧ IsConj (t : G) (u : G) := by
  intro z t hz hzc htH hconj hne
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hzO : (⟨z, hzc⟩ : center S) ∈ omega₁ (center S) (p := 2) := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (mem_map_of_mem (center S).subtype hzO)
  have hzH : z ∈ H := four_le_omegaCorePreimage hN S hZ W hW hno hzW
  have hline : zpowers (z : G) = centralOmega S := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr ?_) ?_
    · exact mem_map_of_mem (S : Subgroup G).subtype
        (mem_map_of_mem (center S).subtype hzO)
    · rw [Nat.card_zpowers, orderOf_coe, hz, card_centralOmega, hZ]
  have hnorm : omegaNormalizer S = centralizer ({(z : G)} : Set G) := by
    change normalizer (centralOmega S : Set G) = _
    rw [← hline, normalizer_zpowers_eq_centralizer_of_order_two (z : G)
      ((orderOf_coe z).trans hz)]
  apply S.exists_isConj_mem_unique_normal_four_of_extraspecial_index_two
    hno W hunique H ((card_omegaCorePreimage S).trans hH) hindex z hz hzc hzH ?_
    t htH hconj hne
  intro a ha g hg b hgb
  let N := omegaNormalizer S
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  let K := (pCore 2 (OmegaQuotient S)).comap q
  have hgN : g ∈ N := by
    rw [show N = omegaNormalizer S from rfl, hnorm]
    exact mem_centralizer_singleton_iff.mpr hg
  let gN : N := ⟨g, hgN⟩
  let aN : N := inclusion (sylow_le_omegaNormalizer S) a
  let bN : N := inclusion (sylow_le_omegaNormalizer S) b
  have haK : aN ∈ K := by
    change omegaQuotientHom S a ∈ pCore 2 (OmegaQuotient S) at ha
    rw [omegaQuotientHom_apply] at ha
    exact ha
  have hbK := (inferInstance : K.Normal).conj_mem aN haK gN
  have heq : gN * aN * gN⁻¹ = bN := Subtype.ext hgb
  rw [heq] at hbK
  change omegaQuotientHom S b ∈ pCore 2 (OmegaQuotient S)
  rw [omegaQuotientHom_apply]
  exact hbK

end Stellmacher.Recognition.NormalEightNonnormalImage
