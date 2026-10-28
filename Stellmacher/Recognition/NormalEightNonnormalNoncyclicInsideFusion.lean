module
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Stellmacher.Recognition.NormalFourNonnormalCoreInvolutionFusion
public import Theory.GroupTheory.PGroup.CyclicCenterFourOrbit
public import Theory.GroupTheory.PGroup.LargeHallRotationCenter

/-!
# Ambient fusion of involutions in the intrinsic rotation product

The rotation product of an extraspecial eight and a large noncyclic Hall
tail has cyclic center of index four. In the actual odd-core quotient it
is normal. Its normal elementary fours number at most three, and the
quotient has no normal elementary four, so its conjugation action on them
is transitive. Every rotation-product involution therefore fuses into the
image of the chosen four. Conjugacy of involutions lifts through the odd
kernel and then into the original ambient group.

This proves the inside-fusion step of Janko–Thompson, Math. Z. 113 (1970),
§4, Case 1, printed p.392. It needs only the normal elementary bound on the
Sylow subgroup. Weak closure of a fixed central involution is not used.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

private theorem rotation_map (S : Sylow 2 G) :
    (noncyclicRotationPreimage S).map (omegaQuotientHom S) =
      (closure {x : pCore 2 (OmegaQuotient S) | x ^ 4 ≠ 1}).map
        (pCore 2 (OmegaQuotient S)).subtype := by
  let f := omegaQuotientHom S
  let P := pCore 2 (OmegaQuotient S)
  change ((closure {x : omegaCorePreimage S | x ^ 4 ≠ 1}).map
    (omegaCorePreimage S).subtype).map f = _
  rw [map_map, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨f u, u.property⟩, ?_, rfl⟩
    intro he
    apply hu
    apply Subtype.ext
    apply omegaQuotientHom_injective S
    have hh := congrArg (fun a : P => (a : OmegaQuotient S)) he
    change f (u : S) ^ 4 = 1 at hh
    change f ((u : S) ^ 4) = f 1
    simpa only [map_pow, map_one] using hh
  · rintro ⟨u, hu, rfl⟩
    have hm : (u : OmegaQuotient S) ∈ (omegaCorePreimage S).map f := by
      rw [show (omegaCorePreimage S).map f = P from omegaCorePreimage_map S]
      exact u.property
    obtain ⟨v, hv, he⟩ := hm
    refine ⟨⟨v, hv⟩, ?_, he⟩
    intro hh
    apply hu
    apply Subtype.ext
    have hh' := congrArg (fun a : omegaCorePreimage S => f (a : S)) hh
    change f (v ^ 4) = f 1 at hh'
    change (u : OmegaQuotient S) ^ 4 = 1
    simpa only [map_pow, map_one, he] using hh'

/-- Every involution in the intrinsic rotation product is ambient-conjugate
to an element of the normal four. The local quotient supplies the fusion action. -/
public theorem exists_isConj_mem_four_of_mem_noncyclicRotationPreimage
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (u : S) (hu : u ∈ noncyclicRotationPreimage S) (hu2 : orderOf u = 2) :
    ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  let P := pCore 2 (OmegaQuotient S)
  let M := closure {x : P | x ^ 4 ≠ 1}
  let K := M.map P.subtype
  have hmap : (noncyclicRotationPreimage S).map (omegaQuotientHom S) = K := rotation_map S
  let : IsCyclic (center P) := omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨hMc, hMcyc, hMi, hMz⟩ :=
    intrinsic_rotation_center_of_large_hall pCore_isPGroup B D hB hD hn hc hg hlarge
  change 8 ≤ Nat.card (center M) at hMz
  let : M.Characteristic := hMc
  let : K.Normal := inferInstance
  let e : M ≃* K := M.equivMapOfInjective P.subtype P.subtype_injective
  let : IsCyclic (center M) := hMcyc
  let : IsCyclic (center K) := (centerCongr e).isCyclic.mp inferInstance
  have hKi : (center K).index = 4 := by
    have hm := (center M).card_mul_index
    have hk := (center K).card_mul_index
    rw [hMi] at hm
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (centerCongr e).toEquiv] at hk
    have hp : 0 < Nat.card (center M) := Nat.card_pos
    nlinarith
  have hKz : 2 ∣ Nat.card (center K) := by
    rw [← Nat.card_congr (centerCongr e).toEquiv]
    obtain ⟨n, hn⟩ := ((pCore_isPGroup (p := 2) (G := OmegaQuotient S)).to_subgroup M
      |>.to_subgroup (center M)).exists_card_eq
    have hn1 : 1 ≤ n := by
      by_contra hh
      have : n = 0 := by omega
      rw [this, pow_zero] at hn
      change Nat.card (center M) = 1 at hn
      omega
    rw [hn]
    exact dvd_trans (by decide : 2 ∣ 2 ^ 1) (pow_dvd_pow 2 hn1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let zS : S := (z : center S)
  have hzS : orderOf zS = 2 := (orderOf_coe (z : center S)).trans
    ((orderOf_coe z).trans hz)
  have hWK : fourImage S W ≤ K := by
    rw [fourImage_eq_map, ← hmap]
    exact map_mono (four_le_noncyclicRotationPreimage_of_large_noncyclic_tail
      hN S hno hZ W hW hunique hnormal B D hD hn hc hg hlarge zS
      (z : center S).property hzS)
  let F := (fourImage S W).subgroupOf K
  let : IsElementaryAbelian 2 (fourImage S W) := fourImage_elementary S W
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hWK
  let : F.Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hWK).mpr
    have hh := W.le_normalizer_map (omegaQuotientHom S)
    rw [W.normalizer_eq_top, ← MonoidHom.range_eq_map, omegaQuotientHom_range,
      ← fourImage_eq_map] at hh
    exact (map_subtype_le M).trans
      ((pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)).trans hh)
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWK).toEquiv).trans (fourImage_card S W hW)
  let v : K := ⟨omegaQuotientHom S u, by
    rw [← hmap]
    exact mem_map_of_mem _ hu⟩
  have hv : orderOf v = 2 := by
    rw [← orderOf_coe]
    exact (orderOf_injective _ (omegaQuotientHom_injective S) u).trans hu2
  obtain ⟨w, hw⟩ := CyclicCenterFourOrbit.Subgroup.exists_isConj_mem_normal_four
    K hKi hKz (fun U hUn hUe => by
      let : U.Normal := hUn
      let : IsElementaryAbelian 2 U := hUe
      exact omegaQuotient_no_normal_four S W hunique hnormal U) F hF v hv
  have hwm : ((w : K) : OmegaQuotient S) ∈ W.map (omegaQuotientHom S) := by
    rw [← fourImage_eq_map]
    exact w.property
  obtain ⟨wS, hwS, he⟩ := hwm
  have hconj : IsConj (omegaQuotientHom S u) (omegaQuotientHom S wS) := by
    rw [he]
    exact hw
  have hw2 : orderOf wS = 2 := by
    obtain ⟨g, heq⟩ := isConj_iff.mp hconj
    have heq' : MulAut.conj g (omegaQuotientHom S u) = omegaQuotientHom S wS := heq
    rw [← orderOf_injective _ (omegaQuotientHom_injective S) wS,
      ← heq', MulEquiv.orderOf_eq, orderOf_injective _ (omegaQuotientHom_injective S) u, hu2]
  exact ⟨wS, hwS, (omegaNormalizer S).subtype.map_isConj
    ((involution_isConj_omegaNormalizer_iff_quotient S u wS hu2 hw2).mpr hconj)⟩

end Stellmacher.Recognition.NormalEightNonnormalImage
