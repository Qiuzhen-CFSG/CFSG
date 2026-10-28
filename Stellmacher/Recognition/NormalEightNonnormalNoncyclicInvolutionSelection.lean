module

public import Stellmacher.Recognition.NormalEightOmegaNormalizerCentralizer

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransferSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Theory.GroupTheory.SylowFusionInvariantSelection
public import Theory.GroupTheory.PGroup.LargeHallOutsideInvolution

/-!
# Local Sylow-centralizer selection outside the rotation product

The fourth-power closure in the quotient two-core is characteristic, so its
image is normal in the odd-core quotient of the omega normalizer. Consequently
conjugacy in that normalizer preserves the complement of the rotation product
in the actual core preimage, whenever both elements lie in the original Sylow
subgroup. This does not assert that the core preimage is ambient normal.

Apply Sylow conjugacy inside the omega normalizer to an outside-rotation core
involution. When the central omega has order two, that normalizer is exactly
the centralizer of the central involution. The resulting Sylow centralizer
has odd relative index in the common centralizer.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed pp.392–393,
the paragraph beginning “Since H₁H̃₂ char H”.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic rotation product is the inverse image of the normal
rotation product in the actual odd-core quotient. -/
public theorem noncyclicRotationPreimage_eq_comap_quotient_rotation (S : Sylow 2 G) :
    noncyclicRotationPreimage S =
      ((closure {x : pCore 2 (OmegaQuotient S) | x ^ 4 ≠ 1}).map
        (pCore 2 (OmegaQuotient S)).subtype).comap (omegaQuotientHom S) := by
  have hmap : (noncyclicRotationPreimage S).map (omegaQuotientHom S) =
      (closure {x : pCore 2 (OmegaQuotient S) | x ^ 4 ≠ 1}).map
        (pCore 2 (OmegaQuotient S)).subtype := by
    rw [noncyclicRotationPreimage, map_map, MonoidHom.map_closure, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨omegaQuotientHom S x, x.property⟩, ?_, rfl⟩
      intro he
      apply hx
      apply Subtype.ext
      apply omegaQuotientHom_injective S
      have hh := congrArg Subtype.val he
      simpa only [coe_pow, coe_one, map_pow, map_one] using hh
    · rintro ⟨y, hy, rfl⟩
      have hym : (y : OmegaQuotient S) ∈
          (omegaCorePreimage S).map (omegaQuotientHom S) := by
        rw [omegaCorePreimage_map]
        exact y.property
      obtain ⟨x, hx, he⟩ := hym
      refine ⟨⟨x, hx⟩, ?_, he⟩
      intro hs
      apply hy
      apply Subtype.ext
      have hh := congrArg (omegaQuotientHom S) (congrArg Subtype.val hs)
      simpa only [coe_pow, coe_one, map_pow, map_one, he] using hh
  rw [← hmap, comap_map_eq_self_of_injective (omegaQuotientHom_injective S)]

private theorem normal_mem_iff_of_isConj
    {P : Type*} [Group P] (K : Subgroup P) [K.Normal]
    {x y : P} (h : IsConj x y) : x ∈ K ↔ y ∈ K := by
  have transport {a b : P} (hab : IsConj a b) (ha : a ∈ K) : b ∈ K := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hab
    exact hg ▸ (inferInstance : K.Normal).conj_mem a ha g
  exact ⟨transport h, transport h.symm⟩

/-- Local conjugacy preserves the outside-rotation part of the core. The
normal subgroups used in this proof live in the odd-core quotient. -/
public theorem outside_noncyclicRotationPreimage_of_omegaNormalizer_isConj
    (S : Sylow 2 G) (x y : S)
    (hxH : x ∈ omegaCorePreimage S) (hxR : x ∉ noncyclicRotationPreimage S)
    (hxy : IsConj
      (⟨(x : G), sylow_le_omegaNormalizer S x.property⟩ : omegaNormalizer S)
      ⟨(y : G), sylow_le_omegaNormalizer S y.property⟩) :
    y ∈ omegaCorePreimage S ∧ y ∉ noncyclicRotationPreimage S := by
  let H := pCore 2 (OmegaQuotient S)
  let K := closure {u : H | u ^ 4 ≠ 1}
  let : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f
    apply (closure_le _).mpr
    intro u hu
    apply Subgroup.subset_closure
    change (f u) ^ 4 ≠ 1
    intro he
    apply hu
    apply f.injective
    simpa only [map_pow, map_one] using he
  let : (K.map H.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hq : IsConj (omegaQuotientHom S x) (omegaQuotientHom S y) := by
    simpa only [omegaQuotientHom_apply] using
      (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))).map_isConj hxy
  refine ⟨(normal_mem_iff_of_isConj H hq).mp hxH, ?_⟩
  rw [noncyclicRotationPreimage_eq_comap_quotient_rotation] at hxR ⊢
  exact fun hy => hxR ((normal_mem_iff_of_isConj (K.map H.subtype) hq).mpr hy)

/-- Starting from one outside-rotation core involution, select one whose
Sylow centralizer is Sylow in the common ambient centralizer. -/
public theorem exists_outside_rotation_involution_with_local_sylow_centralizer_of_seed
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (x : S) (hxH : x ∈ omegaCorePreimage S)
    (hxR : x ∉ noncyclicRotationPreimage S) (hx : orderOf x = 2) :
    ∃ y : S, y ∈ omegaCorePreimage S ∧ y ∉ noncyclicRotationPreimage S ∧
      orderOf y = 2 ∧
      ¬ 2 ∣ ((centralizer ({y} : Set S)).map (S : Subgroup G).subtype).relIndex
        (centralizer ({(z : G)} : Set G) ⊓ centralizer ({(y : G)} : Set G)) := by
  obtain ⟨y, hy, horder, hlocal⟩ :=
    S.exists_fusion_invariant_with_local_centralizer (omegaNormalizer S)
      (sylow_le_omegaNormalizer S)
      (fun u => u ∈ omegaCorePreimage S ∧ u ∉ noncyclicRotationPreimage S)
      (fun u v hu huv => outside_noncyclicRotationPreimage_of_omegaNormalizer_isConj
        S u v hu.1 hu.2 huv) x ⟨hxH, hxR⟩
  rw [omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzc] at hlocal
  exact ⟨y, hy.1, hy.2, horder.trans hx, hlocal⟩

/-- The quotient-core witness is transported through the actual core
equivalence before local Sylow selection. Only its intrinsic fourth-power
closure is used, so no compatibility choice for the equivalence is needed. -/
public theorem exists_outside_rotation_involution_with_local_sylow_centralizer_of_quotient_seed
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (hseed : ∃ u : pCore 2 (OmegaQuotient S),
      u ∉ closure {v : pCore 2 (OmegaQuotient S) | v ^ 4 ≠ 1} ∧ orderOf u = 2) :
    ∃ y : S, y ∈ omegaCorePreimage S ∧ y ∉ noncyclicRotationPreimage S ∧
      orderOf y = 2 ∧
      ¬ 2 ∣ ((centralizer ({y} : Set S)).map (S : Subgroup G).subtype).relIndex
        (centralizer ({(z : G)} : Set G) ⊓ centralizer ({(y : G)} : Set G)) := by
  obtain ⟨u, huR, hu⟩ := hseed
  let e := omegaCorePreimageEquiv S
  let x : S := e.symm u
  have hxR : x ∉ noncyclicRotationPreimage S := by
    rw [noncyclicRotationPreimage_eq_map_quotient_core]
    rintro ⟨v, hv, he⟩
    have hvu : v = u := ((omegaCorePreimage S).subtype_injective.comp e.symm.injective) he
    exact huR (hvu ▸ hv)
  have hx : orderOf x = 2 :=
    (orderOf_coe (e.symm u)).trans ((e.symm.orderOf_eq u).trans hu)
  exact exists_outside_rotation_involution_with_local_sylow_centralizer_of_seed
    S hZ z hzc hz x (e.symm u).property hxR hx

/-- The large noncyclic Hall factor supplies the quotient-core seed needed by
the local Sylow-centralizer selection. The rotation product in the conclusion
is the intrinsic fourth-power product in the actual core preimage. -/
public theorem exists_outside_rotation_involution_with_local_sylow_centralizer
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hD : IsBinaryHallFactor D)
    (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2) :
    ∃ x : S, x ∈ omegaCorePreimage S ∧
      x ∉ (Subgroup.closure {u : omegaCorePreimage S | u ^ 4 ≠ 1}).map
        (omegaCorePreimage S).subtype ∧ orderOf x = 2 ∧
      ¬ 2 ∣ ((centralizer ({x} : Set S)).map (S : Subgroup G).subtype).relIndex
        (centralizer ({(z : G)} : Set G) ⊓ centralizer ({(x : G)} : Set G)) := by
  let H := pCore 2 (OmegaQuotient S)
  let : IsCyclic (center H) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hseed : ∃ u : H, u ∉ Subgroup.closure {v : H | v ^ 4 ≠ 1} ∧
      orderOf u = 2 := by
    simpa only [H] using
      (Subgroup.exists_involution_outside_fourth_power_closure_of_large_hall
        (pCore_isPGroup (p := 2) (G := OmegaQuotient S)) B D hD hn hc hg hlarge)
  obtain ⟨x, hxH, hxR, hx, hlocal⟩ :=
    exists_outside_rotation_involution_with_local_sylow_centralizer_of_quotient_seed
      S hZ z hzc hz hseed
  exact ⟨x, hxH, hxR, hx, hlocal⟩

end Stellmacher.Recognition.NormalEightNonnormalImage
