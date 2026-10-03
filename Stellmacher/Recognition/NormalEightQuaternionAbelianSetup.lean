module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightOmegaNormalizerCentralizer
public import Theory.GroupTheory.SaturatedCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

public import Theory.GroupTheory.PGroup.ExtraspecialFixedCentralizerLine

/-!
# Local reductions for quaternion-core abelian quotients

For the cyclic-four and elementary-four quotient branches, the outside
involution may be chosen fully centralized inside the central-omega normalizer.
Membership in the core preimage is invariant under this local conjugacy,
because the corresponding subgroup of the normalizer is normal. Consequently
the selected involution is still outside the core.

When its fixed core is extraspecial, the derived-center intersection of its
Sylow centralizer is the original central involution line. The remaining
quaternion action calculations and the elementary fixed-core transfer argument
are separate from these selection and characteristic-line reductions.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.390–391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugacy inside the omega normalizer preserves core-preimage membership. -/
public theorem omegaCorePreimage_mem_iff_of_local_isConj
    (S : Sylow 2 G) (x y : S)
    (hconj : IsConj (inclusion (sylow_le_omegaNormalizer S) x)
      (inclusion (sylow_le_omegaNormalizer S) y)) :
    x ∈ omegaCorePreimage S ↔ y ∈ omegaCorePreimage S := by
  let N := omegaNormalizer S
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  let K := (pCore 2 (OmegaQuotient S)).comap q
  have hmem (a b : S)
      (hab : IsConj (inclusion (sylow_le_omegaNormalizer S) a)
        (inclusion (sylow_le_omegaNormalizer S) b))
      (ha : a ∈ omegaCorePreimage S) : b ∈ omegaCorePreimage S := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hab
    have haK : inclusion (sylow_le_omegaNormalizer S) a ∈ K := by
      change omegaQuotientHom S a ∈ pCore 2 (OmegaQuotient S) at ha
      rw [omegaQuotientHom_apply] at ha
      exact ha
    have hbK := (inferInstance : K.Normal).conj_mem _ haK g
    rw [hg] at hbK
    change omegaQuotientHom S b ∈ pCore 2 (OmegaQuotient S)
    rw [omegaQuotientHom_apply]
    exact hbK
  exact ⟨hmem x y hconj, hmem y x hconj.symm⟩

/-- An outside element has an outside local conjugate with maximal local two-centralizer. -/
public theorem exists_outside_conjugate_with_saturated_local_centralizer
    (S : Sylow 2 G) (x : S) (hx : x ∉ omegaCorePreimage S) :
    ∃ t : S,
      IsConj (inclusion (sylow_le_omegaNormalizer S) x)
        (inclusion (sylow_le_omegaNormalizer S) t) ∧
      t ∉ omegaCorePreimage S ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ omegaNormalizer S → V ≤ centralizer ({(t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  let N := omegaNormalizer S
  let T := S.subtype (sylow_le_omegaNormalizer S)
  let e : T ≃* S := subgroupOfEquivOfLe (sylow_le_omegaNormalizer S)
  obtain ⟨u, hxu, hmax⟩ := T.exists_conjugate_with_saturated_centralizer (e.symm x)
  let t := e u
  have hconj : IsConj (inclusion (sylow_le_omegaNormalizer S) x)
      (inclusion (sylow_le_omegaNormalizer S) t) := hxu
  let U := (centralizer ({u} : Set T)).map (T : Subgroup N).subtype
  let E := (centralizer ({t} : Set S)).map (S : Subgroup G).subtype
  have hUE : U.map N.subtype = E := by
    apply le_antisymm
    · rintro y ⟨n, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨e v, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hv)
    · rintro y ⟨v, hv, rfl⟩
      refine ⟨((e.symm v : T) : N), ⟨e.symm v, ?_, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hv
  refine ⟨t, hconj, fun ht => hx ((omegaCorePreimage_mem_iff_of_local_isConj S x t hconj).mpr ht), ?_⟩
  intro V hpV hEV hVN hVC
  have hVU : V.subgroupOf N = U := hmax _ hpV.comap_subtype (by
    intro n hn
    have hnE : (n : G) ∈ E := by
      rw [← hUE]
      exact mem_map_of_mem N.subtype hn
    exact hEV hnE) (by
    intro n hn
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hVC hn)))
  have he := congrArg (fun L : Subgroup N => L.map N.subtype) hVU
  rwa [map_subgroupOf_eq_of_le hVN, hUE] at he


/-- Choose an outside involution with saturated common centralizer while preserving fusion. -/
public theorem exists_outside_isConj_with_saturated_common_centralizer
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hx : x ∉ omegaCorePreimage S) (hzx : IsConj (z : G) (x : G)) :
    ∃ t : S, orderOf t = 2 ∧ t ∉ omegaCorePreimage S ∧
      IsConj (z : G) (t : G) ∧
      IsConj (inclusion (sylow_le_omegaNormalizer S) x)
        (inclusion (sylow_le_omegaNormalizer S) t) ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  obtain ⟨t, hxt, ht, hsat⟩ :=
    exists_outside_conjugate_with_saturated_local_centralizer S x hx
  have hzt : IsConj (z : G) (t : G) :=
    hzx.trans ((omegaNormalizer S).subtype.map_isConj hxt)
  have htorder : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    exact ((MulAut.conj g).orderOf_eq (z : G)).trans ((orderOf_coe z).trans hz)
  refine ⟨t, htorder, ht, hzt, hxt, ?_⟩
  intro V hpV hEV hVC
  apply hsat V hpV hEV
  · rw [omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzc]
    intro v hv
    exact mem_centralizer_singleton_iff.mpr ((hVC hv z (by simp)).symm)
  · intro v hv
    exact mem_centralizer_singleton_iff.mpr ((hVC hv t (by simp)).symm)

/-- A core of order thirty-two and index four gives Sylow order 128. -/
public theorem sylow_card_eq_one_twenty_eight_of_quaternion_core_index_four
    (S : Sylow 2 G) (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4) : Nat.card S = 128 := by
  have h := (omegaCorePreimage S).card_mul_index
  rw [card_omegaCorePreimage, hH, hindex] at h
  exact h.symm


/-- An extraspecial fixed core gives the characteristic central line needed
for the non-elementary fixed-core fusion exclusion. -/
public theorem omegaCorePreimage_centralizer_derived_inf_center_line
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [IsMulCommutative (S ⧸ omegaCorePreimage S)]
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    [IsExtraspecial 2 ((omegaCorePreimage S).subgroupOf (centralizer ({t} : Set S)))] :
    (_root_.commutator (centralizer ({t} : Set S)) ⊓
      center (centralizer ({t} : Set S))).map
      (centralizer ({t} : Set S)).subtype = zpowers z := by
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  exact centralizer_derived_inf_center_line_of_extraspecial_fixed
    (omegaCorePreimage S) z t hz hzc
    (four_le_omegaCorePreimage hN S hZ W hW hno hzW)

end Stellmacher.Recognition.NormalEightNonnormalImage
