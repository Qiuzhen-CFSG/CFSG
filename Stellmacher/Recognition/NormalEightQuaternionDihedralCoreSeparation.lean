module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightQuaternionFourNonElementary
public import Theory.GroupTheory.SaturatedDerivedCenterFusion
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizerDerived
public import Theory.GroupTheory.PGroup.ExtraspecialInvolutionDoubleCentralizer

/-!
# Core separation from the characteristic centralizer line

A fixed core of order eight lies outside the extraspecial core of order
thirty-two. To exclude fusion into the core, choose a locally saturated core
representative. Its fixed core has derived group containing the original
central involution. The intrinsic double-centralizer bound then makes the
saturated derived-center transport fix that involution. Such a conjugation
lies in the omega normalizer and preserves core membership, a contradiction.

The intrinsic double-centralizer bound applies because the core is normal
and self-centralizing. The assembly uses no bound on arbitrary elementary
eights and no calculation of squares in a maximal subgroup.

Source: Janko–Thompson (1970), §4, case (c), printed p.392, the assertion
that the saturated nonabelian fixed-eight involution cannot fuse into the core.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

private theorem exists_locally_saturated_core_conjugate
    (S : Sylow 2 G) (u : S) (hu : u ∈ omegaCorePreimage S) :
    ∃ y : S, y ∈ omegaCorePreimage S ∧
      IsConj (inclusion (sylow_le_omegaNormalizer S) u)
        (inclusion (sylow_le_omegaNormalizer S) y) ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({y} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ omegaNormalizer S → V ≤ centralizer ({(y : G)} : Set G) →
        V = (centralizer ({y} : Set S)).map (S : Subgroup G).subtype := by
  let N := omegaNormalizer S
  let T := S.subtype (sylow_le_omegaNormalizer S)
  let e : T ≃* S := subgroupOfEquivOfLe (sylow_le_omegaNormalizer S)
  obtain ⟨v, huv, hmax⟩ := T.exists_conjugate_with_saturated_centralizer (e.symm u)
  let y := e v
  have hconj : IsConj (inclusion (sylow_le_omegaNormalizer S) u)
      (inclusion (sylow_le_omegaNormalizer S) y) := huv
  let U := (centralizer ({v} : Set T)).map (T : Subgroup N).subtype
  let R := (centralizer ({y} : Set S)).map (S : Subgroup G).subtype
  have hUR : U.map N.subtype = R := by
    apply le_antisymm
    · rintro r ⟨n, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨e a, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp ha)
    · rintro r ⟨a, ha, rfl⟩
      refine ⟨((e.symm a : T) : N), ⟨e.symm a, ?_, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp ha
  refine ⟨y, (omegaCorePreimage_mem_iff_of_local_isConj S u y hconj).mp hu, hconj, ?_⟩
  intro V hpV hRV hVN hVC
  have hVU : V.subgroupOf N = U := hmax _ hpV.comap_subtype (by
    intro n hn
    have hnR : (n : G) ∈ R := by
      rw [← hUR]
      exact mem_map_of_mem N.subtype hn
    exact hRV hnR) (by
    intro n hn
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hVC hn)))
  have he := congrArg (fun L : Subgroup N => L.map N.subtype) hVU
  rwa [map_subgroupOf_eq_of_le hVN, hUR] at he

/-- The derived group of every core-element centralizer contains the central
involution, with no bound on arbitrary elementary subgroups. -/
public theorem omegaCorePreimage_centralizer_commutator_contains
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (z : S) (hzc : z ∈ center S) (u : S) (hu : u ∈ omegaCorePreimage S) :
    z ∈ ⁅omegaCorePreimage S ⊓ centralizer ({u} : Set S),
      omegaCorePreimage S ⊓ centralizer ({u} : Set S)⁆ := by
  let P := omegaCorePreimage S
  let : IsExtraspecial 2 P :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hzP : z ∈ P := omegaCorePreimage_centralizer_le hN S hZ
    (fun p _ => mem_center_iff.mp hzc p)
  let uP : P := ⟨u, hu⟩
  have hzPc : (⟨z, hzP⟩ : P) ∈ center P :=
    mem_center_iff.mpr (fun p => Subtype.ext (mem_center_iff.mp hzc p))
  rw [← IsExtraspecial.commutator_centralizer_eq_center_of_card_thirty_two
    ((card_omegaCorePreimage S).trans hH) uP] at hzPc
  have hm := mem_map_of_mem P.subtype hzPc
  rwa [map_commutator, map_subtype_centralizer_singleton] at hm

/-- The intrinsic double-centralizer bound completes core separation for a
saturated centralizer with the supplied characteristic line. -/
public theorem quaternion_dihedral_core_separation_of_double_centralizer
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hdouble : ∀ u : S, u ∈ omegaCorePreimage S → orderOf u = 2 →
      centralizer (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Set S) ≤
        closure ({z, u} : Set S))
    (x : S) (hx : orderOf x = 2)
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8)
    (hline : let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G))
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) :
    ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G) := by
  let P := omegaCorePreimage S
  let : IsExtraspecial 2 P :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hout : x ∉ P := by
    intro hxP
    have hb := IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two
      ((card_omegaCorePreimage S).trans hH) (⟨x, hxP⟩ : P)
    have he : Nat.card (centralizer ({(⟨x, hxP⟩ : P)} : Set P)) =
        Nat.card (P ⊓ centralizer ({x} : Set S) : Subgroup S) := by
      rw [← map_subtype_centralizer_singleton P ⟨x, hxP⟩,
        card_map_of_injective P.subtype_injective]
    rw [he, hcard] at hb
    omega
  have hzP : z ∈ P := omegaCorePreimage_centralizer_le hN S hZ
    (fun p _ => mem_center_iff.mp hzc p)
  have hxz : x ≠ z := fun he => hout (he ▸ hzP)
  intro u hu hxu
  obtain ⟨y, hyP, huy, hlocal⟩ := exists_locally_saturated_core_conjugate S u hu
  have huyG := (omegaNormalizer S).subtype.map_isConj huy
  have hxy : IsConj (x : G) (y : G) := hxu.trans huyG
  have hy : orderOf y = 2 := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxy
    have hh : (MulAut.conj a) (x : G) = y := ha
    rw [← orderOf_coe y, ← hh, MulEquiv.orderOf_eq, orderOf_coe, hx]
  obtain ⟨g, hg, hgy⟩ := S.exists_local_conjugator_of_saturated_derived_center
    z x y hz hy hzc hxz hline hmax (by
      intro V hpV hRV hVz hVy
      apply hlocal V hpV hRV _ hVy
      rwa [omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzc])
    (P ⊓ centralizer ({y} : Set S)) inf_le_right
    (omegaCorePreimage_centralizer_commutator_contains hN S hZ hH z hzc y hyP)
    (hdouble y hyP hy) hxy.symm
  have hgN : g ∈ omegaNormalizer S := by
    rwa [omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzc]
  have hyx : IsConj (inclusion (sylow_le_omegaNormalizer S) y)
      (inclusion (sylow_le_omegaNormalizer S) x) :=
    isConj_iff.mpr ⟨⟨g, hgN⟩, Subtype.ext hgy⟩
  exact hout ((omegaCorePreimage_mem_iff_of_local_isConj S y x hyx).mp hyP)

/-- A saturated involution centralizer with fixed core of order eight and the
specified derived-center line cannot fuse its involution into the extraspecial
core of order thirty-two. -/
public theorem quaternion_dihedral_core_separation
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (x : S) (hx : orderOf x = 2)
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8)
    (hline : let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G))
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) :
    ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G) := by
  let : IsExtraspecial 2 (omegaCorePreimage S) :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  apply quaternion_dihedral_core_separation_of_double_centralizer
    hN S hZ hH z hz hzc ?_ x hx hcard hline hmax
  intro u hu hu2
  exact IsExtraspecial.ambient_involution_double_centralizer_le
    (omegaCorePreimage S) (omegaCorePreimage_centralizer_le hN S hZ)
    z u hz hzc hu hu2

end Stellmacher.Recognition.NormalEightNonnormalImage
