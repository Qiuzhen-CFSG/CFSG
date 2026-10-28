module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupTheory.InvolutionTransfer
public import Mathlib.GroupTheory.Nilpotent

/-!
# Squares, saturated centralizers, and involution transfer

An ambient square root of an involution can be moved into a Sylow subgroup
when the involution's Sylow centralizer is maximal in its ambient centralizer.
Sylow conjugacy inside that centralizer moves the cyclic group of order four
while fixing the involution. Consequently the property of being a square
passes along fusion towards an involution with saturated centralizer.

Thompson transfer therefore excludes an involution outside an index-two
subgroup if it has saturated centralizer, cannot fuse into a specified core,
and every involution in the maximal subgroup outside that core is a square.
A normalizer-condition lemma upgrades saturation in a smaller centralizer to
saturation in the full centralizer when the normalizer preserves the smaller one.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- An ambient square root can be placed in the Sylow when its involution
has saturated Sylow centralizer. -/
public theorem exists_square_root_of_saturated_centralizer {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (x : S) (hx : orderOf x = 2)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype)
    (r : G) (hr : r ^ 2 = (x : G)) : ∃ s : S, s ^ 2 = x := by
  let C := centralizer ({(x : G)} : Set G)
  let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  have hEC : E ≤ C := by
    dsimp only [E, C]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hEp : IsPGroup 2 E := (S.isPGroup'.to_subgroup _).map _
  obtain ⟨P, hEP⟩ := (hEp.comap_subtype (K := C)).exists_le_sylow
  have hPE : (P : Subgroup C).map C.subtype = E :=
    hmax _ (P.isPGroup'.map _) (by
      change E ≤ _
      rw [← map_subgroupOf_eq_of_le hEC]
      exact map_mono hEP) (map_subtype_le _)
  have hrC : r ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hr]
    exact (Commute.self_pow r 2).eq
  let rC : C := ⟨r, hrC⟩
  have hr4 : rC ^ 4 = 1 := by
    apply Subtype.ext
    change r ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hr]
    exact congrArg Subtype.val (by simpa only [hx] using pow_orderOf_eq_one x)
  have hp : IsPGroup 2 (zpowers rC) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hr4)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq C Q P
  have hrP : (MulAut.conj a) rC ∈ P := by
    rw [← ha]
    change (MulAut.conj a) • rC ∈ (MulAut.conj a) • (Q : Set C)
    exact Set.smul_mem_smul_set (hQ (mem_zpowers rC))
  have hrE : (((MulAut.conj a) rC : C) : G) ∈ E := by
    rw [← hPE]
    exact mem_map_of_mem C.subtype hrP
  obtain ⟨s, _, hs⟩ := hrE
  refine ⟨s, Subtype.ext ?_⟩
  change (s : G) ^ 2 = (x : G)
  change (s : G) = _ at hs
  rw [hs]
  change ((MulAut.conj (a : G)) r) ^ 2 = (x : G)
  rw [← map_pow, hr]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)

/-- Square roots pass along fusion to an involution with saturated centralizer. -/
public theorem exists_square_root_of_isConj_of_saturated_centralizer {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (x : S) (hx : orderOf x = 2)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype)
    (y : S) (hxy : IsConj (x : G) (y : G))
    (hy : ∃ r : S, r ^ 2 = y) : ∃ s : S, s ^ 2 = x := by
  obtain ⟨r, hr⟩ := hy
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  let f := MulAut.conj a
  apply S.exists_square_root_of_saturated_centralizer x hx hmax (f.symm (r : G))
  apply f.injective
  rw [map_pow, f.apply_symm_apply]
  exact (congrArg Subtype.val hr).trans ha.symm

/-- Transfer excludes a nonsquare involution when the only possible targets
outside the core are squares and fusion into the core is impossible. -/
public theorem false_of_index_two_square_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (H M : Subgroup S) (hM : M.index = 2)
    (x : S) (hx : orderOf x = 2) (hxM : x ∉ M)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype)
    (hcore : ∀ u : S, u ∈ H → ¬ IsConj (x : G) (u : G))
    (hsquares : ∀ u : S, u ∈ M → u ∉ H → orderOf u = 2 →
      ∃ r : S, r ^ 2 = u) : False := by
  obtain ⟨u, hxu, huM⟩ := S.exists_isConj_mem_of_index_two hno M hM x hx
  have huH : u ∉ H := fun hu => hcore u hu hxu
  have hu : orderOf u = 2 := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxu
    have he : (MulAut.conj a) (x : G) = u := ha
    rw [← Subgroup.orderOf_coe, ← he, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  obtain ⟨r, hr⟩ := S.exists_square_root_of_isConj_of_saturated_centralizer
    x hx hmax u hxu (hsquares u huM huH hu)
  exact hxM (hr ▸ M.sq_mem_of_index_two hM r)

end Sylow

namespace Subgroup

/-- Saturation in `N ∩ C` upgrades to saturation in `C` if the normalizer
inside `C` is contained in `N`. The p-group normalizer condition proves this. -/
public theorem saturated_of_normalizer_control {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (E N C : Subgroup G)
    (hmax : ∀ V : Subgroup G, IsPGroup p V → E ≤ V → V ≤ N ⊓ C → V = E)
    (hcontrol : normalizer (E : Set G) ⊓ C ≤ N) :
    ∀ V : Subgroup G, IsPGroup p V → E ≤ V → V ≤ C → V = E := by
  intro V hVp hEV hVC
  by_contra hne
  let L := E.subgroupOf V
  have hproper : L < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun hVE => hne (le_antisymm hVE hEV)
  let : Group.IsNilpotent V := hVp.isNilpotent
  obtain ⟨u, huN, huL⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent L hproper)
  let R : Subgroup G := V ⊓ normalizer (E : Set G)
  have hR : R = E := hmax R hVp.to_inf_left (le_inf hEV E.le_normalizer)
    (le_inf (fun v hv => hcontrol ⟨hv.2, hVC hv.1⟩) (inf_le_left.trans hVC))
  apply huL
  change (u : G) ∈ E
  rw [← hR]
  refine ⟨u.property, ?_⟩
  rw [← subgroupOf_normalizer_eq hEV] at huN
  exact huN

end Subgroup
