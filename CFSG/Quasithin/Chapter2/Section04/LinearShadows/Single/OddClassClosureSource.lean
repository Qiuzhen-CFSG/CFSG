module
public import Theory.GroupTheory.ElementaryClassClosure
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ThompsonNormalSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideSuzukiSource
/-!
# The elementary outside class closure in the noncentral branch

The original Δ-centrality and normality of R in M first absorb conjugates
of a Δ involution that commute with another Δ element into R. For an
outside involution x, its fixed Thompson center is elementary, nontrivial,
and all its nonidentity elements lie in Δ. The elementary normalizer
criterion therefore makes that fixed center the entire u-class intersection
in every containing two-subgroup of C_G(x).

Source: Aschbacher–Smith, Lemma 2.4.24(2), the odd half-degree branch on
printed p.540. The only earlier fusion premise is the original 2.4.21
involution closure of R in T.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)

include hG hST hsingle hL hM hTM hunique

private theorem source_center_elementary_for_class_closure :
    IsElementaryAbelian 2 ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) : Subgroup G) := by
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let U := sourceModule (d.block.map d.H.subtype)
  have hU : U=twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  have hAU := (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  exact IsElementaryAbelian.of_injective (inclusion hAU) (inclusion_injective hAU)

theorem source_delta_class_in_centralizer_mem_thompson
    (hclosed : ∀ r t:T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) → (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (u v : G) (hu : u∈distinguishedDelta d x) (hv : v∈distinguishedDelta d x)
    (t : G) (ht : t∈centralizer ({v}:Set G)) (hut : IsConj u t) :
    t∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := R⊓centralizer (R:Set G)
  let : IsElementaryAbelian 2 A := source_center_elementary_for_class_closure d hG T hST hsingle hL hM hTM hunique
  have hRT : R≤(T:Subgroup G) := (show R≤S from sSup_le fun _ h=>h.1).trans hST.le
  have huA : u∈A := hu.1
  have hu1 : u≠1 := fun he => hu.2.1 (he ▸ (distinguishedZ d).one_mem)
  have hu2 : orderOf u=2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u huA) hu1
  have hMR := source_noncenterless_thompson_normal d hG T hST hsingle hL hM hTM hunique hz
  have hvdata := source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz x hxT hxS v hv
  obtain ⟨m,hm,hmc⟩ := hvdata.1
  let f := MulAut.conj m
  let H := centralizer ({f v}:Set G)
  have hTH : (T:Subgroup G)≤H := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hmc.2 a ha)
  have hHM : H≤M := by
    intro a ha
    have hfa : f.symm a ∈ centralizer ({v}:Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul,f.apply_symm_apply] using mem_centralizer_singleton_iff.mp ha
    have hh := (mem_normalizer_iff.mp (M.le_normalizer hm) (f.symm a)).mp
      (hvdata.2.2.1 hfa)
    exact f.apply_symm_apply a ▸ hh
  have hft : f t ∈ H := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ht)
  have hh := class_mem_of_normalized_core_and_sylow T R H hTH (hHM.trans hMR)
    ⟨u,hRT huA.1⟩ ((orderOf_coe (⟨u,hRT huA.1⟩:T)).symm.trans hu2) huA.1 hclosed
    (f t) hft (hut.trans (isConj_iff.mpr ⟨m,rfl⟩))
  exact (mem_normalizer_iff.mp (hMR hm) t).mpr hh

theorem source_noncenterless_outside_fixed_nonidentity_mem_delta
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (v : G)
    (hv : v∈(Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype):Set G))⊓
        centralizer ({x}:Set G)) (hv1 : v≠1) : v∈distinguishedDelta d x := by
  have hp := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
  let e := MulAut.conj x⁻¹
  have hc : Commute x v := (mem_centralizer_singleton_iff.mp hv.2).symm
  have hev : e v=v := mul_inv_eq_iff_eq_mul.mpr hc.inv_left.eq
  have hnZ : v∉distinguishedZ d := by
    intro hZ
    exact hv1 (disjoint_def.mp hp.1 hZ ⟨v,hZ,hev⟩)
  refine ⟨hv.1,hnZ,?_⟩
  rintro ⟨z,hzZ,he⟩
  have hzv : z=v := e.injective (he.trans hev.symm)
  exact hnZ (hzv ▸ hzZ)

theorem source_noncenterless_outside_elementary_class_closure
    (c : CyclicTorusSetup d T n)
    (hclosed : ∀ r t:T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) → (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (hxB : x∈normalizer (c.hall:Set G)) (hx2 : x^2=1)
    (u : G) (hu : u∈distinguishedDelta d x)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPC : P≤centralizer ({x}:Set G))
    (hVP : (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype):Set G))⊓
        centralizer ({x}:Set G) ≤ P) :
    ∀ t∈P, IsConj u t → t∈
      (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype):Set G))⊓
          centralizer ({x}:Set G) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  let A := R⊓centralizer (R:Set G)
  let V := A⊓centralizer ({x}:Set G)
  let : IsElementaryAbelian 2 A := source_center_elementary_for_class_closure d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion (show V≤A from inf_le_left)) (inclusion_injective _)
  have hV : V≠⊥ := by
    have hc := (source_noncenterless_outside_center_fixed_data d hG T hST hsingle hL hM hTM hunique hz x hxT hxS hx2).1
    intro he
    change Nat.card V=2^n at hc
    rw [he,card_bot] at hc
    have hn := hL.1
    have hh : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hdelta : ∀ v∈V, v≠1 → v∈distinguishedDelta d x :=
    source_noncenterless_outside_fixed_nonidentity_mem_delta d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
  have huA : u∈A := hu.1
  have hu1 : u≠1 := fun he => hu.2.1 (he ▸ (distinguishedZ d).one_mem)
  have hu2 : orderOf u=2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u huA) hu1
  apply class_mem_of_elementary_centralizer_control P V hP hV hVP u hu2
  · intro v hv hv1
    obtain ⟨b,hb,he⟩ := source_distinguished_delta_transitive d hG T hST hsingle hL hM hTM hunique c hz x hxT hxS hxB u hu v (hdelta v hv hv1)
    exact isConj_iff.mpr ⟨b,he⟩
  · intro v hv hv1 t ht hut htv
    have htR := source_delta_class_in_centralizer_mem_thompson d hG T hST hsingle hL hM hTM hunique hclosed hz x hxT hxS u v hu (hdelta v hv hv1) t
      (mem_centralizer_singleton_iff.mpr htv.eq) hut
    have ht2 : t^2=1 := isConj_one_right.mp ((by simpa only [hu2] using pow_orderOf_eq_one u) ▸ IsConj.pow 2 hut)
    exact ⟨source_outside_fixed_involution_mem_center d hG T hST hsingle hL hM hTM hunique x hxT hxS t htR ht2
      (mem_centralizer_singleton_iff.mp (hPC ht)).symm,hPC ht⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
