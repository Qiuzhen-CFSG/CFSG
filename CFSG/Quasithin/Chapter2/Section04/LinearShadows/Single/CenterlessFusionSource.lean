module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideNoncentralFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterCentralFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModuleFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldDerivedSource

/-!
# Involution fusion in the original centerless single linear branch

Every involution of R is fused into its center Z. An outside involution fused
into Z must centralize Z, by the fixed-derived and cyclic-action argument; the
central elementary-product exclusion then places it in R. An inside involution
uses the actual field fixed-derived inclusion and the same cyclic-action
argument, followed by C_S(Z)=R.

This proves the full original 2.4.21(2) in the centerless block branch, with all
local geometry and action premises discharged. The record method is the literal
T-valued closure contract consumed by source 2.4.22 and terminal transfer.
Source: Aschbacher–Smith, printed pp.535–537.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_outside_involution_not_fused
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (r a : G)
    (hr : r∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hr2 : orderOf r=2) (haT : a∈T)
    (haS : a∉(d.S : Subgroup d.H).map d.H.subtype) : ¬IsConj r a := by
  intro hfused
  have hr1 : r≠1 := by intro he; simp only [he,orderOf_one] at hr2; omega
  obtain ⟨z,hz,_,hrz⟩ := source_involution_fused_into_distinguished_of_centerless
    d hG T hST hsingle hL hM hTM hunique hZ r hr
    (by simpa only [hr2] using pow_orderOf_eq_one r) hr1
  have haz : IsConj a z := hfused.symm.trans hrz
  obtain ⟨g,hg⟩ := isConj_iff.mp haz.symm
  have hzdef := distinguishedZ_of_centerless d hZ
  have ha2 : a^2=1 := by
    obtain ⟨u,hu⟩ := hfused
    have hh : orderOf a=2 := (hu.orderOf_eq u.val).symm.trans hr2
    simpa only [hh] using pow_orderOf_eq_one a
  have hac := source_centerless_outside_conjugate_centralizes d hG T hST hsingle hL
    hM hTM hunique c hZ a g haT haS ha2 (by
      rw [←hzdef]
      exact ⟨z,hz,hg⟩)
  have hac' : a∈centralizer (distinguishedZ d:Set G) := by rwa [hzdef]
  have har := source_centerless_central_fusion_contained d hG T hST hsingle hL
    hM hTM hunique hZ a z haT hz haz hac'
  have hRS : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      (d.S : Subgroup d.H).map d.H.subtype := sSup_le fun _ h=>h.1
  exact haS (hRS har)


theorem source_centerless_involution_fusion_closed
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (r a : G)
    (hr : r∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hr2 : orderOf r=2) (haT : a∈T) (hfused : IsConj r a) :
    a∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  by_contra haR
  have haS : a∈(d.S : Subgroup d.H).map d.H.subtype := by
    by_contra hn
    exact source_centerless_outside_involution_not_fused d hG T hST hsingle hL
      hM hTM hunique c hZ r a hr hr2 haT hn hfused
  have hr1 : r≠1 := by intro he; simp only [he,orderOf_one] at hr2; omega
  have ha1 : a≠1 := fun he=>haR (he ▸ one_mem _)
  have haorder : orderOf a=2 := by
    obtain ⟨u,hu⟩ := hfused
    exact (hu.orderOf_eq u.val).symm.trans hr2
  have ha2 : a^2=1 := by simpa only [haorder] using pow_orderOf_eq_one a
  obtain ⟨z,hz,_,hrz⟩ := source_involution_fused_into_distinguished_of_centerless
    d hG T hST hsingle hL hM hTM hunique hZ r hr
    (by simpa only [hr2] using pow_orderOf_eq_one r) hr1
  have haz : IsConj a z := hfused.symm.trans hrz
  obtain ⟨g,hg⟩ := isConj_iff.mp haz.symm
  have hd := source_centerless_inside_fixed_center_le_derived d hG T hST hsingle hL
    hM hTM hunique c hZ a haS haorder haR
  have hac := source_centerless_conjugate_centralizes_of_fixed_derived d hG T hST hsingle hL
    hM hTM hunique c hZ a g haT ha2 ha1 (by
      rw [←distinguishedZ_of_centerless d hZ]
      exact ⟨z,hz,hg⟩) hd
  have hac' : a∈centralizer (distinguishedZ d:Set G) := by
    rwa [distinguishedZ_of_centerless d hZ]
  exact haR ((source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL
    hM hTM hunique).le ⟨haS,hac'⟩)

theorem CyclicTorusSetup.centerless_involution_fusion_closed
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥) :
    ∀ r t : T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) →
      (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  intro r t hr2 hr hrt
  exact source_centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hunique c hZ
    r t hr ((Subgroup.orderOf_coe r).trans hr2) t.property hrt
end CFSG.Quasithin.Chapter2.LinearShadows.Single
