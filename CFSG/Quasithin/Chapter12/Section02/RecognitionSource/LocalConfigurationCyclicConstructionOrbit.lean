module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionDefs
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.PGroup.CommutatorKernel
public import Theory.GroupTheory.TIElementaryOrbit
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The pair core and elementary orbit in 12.2.21--22

The image of U = [U,⟨g⟩] in H/O₂(H) lies simultaneously in a two-subgroup
and the normal odd-prime core, so U ≤ O₂(H). The index-two pair hyperplane
and movement of V identify U ∩ V with O₂(H) ∩ V. Its H-conjugates commute
by TI and relative normality inside O₂(H).

The actual factorization H = PT identifies this elementary H-orbit with
⟨Uᴾ⟩. Pair commutators then supply [W,P] = W and [W,V] = U ∩ V.
The initial pair is an explicit source input. This module does not assume
or prove the subsequent invariant-Sylow selection.
Source: Aschbacher--Smith, 12.2.21--22, printed pp.802--803.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}

namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

private theorem prime_le : P ≤ H := S.overgroup ▸ le_sup_left

private theorem core_le (D : ChosenModule T L V) : U ≤ H := by
  have hVH := D.le_sylow.trans S.hstar.1.1.2
  rw [S.core_generated]
  refine sup_le (inf_le_right.trans hVH) ?_
  rw [← mem_normalizer_iff_map_conj_eq.mp
    (H.le_normalizer (S.prime_le S.generator_mem))]
  exact map_mono (inf_le_right.trans hVH)

/-- The two-core of the literal pair lies in O₂(H), as in 12.2.21. -/
theorem core_in_hstar_core (D : ChosenModule T L V) : U ≤ H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hUH := S.core_le D
  have hgH : zpowers g ≤ H := (zpowers_le.mpr S.generator_mem).trans S.prime_le
  have hU2 : IsPGroup 2 U := S.pair_core ▸ isPGroup_pCoreIn 2 _
  have hm : ⁅U.subgroupOf H, (zpowers g).subgroupOf H⁆ = U.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUH,
      map_subgroupOf_eq_of_le hgH, S.core_moved]
  have hR : ((zpowers g).subgroupOf H).map q ≤ pCore p (H ⧸ pCore 2 H) := by
    rw [← S.quotient_core]
    exact map_mono (subgroupOf_mono H (zpowers_le.mpr S.generator_mem))
  have hk := pgroup_le_ker_of_commutator_eq_self q (U.subgroupOf H)
    ((zpowers g).subgroupOf H) (pCore p (H ⧸ pCore 2 H)) hU2.comap_subtype
    pCore_isPGroup (Nat.coprime_two_left.mpr S.odd_prime) hm hR
  rw [QuotientGroup.ker_mk'] at hk
  have hh := map_mono (f := H.subtype) hk
  rwa [map_subgroupOf_eq_of_le hUH] at hh

/-- Movement of V and its pair hyperplane identify the intersection with O₂(H). -/
theorem core_intersection (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    H.pCoreIn 2 ⊓ V = U ⊓ V := by
  have hi : U ⊓ V ≤ H.pCoreIn 2 ⊓ V := inf_le_inf_right V (S.core_in_hstar_core D)
  have hd : (H.pCoreIn 2 ⊓ V).relIndex V ∣ 2 := by
    have hd := relIndex_dvd_of_le_left V hi
    rwa [S.hyperplane_index] at hd
  have he : (H.pCoreIn 2 ⊓ V).relIndex V = 2 := by
    apply ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    intro h1
    exact A.hstar_movement H S.hstar ((relIndex_eq_one.mp h1).trans inf_le_left)
  have ht := relIndex_mul_relIndex (U ⊓ V) (H.pCoreIn 2 ⊓ V) V hi inf_le_right
  rw [he, S.hyperplane_index] at ht
  have h1 : (U ⊓ V).relIndex (H.pCoreIn 2 ⊓ V) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp h1) hi

omit S in
private theorem overgroup_normalizes_core (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

private theorem core_le_sylow : H.pCoreIn 2 ≤ (T : Subgroup G) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
  exact hy

omit S in
/-- The canonical H-orbit of O₂(H) ∩ V lies in O₂(H). -/
theorem orbit_in_core (H V : Subgroup G) : componentOrbit (H.pCoreIn 2 ⊓ V) H ≤ H.pCoreIn 2 :=
  iSup_conjugates_le_of_le_normalizer _ _ _ inf_le_left (overgroup_normalizes_core H)

/-- The canonical H-orbit is elementary. Only relative normality of O₂(H) is used. -/
theorem orbit_elementary (D : ChosenModule T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    IsElementaryAbelian 2 (componentOrbit (H.pCoreIn 2 ⊓ V) H) := by
  let := D.elementary
  refine elementary_orbit_of_relative_ti (H.pCoreIn 2 ⊓ V) V (H.pCoreIn 2) H
    inf_le_right inf_le_left ?_ (overgroup_normalizes_core H) ?_
  · exact (le_inf (H.pCoreIn 2).le_normalizer
      (S.core_le_sylow.trans hTV)).trans inf_normalizer_le_normalizer_inf
  · intro x _
    exact (hTI.eq_or_disjoint_conjugate x).imp id (fun hd => hd.symm)

/-- The H-orbit of the hyperplane is exactly the P-orbit of the whole pair core. -/
theorem orbit_eq (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    componentOrbit (H.pCoreIn 2 ⊓ V) H = componentOrbit U P := by
  let B := H.pCoreIn 2 ⊓ V
  let W := componentOrbit B H
  have hBeq : B = U ⊓ V := S.core_intersection D A
  have hBT : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (le_inf (S.hstar.1.1.2.trans (overgroup_normalizes_core H)) hTV).trans
      inf_normalizer_le_normalizer_inf
  have hUW : U ≤ W := by
    rw [S.core_generated, ← hBeq]
    refine sup_le (le_componentOrbit B H) ?_
    exact le_iSup (fun x : H => B.map (MulAut.conj (x : G)).toMonoidHom)
      ⟨g, S.prime_le S.generator_mem⟩
  apply le_antisymm
  · apply iSup_le
    intro x
    obtain ⟨a, ha, t, ht, he⟩ := S.factorization x x.property
    have hprod : B.map (MulAut.conj (x : G)).toMonoidHom =
        (B.map (MulAut.conj t).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      rw [he, map_map]
      congr 1
      ext b
      simp [MulAut.conj_apply, mul_assoc]
    have htB : B.map (MulAut.conj t).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (hBT ht)
    rw [hprod, htB]
    exact (map_mono (hBeq.le.trans inf_le_left)).trans
      (le_iSup (fun a : P => U.map (MulAut.conj (a : G)).toMonoidHom) ⟨a, ha⟩)
  · exact iSup_conjugates_le_of_le_normalizer U P W hUW
      (S.prime_le.trans (le_normalizer_componentOrbit B H))

theorem orbit_intersection (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    componentOrbit (H.pCoreIn 2 ⊓ V) H ⊓ V = U ⊓ V := by
  rw [← S.core_intersection D A]
  apply le_antisymm (inf_le_inf_right V (orbit_in_core H V))
  exact le_inf (le_componentOrbit _ _) inf_le_right

/-- Pair movement propagates to every P-conjugate of U. -/
theorem orbit_moved (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅componentOrbit (H.pCoreIn 2 ⊓ V) H, P⁆ = componentOrbit (H.pCoreIn 2 ⊓ V) H := by
  rw [S.orbit_eq D A hTV]
  apply le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_componentOrbit U P))
  apply iSup_conjugates_le_of_le_normalizer U P _ _ (normalizer_commutator_ge_right _ _)
  conv_lhs => rw [← S.core_moved]
  exact commutator_mono (le_componentOrbit U P) (zpowers_le.mpr S.generator_mem)

/-- The invariant orbit has exactly the same transvection axis as the pair. -/
theorem orbit_transvections (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅componentOrbit (H.pCoreIn 2 ⊓ V) H, V⁆ = U ⊓ V := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  have hUW : U ≤ W := (le_componentOrbit U P).trans_eq (S.orbit_eq D A hTV).symm
  apply le_antisymm
  · rw [← S.orbit_intersection D A]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp
        ((D.le_sylow.trans S.hstar.1.1.2).trans (le_normalizer_componentOrbit _ _)))
      (le_normalizer_iff_commutator_le_right.mp
        ((orbit_in_core H V).trans (S.core_le_sylow.trans hTV)))
  · rw [← S.transvections]
    exact commutator_mono hUW le_rfl

end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
