module
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.AlternatingSevenNormalized
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Perfect images in the empty-family rank bound

Original 14.1.18 bounds the three-rank of the module centralizer in M.
Every perfect subgroup of M lies in that centralizer, since its quotient is
S₃. Taking the solvable residual transfers this bound to perfect subgroups
of an image of M through a map with two-group kernel. This is the ambient
rank obstruction used in the M₂₂ branch of original 14.3.6(6).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_perfect_threeRank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (D : Subgroup G) [Group.IsPerfect D] (hDM : D ≤ M) : primeRank 3 D ≤ 1 := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let DM := D.subgroupOf M
  let ed : DM ≃* D := subgroupOfEquivOfLe hDM
  let : Group.IsPerfect DM := Group.IsPerfect.ofSurjective
    (f := ed.symm.toMonoidHom) ed.symm.surjective
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide +kernel)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (M ⧸ C) := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hDC : DM ≤ C := le_of_isPerfect_of_solvable_quotient DM C
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hr,_,_,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hc : C.map M.subtype = M ⊓ centralizer (localModule T M : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hle : D ≤ M ⊓ centralizer (localModule T M : Set G) := by
    have hh := map_mono (f := M.subtype) hDC
    rwa [map_subgroupOf_eq_of_le hDM,hc] at hh
  exact (primeRank_mono 3 hle).trans hr

theorem source_perfect_image_threeRank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K : Subgroup G) {B : Type*} [Group B] [Finite B]
    (q : K →* B) (hk : IsPGroup 2 q.ker)
    (D : Subgroup B) [Group.IsPerfect D]
    (hD : D ≤ (M.subgroupOf K).map q) : primeRank 3 D ≤ 1 := by
  let N := M.subgroupOf K
  let R := (solvableResidual N).map N.subtype
  let A := R.map K.subtype
  have hr : R.map q = (solvableResidual (N.map q)).map (N.map q).subtype := by
    have hh := congrArg (Subgroup.map (N.map q).subtype)
      (map_solvableResidual_eq (q.subgroupMap N) (q.subgroupMap_surjective N))
    rw [map_map] at hh
    change (solvableResidual N).map (q.comp N.subtype) = _ at hh
    simpa only [R,map_map] using hh
  have hDR : D ≤ R.map q := hr.symm ▸ le_map_solvableResidual_of_isPerfect D (N.map q) hD
  let er := (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
  let ea := R.equivMapOfInjective K.subtype K.subtype_injective
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := er.toMonoidHom) er.surjective
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := ea.toMonoidHom) ea.surjective
  have hAM : A ≤ M := by
    have hh := map_mono (f := K.subtype) (map_subtype_le (solvableResidual N))
    exact hh.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  have hbound := source_perfect_threeRank_le_one hG T hempty hM hu hmany hcard e A hAM
  have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) q hk R
  calc
    primeRank 3 D ≤ primeRank 3 (R.map q) := primeRank_mono 3 hDR
    _ = primeRank 3 R := he
    _ = primeRank 3 A := primeRank_equiv 3 ea
    _ ≤ 1 := hbound

end CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
