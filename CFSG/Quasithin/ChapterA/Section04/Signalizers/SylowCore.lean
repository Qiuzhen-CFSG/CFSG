module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The two-core obtained from a Sylow subgroup of the normalizer

Intersect a Sylow subgroup of N_M(X) with the normal section centralizer.
This intersection is a maximal signalizer by A.4.2(4), and is normal in XT.
The two-core of XT is itself a signalizer, so maximality identifies the two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.2(5), printed p. 57.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_intersection (N C : Subgroup G) (hCN : C ≤ N)
    (hNC : N ≤ normalizer (C : Set G)) (T : Sylow 2 N) :
    ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype =
      (T : Subgroup N).map N.subtype ⊓ C := by
  let : (C.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNC
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal (C.subgroupOf N)
  let e := subgroupOfEquivOfLe hCN
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup (C.subgroupOf N)).map e.toMonoidHom).map C.subtype = _
  ext g
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨⟨s.val, by rwa [hS] at hs, rfl⟩, (e s).property⟩
  · rintro ⟨⟨n, hn, rfl⟩, hc⟩
    refine ⟨⟨n.val, hc⟩, ?_, rfl⟩
    exact ⟨⟨n, hc⟩, by rw [hS]; exact hn, rfl⟩

/-- A.4.2(5): the two-core of XT is a maximal signalizer. -/
theorem sylow_normalizer_core_isMaximal (X M : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hX : IsPPerfect 2 X)
    (T : Sylow 2 ↥(M ⊓ normalizer (X : Set G))) :
    IsMaximalTwoSignalizer X M
      ((X ⊔ (T : Subgroup ↥(M ⊓ normalizer (X : Set G))).map
        (M ⊓ normalizer (X : Set G)).subtype).pCoreIn 2) := by
  let N := M ⊓ normalizer (X : Set G)
  let U := (T : Subgroup N).map N.subtype
  let C := twoSectionCentralizer X M
  have hUN : U ≤ N := map_subtype_le _
  have hUM : U ≤ M := hUN.trans inf_le_left
  obtain ⟨S, hS⟩ := sylow_intersection N C
    (le_inf (twoSectionCentralizer_le X M) (twoSectionCentralizer_le_normalizer X M))
    (normalizer_twoSectionCentralizer X M) T
  have hmax : IsMaximalTwoSignalizer X M (U ⊓ C) :=
    (maximal_signalizer_iff_sylow X M _ hXM hsub hX).mpr ⟨S, hS⟩
  have hs := ((isMaximalTwoSignalizer_iff _ _ _).mp hmax).1
  have hU : U ≤ normalizer (U ⊓ C : Set G) :=
    (le_inf le_normalizer (hUN.trans (normalizer_twoSectionCentralizer X M))).trans
      inf_normalizer_le_normalizer_inf
  have hcore : U ⊓ C ≤ (X ⊔ U).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hs.isPGroup (inf_le_left.trans le_sup_right)
      (sup_le hs.normalizes hU)
  have hsig : IsTwoSignalizer X M ((X ⊔ U).pCoreIn 2) := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    exact ⟨(pCoreIn_le _ _).trans (sup_le hXM hUM), isPGroup_pCoreIn _ _,
      le_sup_left.trans (le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))⟩
  have he : (X ⊔ U).pCoreIn 2 = U ⊓ C := le_antisymm
    (((isMaximalTwoSignalizer_iff _ _ _).mp hmax).2 _ hsig hcore) hcore
  change IsMaximalTwoSignalizer X M ((X ⊔ U).pCoreIn 2)
  rwa [he]
end CFSG.Quasithin.ChapterA.Section04

end
