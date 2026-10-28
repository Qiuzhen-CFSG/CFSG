module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingSupport
public import Theory.GroupAction.OmegaCenterFixedProduct
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.SylowKernelCore

/-!
# The block Sylow factors lie in the transvection subgroup

The source direct factorization Q = U × D, with S-normal factors, splits
its omega-center into the S-fixed parts of U and D. A two-group acting on
the four-element fixed plane of U has fixed index at most two. Since the
block centralizes D, the same index bound holds on the full omega-center.
Consequently R ∩ K is contained in the source transvection subgroup R⁺.

Source: Aschbacher–Smith, proof of C.5.6, printed p.157.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]
private theorem centralizer_index_four (A F : Subgroup G) (hA : IsPGroup 2 A)
    (hAF : A ≤ normalizer (F : Set G)) (hcard : Nat.card F = 4) :
    (centralizer (A : Set G)).relIndex F ≤ 2 := by
  have hm := card_modEq_card_inf_centralizer A F hA hAF
  have hp : 0 < Nat.card (F ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G)
    (F ⊓ centralizer (A : Set G)) F bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hcard] at hmul
  rw [hcard] at hm
  have he : 2 ≤ Nat.card (F ⊓ centralizer (A : Set G) : Subgroup G) := by
    have : Nat.card (F ⊓ centralizer (A : Set G) : Subgroup G) % 2 = 0 := by
      exact hm.symm.trans (by decide : Nat.ModEq 2 4 0)
    omega
  nlinarith

omit [Finite G] in
private theorem centralizer_index_join (F D C : Subgroup G)
    (hJ : IsMulCommutative (F ⊔ D : Subgroup G)) (hDC : D ≤ C) :
    C.relIndex (F ⊔ D) = C.relIndex F := by
  let J := F ⊔ D
  let := hJ
  let CJ := C.subgroupOf J
  let FJ := F.subgroupOf J
  have hsup : FJ ⊔ CJ = ⊤ := by
    have hj : (F ⊔ D).subgroupOf J = ⊤ := subgroupOf_self J
    rw [subgroupOf_sup le_sup_left le_sup_right] at hj
    apply top_unique
    rw [← hj]
    exact sup_le le_sup_left ((subgroupOf_mono J hDC).trans le_sup_right)
  have hh := relIndex_sup_right FJ CJ
  rw [hsup, relIndex_top_right] at hh
  exact hh.trans (relIndex_subgroupOf (show F ≤ J from le_sup_left))

theorem factor_le_transvectionRadical (R K U D : Subgroup G)
    (hR : IsPGroup 2 R)
    (hUS : U ≤ CFSG.Quasithin.ChapterB.baumann R)
    (hDS : D ≤ CFSG.Quasithin.ChapterB.baumann R)
    (hDK : D ≤ centralizer (K : Set G))
    (hUD : Disjoint U D) (hcomm : U ≤ centralizer (D : Set G))
    (hUn : CFSG.Quasithin.ChapterB.baumann R ≤ normalizer (U : Set G))
    (hDn : CFSG.Quasithin.ChapterB.baumann R ≤ normalizer (D : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hE : omegaOneCenterAmbient (CFSG.Quasithin.ChapterB.baumann R) ≤ U ⊔ D)
    (hfixed : Nat.card (U ⊓ centralizer (CFSG.Quasithin.ChapterB.baumann R : Set G) : Subgroup G) = 4) :
    R ⊓ K ≤ transvectionRadical R := by
  let S := CFSG.Quasithin.ChapterB.baumann R
  let F := U ⊓ centralizer (S : Set G)
  let C := D ⊓ centralizer (S : Set G)
  let A := R ⊓ K
  have hnormS : R ≤ normalizer (S : Set G) :=
    R.le_normalizer.trans (normalizer_le_normalizer_baumann R)
  have hnormC : A ≤ normalizer (centralizer (S : Set G) : Set G) :=
    (inf_le_left.trans hnormS).trans (by
      exact (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (S : Set G))).mp inferInstance)
  have hnormF : A ≤ normalizer (F : Set G) :=
    (le_inf (inf_le_right.trans hKU) hnormC).trans inf_normalizer_le_normalizer_inf
  have hFC : F ≤ centralizer (C : Set G) :=
    inf_le_left.trans (hcomm.trans (centralizer_le inf_le_left))
  have hJleS : F ⊔ C ≤ S := sup_le (inf_le_left.trans hUS) (inf_le_left.trans hDS)
  have hJleC : F ⊔ C ≤ centralizer (S : Set G) := sup_le inf_le_right inf_le_right
  have hJF : IsMulCommutative (F ⊔ C : Subgroup G) := by
    apply le_centralizer_iff_isMulCommutative.mp
    exact hJleC.trans (centralizer_le hJleS)
  have hidx := centralizer_index_four A F (hR.to_le inf_le_left) hnormF hfixed
  have hspan := omegaOneCenterAmbient_le_fixed_factors S U D hUS hDS hUD hUn hDn hcomm hE
  intro r hr
  apply mem_transvectionGenerated hr.1
  have hCF : (centralizer ({r} : Set G)).relIndex F ≤ 2 := by
    apply le_trans ?_ hidx
    exact relIndex_le_of_le_left (centralizer_le (Set.singleton_subset_iff.mpr hr)) index_ne_zero_of_finite
  have hCr : C ≤ centralizer ({r} : Set G) :=
    inf_le_left.trans (hDK.trans (centralizer_le (Set.singleton_subset_iff.mpr hr.2)))
  exact (relIndex_le_of_le_right hspan index_ne_zero_of_finite).trans
    ((centralizer_index_join F C (centralizer ({r} : Set G)) hJF hCr).le.trans hCF)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup Stellmacher BinaryPermutation
variable {G : Type*} [Group G] [Finite G]

/-- C.5.4(3), on the original A₅ block and S-action, supplies the source
inclusion R ∩ K₁ ≤ R⁺. No part of C.5.6 is assumed. -/
public theorem alternating_blockSylow_le_transvectionRadical
    (R K : Subgroup G) (hR : IsPGroup 2 R) (hK : IsAlternatingBlock K 5)
    (hSK : ChapterB.baumann R ≤ normalizer (K : Set G))
    (hUS : sourceModule K ≤ ChapterB.baumann R)
    (hcore : (K ⊔ ChapterB.baumann R).pCoreIn 2 =
      ChapterB.baumann R ⊓ centralizer (sourceModule K : Set G))
    (hprod : (K ⊔ ChapterB.baumann R).pCoreIn 2 =
      sourceModule K ⊔ (ChapterB.baumann R ⊓ centralizer (K : Set G)))
    (a : ChapterB.baumann R →* Equiv.Perm (Fin 5))
    (e : sourceModule K ≃* Multiplicative (core (Fin 5)))
    (himage : a.range = ChapterB.Offenders.D 5)
    (he : ∀ (s : ChapterB.baumann R) (u : sourceModule K),
      (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 5) (a s) (e u).toAdd)) : G) =
        (s : G) * (u : G) * (s : G)⁻¹) :
    R ⊓ K ≤ transvectionRadical R := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let D := S ⊓ centralizer (K : Set G)
  have hUD : Disjoint U D := alternatingModule_disjoint_of_commuting K D hK inf_le_right
  have hnorm : normalizer (K : Set G) ≤ normalizer (U : Set G) :=
    normalizer_le_normalizer_characteristic_image K (blockU K)
  have hSD : S ≤ normalizer (D : Set G) :=
    (le_inf S.le_normalizer
      (hSK.trans ((normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance))).trans
      inf_normalizer_le_normalizer_inf
  have hE : omegaOneCenterAmbient S ≤ U ⊔ D := by
    rw [← hprod, hcore]
    intro z hz
    obtain ⟨hzS, _, hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact ⟨hzS, fun u hu => hzC u (hUS hu)⟩
  exact factor_le_transvectionRadical R K U D hR hUS inf_le_left inf_le_right hUD
    ((le_centralizer_iff.mp (show D ≤ centralizer (U : Set G) from
      inf_le_right.trans (centralizer_le (map_subtype_le _)))))
    (hSK.trans hnorm) hSD (K.le_normalizer.trans hnorm) hE
    (marked_fixed_plane_card S U a e himage he)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
