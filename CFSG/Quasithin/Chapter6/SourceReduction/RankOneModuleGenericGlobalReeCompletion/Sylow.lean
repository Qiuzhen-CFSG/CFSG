module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Centers
public import Theory.SpecificGroups.Suzuki.SylowSupplement
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import FeitThompson.FinalTheorem

/-!
# The full original Sylow and the Ree long-root centralizer invariant

The Suzuki quotient of the whole residual has odd outer automorphism group.
Its original Sylow supplement is consequently the product of the residual
intersection and the enlarged two-core. The already proved core identity
puts both factors in the residual. The common-Sylow comparison then gives
S = T in both original factors and H = O²(H).

Each factor is perfect and contains an ambient Sylow, so its quotient in
its full normalizer has odd order and is solvable. Thus the two factors are
exactly the solvable residuals of their full normalizers. The long-root
centralizer bound now puts the solvable residual of that full ambient
centralizer inside the Suzuki factor, whose order is prime to three.
This is the long-root invariant used to exclude fusion in F.4.35.

Both compatible comparison orientations and every positive Ree parameter
are retained. The simultaneous native normalizer extension, short-root
centralizer control and full-extension order comparison remain separate
obligations; no native realization or ambient generation is assumed here.
Source: Aschbacher–Smith 5.3.1–3 and F.4.35,38, printed pp.658–659,
292,294 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]

/-- The common parabolic Sylow is the entire original ambient Sylow. -/
theorem Preparation.ree_full_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    sourceS L H = (T : Subgroup G) ∧
      (T : Subgroup G) ≤ L ∧ (T : Subgroup G) ≤ residual H ∧ residual H = H := by
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  have hK := d.ree_right_maximal h hH hp m (Or.inr ⟨e⟩)
  obtain ⟨_,hm,_,_,⟨a⟩,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  have hcore := (d.ree_overcomponent_core_le h hH.1.1.2 hp m e hK.1 le_rfl).1
  have hfact := BenderSuzuki.MatrixGroups.suzuki_quotient_sylow_factorization
    (residual H) T (hH.1.1.2.trans (le_normalizer_residual H)) hm a
  rw [residual_sup_sylow T H hH.1.1.2,hcore] at hfact
  have hTK : (T : Subgroup G) ≤ residual H := by
    rw [hfact]
    exact sup_le (pCoreIn_le 2 _) inf_le_right
  have hcommon := d.common_sylow_of_comparison h hH.1.1.2 hp (.ree m (Or.inr ⟨e⟩))
  rw [inf_eq_left.mpr hTK] at hcommon
  have hTL : (T : Subgroup G) ≤ L := by
    rw [←hcommon]
    exact inf_le_right
  have hS : sourceS L H = (T : Subgroup G) := by
    apply le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    rw [←inf_eq_left.mpr hTL,←d.left_intersection]
    exact inf_le_left
  exact ⟨hS,hTL,hTK,(sup_eq_left.mpr hTK).symm.trans
    (residual_sup_sylow T H hH.1.1.2)⟩

private theorem normalizer_residual_of_sylow
    (T : Sylow 2 G) (K : Subgroup G) [Group.IsPerfect K]
    (hTK : (T : Subgroup G) ≤ K) :
    (solvableResidual (normalizer (K : Set G))).map
      (normalizer (K : Set G)).subtype = K := by
  let N := normalizer (K : Set G)
  let D := K.subgroupOf N
  let : D.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (K : Set G) from le_rfl)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe K.le_normalizer).symm.toMonoidHom)
    (subgroupOfEquivOfLe K.le_normalizer).symm.surjective
  let S := T.subtype (hTK.trans K.le_normalizer)
  have hSD : (S : Subgroup N) ≤ D := fun _ hx => hTK hx
  have hodd : Odd (Nat.card (N ⧸ D)) := by
    change Odd D.index
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSD)))
  let : Group.IsSolvable (N ⧸ D) := odd_order_theorem _ hodd
  have hr : solvableResidual N = D := le_antisymm
    (solvableResidual_le_of_solvable_quotient D) (le_solvableResidual_of_isPerfect D)
  rw [hr,map_subgroupOf_eq_of_le K.le_normalizer]

/-- The original factors are the exact solvable residuals of their full normalizers. -/
theorem Preparation.ree_normalizer_residuals
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∀ i : Fin 2, (solvableResidual (normalizer (![L,residual H] i : Set G))).map
      (normalizer (![L,residual H] i : Set G)).subtype = ![L,residual H] i := by
  obtain ⟨_,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.local_mem.1.1
  let := hp
  intro i
  fin_cases i
  · exact normalizer_residual_of_sylow T L hTL
  · exact normalizer_residual_of_sylow T (residual H) hTK

/-- The full ambient long-root centralizer has three-free solvable residual. -/
theorem Preparation.ree_long_centralizer_residual_three_free
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z = 2) :
    ¬ 3 ∣ Nat.card (solvableResidual (centralizer ({z} : Set G))) := by
  have hC := d.ree_central_involution_centralizers h hH hp m he 1 z hz hz2
  change centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) at hC
  have hN := d.ree_normalizer_residuals h hH hp m he 1
  change (solvableResidual (normalizer (residual H : Set G))).map
    (normalizer (residual H : Set G)).subtype = residual H at hN
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨_,hm,_,_,⟨a⟩,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  have hk := BenderSuzuki.MatrixGroups.three_free_of_suzuki_core_quotient m hm a
  let C := centralizer ({z} : Set G)
  let N := normalizer (residual H : Set G)
  have hle : (solvableResidual C).map C.subtype ≤ residual H := by
    rw [←hN]
    have hmap : ((solvableResidual C).map (inclusion hC)).map N.subtype ≤
        (solvableResidual N).map N.subtype :=
      map_mono (map_solvableResidual_le (inclusion hC))
    rw [Subgroup.map_map] at hmap
    exact hmap
  let f : solvableResidual C →* residual H :=
    (C.subtype.comp (solvableResidual C).subtype).codRestrict (residual H)
      (fun x => hle (mem_map_of_mem C.subtype x.property))
  have hf : Function.Injective f := by
    intro x y heq
    exact Subtype.ext (Subtype.ext (congrArg (fun x : residual H => (x : G)) heq))
  exact fun hd => hk (hd.trans (card_dvd_of_injective f hf))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

