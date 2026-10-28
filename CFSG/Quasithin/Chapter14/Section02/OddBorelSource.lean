module
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic

/-!
# The original odd Borel actors in 14.2.11

The plane source identifies M intersection Mc as C_M(V) times its
two-core. Its image on V is therefore a two-group. Every odd-order
subgroup of this intersection acts trivially on V. Since Y is the
original normal residual in M, the same subgroup normalizes Y.

Apply this to each actual odd Borel subgroup B contained in H intersection
M. Source 14.2.3 puts H in Mc, so no centralizer or normalization input
is added. In particular the result applies to every Hall odd subgroup of
the source's K intersection M, independently of the choice of K₁.

Source: Aschbacher--Smith 14.2.11, printed p.983, using 14.2.2(1).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_odd_intersection_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (B : Subgroup G) (hB : B ≤ M ⊓ Mc) (ho : Odd (Nat.card B)) :
    B ≤ M ⊓ centralizer (localModule T M : Set G) ∧
      B ≤ normalizer (sourceResidual M Mc : Set G) := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let q := QuotientGroup.mk' C
  let I := M ⊓ Mc
  let R := I.pCoreIn 2
  have hRM : R ≤ M := (pCoreIn_le 2 I).trans inf_le_left
  have hBM : B ≤ M := hB.trans inf_le_left
  obtain ⟨_,_,hI,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hi : (I.subgroupOf M).map q = (R.subgroupOf M).map q := by
    change ((M ⊓ Mc).subgroupOf M).map q = _
    rw [hI,subgroupOf_sup inf_le_left hRM,inf_subgroupOf_left,Subgroup.map_sup]
    change C.map q ⊔ (R.subgroupOf M).map q = _
    rw [QuotientGroup.map_mk'_self,bot_sup_eq]
  have hp : IsPGroup 2 ((I.subgroupOf M).map q) := by
    rw [hi]
    exact (isPGroup_pCoreIn 2 I).comap_subtype.map q
  have hb : (B.subgroupOf M).map q = ⊥ := by
    have hpB := hp.to_le (map_mono (f := q) (comap_mono hB))
    have hob : Odd (Nat.card (B.subgroupOf M)) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    have hobq := hob.of_dvd_nat (card_map_dvd (B.subgroupOf M) q)
    rcases hpB.card_eq_or_dvd with hc | hc
    · exact Subgroup.card_eq_one.mp hc
    · exact (hobq.not_two_dvd_nat hc).elim
  have hBC : B.subgroupOf M ≤ C := by
    simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hb
  refine ⟨le_inf hBM (fun b hb => hBC (show (⟨b,hBM hb⟩ : M) ∈ B.subgroupOf M from hb)),?_⟩
  exact hBM.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp
    (residualY_normal M Mc))

/-- The centralization and Y-normalization clauses for the literal odd Borel actor. -/
theorem source_lemma_14_2_11_odd_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (B : Subgroup G) (hB : B ≤ H ⊓ M) (ho : Odd (Nat.card B)) :
    B ≤ M ⊓ centralizer (localModule T M : Set G) ∧
      B ≤ normalizer (sourceResidual M Mc : Set G) := by
  have hHMc : H ≤ Mc := by
    have huH := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from huH.symm ▸ Set.mem_singleton Mc).2
  exact source_odd_intersection_centralizes hG T hempty hM hu hmany hcard e B
    (le_inf (hB.trans inf_le_right) ((hB.trans inf_le_left).trans hHMc)) ho
end CFSG.Quasithin.Chapter14.Section02
