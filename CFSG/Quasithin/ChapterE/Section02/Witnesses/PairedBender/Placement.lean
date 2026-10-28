module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents

/-!
# The actual Borel intersections in paired rank-one components

The Sylow normalizer of a rank-one component is a proper nontrivial seed
invariant under the Sylow stabilizer of that component. The component-seed
theorem puts it in the original unique maximal overgroup. Rank-one Sylow
maximality then identifies the whole intersection. The source consumer uses
the original paired-component reduction and retains its multiplication map.

Source: Aschbacher–Smith E.2.7, printed pp.218–219, paired Bender branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {H : Type*} [Group H] [Finite H]

theorem component_borel_intersection (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H)
    (hK : IsComponent H K) [IsSimpleGroup K] (heven : 2 ∣ Nat.card K)
    (ho : componentOrbit K (T : Subgroup H) = pResidual 2 H)
    (hm : ChapterF.Source.IsRankOneModel K) :
    (ChapterB.minimalParabolicMax T hP).subgroupOf K =
      normalizer ((T : Subgroup H).subgroupOf K : Set K) := by
  let M := ChapterB.minimalParabolicMax T hP
  let B := ChapterF.Source.borel K (T : Subgroup H)
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup H) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have hf := ChapterF.Source.rankOneBorelFacts_of_sylow K (T : Subgroup H)
    S hSm (hm.rankOneSylowFacts S)
  have hSB : (T : Subgroup H) ⊓ K ≤ B :=
    le_inf inf_le_right ((T : Subgroup H) ⊓ K).le_normalizer
  have hb : B ≠ ⊥ := by
    intro hb
    apply component_sylow_intersection_ne_bot T hK heven
    have hz : (T : Subgroup H) ⊓ K = ⊥ := le_bot_iff.mp (hb ▸ hSB)
    apply map_injective K.subtype_injective
    rw [subgroupOf_map_subtype,hz,Subgroup.map_bot]
  have hinv : (T : Subgroup H) ⊓ normalizer (K : Set H) ≤ normalizer (B : Set H) := by
    have hn : (T : Subgroup H) ⊓ normalizer (K : Set H) ≤
        normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) :=
      (inf_le_inf (T : Subgroup H).le_normalizer le_rfl).trans inf_normalizer_le_normalizer_inf
    exact (le_inf inf_le_right (hn.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hBM : B ≤ M := ChapterB.component_seed_le_minimalParabolicMax T hP hK
    (show B ≤ K from inf_le_left) hb hf.proper.ne hinv
  have hMK : M ⊓ K < K := lt_of_le_of_ne inf_le_right (by
    intro he
    exact ChapterB.component_not_le_minimalParabolicMax T hP ho
      (he ▸ inf_le_left))
  have he : M ⊓ K = B := le_antisymm
    (hf.unique_maximal _ (inf_le_inf (ChapterB.minimalParabolicMax_spec T hP).2 le_rfl) hMK)
    (le_inf hBM inf_le_left)
  have hh := congrArg (fun A : Subgroup H => A.subgroupOf K) he
  change (M ⊓ K).subgroupOf K =
    (K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)).subgroupOf K at hh
  rw [inf_subgroupOf_right,inf_subgroupOf_left,
    subgroupOf_normalizer_eq inf_le_right,inf_subgroupOf_right] at hh
  exact hh

/-- The original paired source supplies both the product coordinates and
its first Borel marking, without a Borel or automizer conclusion as input. -/
theorem source_pair_borel_coordinates (hH : IsStronglyQuasithin H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (heven : 2 ∣ Nat.card K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    (hm : ChapterF.Source.IsRankOneModel K) :
    ∃ t : T, let D := K.map (MulAut.conj (t:H)).toMonoidHom
      D ≠ K ∧ IsSimpleGroup D ∧ IsComponent H D ∧
      pResidual 2 H = K ⊔ D ∧
      (∃ e : K × D ≃* (K ⊔ D : Subgroup H),
        ∀ k d, (e (k,d) : H) = (k:H)*(d:H)) ∧
      D.map (MulAut.conj (t:H)).toMonoidHom = K ∧
      (∀ p : ℕ, p.Prime → Odd p → primeRank p K ≤ 1) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K =
        normalizer ((T : Subgroup H).subgroupOf K : Set K) := by
  obtain ⟨t,ht,hd,hD,hR,e,hD',hr⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hC hgen hn
  exact ⟨t,ht,hd,hD,hR,e,hD',hr,component_borel_intersection T hP K hK heven
    (Structure.generating_component_orbit_eq_residual hH T hK hgen) hm⟩

end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
