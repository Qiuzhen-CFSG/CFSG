module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Generation by the reselected minimal-parabolic pair

A pair I outside the unique maximal overgroup of T in H generates H with T:
a proper join would lie in that same maximal subgroup. The Sylow image is
retained explicitly, so the resulting equality is in the original ambient group.

Source: Aschbacher–Smith, §8.2 and Lemma 8.2.7, printed pp.714, 718
(PDF pp.731, 735), using the minimal-parabolic property B.6.1.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
variable {G : Type*} [Group G] [Finite G]

/-- A source pair outside the unique maximal overgroup generates H with T. -/
theorem pair_sup_of_minimalParabolic (I T H : Subgroup G) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver S ⊤) (hIH : I ≤ H)
    (hout : ¬ I.subgroupOf H ≤ ChapterB.minimalParabolicMax S hmin) :
    I ⊔ T = H := by
  have hg : I.subgroupOf H ⊔ (S : Subgroup H) = ⊤ := by
    rcases eq_top_or_exists_le_coatom (I.subgroupOf H ⊔ (S : Subgroup H)) with he | ⟨J, hJ, hle⟩
    · exact he
    · have he := ChapterB.minimalParabolicMax_unique S hmin hJ (le_sup_right.trans hle)
      exact (hout (he ▸ le_sup_left.trans hle)).elim
  have hm := congrArg (Subgroup.map H.subtype) hg
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hIH, hS,
    ← MonoidHom.range_eq_map, H.range_subtype] using hm
/-- The proper conjugate intersection in 8.2.2(3), together with its
normalizer identity (4), places the pair outside the maximal overgroup. -/
theorem pair_sup_of_source_intersection (I T H M U V : Subgroup G) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver S ⊤) (hIH : I ≤ H)
    (hmax : M.subgroupOf H = ChapterB.minimalParabolicMax S hmin)
    (hMI : I ⊓ M = I ⊓ normalizer (V : Set G))
    (g : G) (hg : g ∈ I)
    (hU : V ⊓ V.map (MulAut.conj g⁻¹).toMonoidHom = U) (hUV : U < V) :
    I ⊔ T = H := by
  apply pair_sup_of_minimalParabolic I T H S hS hmin hIH
  intro hi
  have hIM : I ≤ M := by
    intro i hiI
    have hm := hi (show (⟨i, hIH hiI⟩ : H) ∈ I.subgroupOf H from hiI)
    rw [← hmax] at hm
    exact hm
  have hgN : g ∈ normalizer (V : Set G) := by
    have hh : g ∈ I ⊓ M := ⟨hg, hIM hg⟩
    rw [hMI] at hh
    exact hh.2
  have he := mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem hgN)
  have he' : V.map (MulAut.conj g⁻¹).toMonoidHom = V := he
  rw [he', inf_idem] at hU
  exact hUV.ne hU.symm

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
