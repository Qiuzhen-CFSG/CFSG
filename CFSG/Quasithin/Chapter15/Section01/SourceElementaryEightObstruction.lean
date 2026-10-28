module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.ElementaryEightPlanePointFullImage
public import Theory.GroupTheory.ElementaryEightSylowCenterSpan

/-!
# The source obstruction to incompatible elementary-eight parabolics

Under the original empty faithful-local-component hypothesis, an elementary
eight normalized by T cannot have both a plane S4 and a point S4 in its
actual normalizer image. Those actors force the full automizer. Its
transitivity puts E in the local module of N_G(E), so 14.1.6 makes this
same action image solvable, contradicting the PSL3(2) quotient.

This uses the ambient source hypothesis in the exceptional Omega extension
of 15.1.11. It does not infer Thompson movement from a bare S4 product.
Source: Aschbacher--Smith 14.1.6(1), printed p.977, and 15.1.11, p.1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03
variable {G : Type*} [Group G] [Finite G]

theorem source_elementaryEight_plane_point_impossible (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hET : E ≤ T) (hTN : (T : Subgroup G) ≤ normalizer (E : Set G))
    (plane : ElementaryEightPlaneImage E) (point : ElementaryEightPointImage E) : False := by
  have hne : E ≠ ⊥ := by
    intro h
    have he := hE
    rw [h, Subgroup.card_bot] at he
    omega
  have hH : normalizer (E : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨E,hne,IsElementaryAbelian.isPGroup 2 E,rfl⟩,hTN⟩
  have hEL := elementaryEight_le_sylowCenter_normalizer_span T E hE hET hTN (elementaryEight_normalizerMonoidHom_surjective_of_plane_point E hE plane point)
  have hr := InitialSource.residual_le_centralizer_localModule
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hH
  have hk : solvableResidual (normalizer (E : Set G)) ≤ E.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact fun _ hx => centralizer_le hEL (hr (mem_map_of_mem _ hx))
  have hz : solvableResidual E.normalizerMonoidHom.range = ⊥ := by
    rw [← map_solvableResidual_eq E.normalizerMonoidHom.rangeRestrict
      E.normalizerMonoidHom.rangeRestrict_surjective]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := E.normalizerMonoidHom.range)
  exact elementaryEight_normalizerImage_not_isSolvable_of_plane_point E hE plane point ⟨n,hn.trans hz⟩

end CFSG.Quasithin.Chapter15.Section01
