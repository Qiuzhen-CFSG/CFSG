module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.CentralThompson
public import Theory.GroupTheory.ElementaryThompsonFrattini.UniqueMaximal
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source

/-!
# The actual outside Thompson group in the initial E reduction

Frattini generation takes place in the original outside local H. The
selected Sylow subgroup is the restriction of the ambient T, so its
Thompson subgroup maps to J(T). In the contrary central-Thompson branch,
the global ambient normalizer lies in M; hence J(H) cannot also lie in M.
This supplies the noncontainment used to place the alternating cubic
residual from solvable Thompson factorization.

Source: the argument of 14.1.4, p.976, specialized after source 15.4.8.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The Frattini factorization retains the ambient T and the intrinsic global J(H). -/
theorem local_thompson_generation (T : Sylow 2 G) (H M : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hN : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    (hJ : (elementaryAbelianMaxJ (⊤ : Subgroup H)).map H.subtype ≤ M) : H ≤ M := by
  have hlocal : (normalizer (elementaryAbelianMaxJ (T.subtype hTH : Subgroup H) : Set H)).map
      H.subtype ≤ M := by
    apply le_trans ((elementaryAbelianMaxJ (T.subtype hTH : Subgroup H)).le_normalizer_map H.subtype)
    rw [← elementaryAbelianMaxJ_map_injective _ H.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
    exact hN
  have hgen := congrArg (Subgroup.map H.subtype)
    (elementaryAbelianMaxJ_frattini (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hgen
  exact hgen ▸ sup_le hlocal hJ

/-- The actual global Thompson subgroup of an outside local escapes M. -/
theorem outside_global_thompson_not_le_of_central {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M H : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ (elementaryAbelianMaxJ (⊤ : Subgroup H)).map H.subtype ≤ M := by
  intro hj
  exact hH.1.2 (local_thompson_generation T H M hH.1.1.2
    (normalizer_thompson_le_of_central hG T M hM hTM hC hcentral) hj)

section Intrinsic
open Chapter1.RadicalNormalizers.ThompsonSource

omit [Finite G] in
/-- The exceptional action makes the original Thompson normalizer proper. -/
theorem exceptional_thompson_normalizer_ne_top (S : Sylow 2 G)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure S)]
    (d : Exceptional S)
    (hker : centralizer (Chapter1.RadicalNormalizers.ThompsonSource.closure S : Set G) =
      pCore 2 G) :
    normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ≠ ⊤ := by
  intro hn
  let : (elementaryAbelianMaxJ (S : Subgroup G)).Normal := normalizer_eq_top_iff.mp hn
  have hJS : elementaryAbelianMaxJ (S : Subgroup G) ≤ (S : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hJC : elementaryAbelianMaxJ (S : Subgroup G) ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, S.isPGroup'.to_le hJS⟩
  apply d.noncentral
  rwa [hker]

/-- Covering the actual global Thompson image by the cubic residual and S
forces XS=H in the minimal-parabolic application. The two-core kernel is
contained in S and no generation conclusion is assumed. -/
theorem exceptional_sup_sylow_eq_top (S : Sylow 2 G)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure S)]
    (d : Exceptional S)
    (hker : centralizer (Chapter1.RadicalNormalizers.ThompsonSource.closure S : Set G) =
      pCore 2 G)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (X : Subgroup G)
    (hcover : (elementaryAbelianMaxJ (⊤ : Subgroup G)).map
        (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)) ≤
      X.map (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)) ⊔
        (S : Subgroup G).map (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S))) :
    X ⊔ (S : Subgroup G) = ⊤ := by
  apply sup_sylow_eq_top_of_global_thompson_le S hunique
    (exceptional_thompson_normalizer_ne_top S d hker) X
  rw [← Subgroup.map_sup] at hcover
  have hpre := Subgroup.map_le_iff_le_comap.mp hcover
  rw [comap_map_eq, starMap, QuotientGroup.ker_mk', hker,
    sup_eq_left.mpr ((pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right)] at hpre
  exact hpre

end Intrinsic
end CFSG.Quasithin.Chapter15.Section04.InitialSource
