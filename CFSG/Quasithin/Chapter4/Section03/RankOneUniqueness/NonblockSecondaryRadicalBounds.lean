module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreComplete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverage
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# The original secondary radical: center and two-core bounds

The original point-radical image fixes exactly the source root in U=Z(Q).
Whole-radical coverage shows that R₂ centralizes this root. An element of
Z(R₂) centralizes U, so the faithful natural-action kernel puts it in Q;
centralizing Q then puts it in U. Thus Z(R₂)=Z_S, with the literal ambient
center map. Every normalizer of R₂ consequently preserves Z_S, and its
intersection with H normalizes the original secondary residual K₂.

If N_G(R₂)≤H, the given Sylow S of H remains Sylow in every intermediate
normalizer containing K₂S. The Sylow-core theorem proves radicality there;
radical saturation then puts the two-core of every overgroup of K₂S in R₂.
In particular this proves O₂(K_Z T)≤R₂ from the preceding containment,
without assuming SecondarySourceData or its enlarged-core field.

NonblockSecondaryRadicalApplications uses these results in the actual
source constructor and linear-four reduction. Normalizer containment in H,
strict enlargement of K₂ by O₂(K_Z), the original MS witness and terminal
representation contradiction remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, original 4.3.14(1)--(3), pp.617--618,
and the radical saturation argument C.2.1, p.144.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
/-- Source 4.3.14(2): radicality in every overgroup of the original K₂S,
conditional on the preceding normalizer containment. -/
theorem radical_relative_core_of_normalizer_le
    (hN : normalizer (R₂ c : Set G) ≤ c.H)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) :
    (normalizer ((R₂ c).subgroupOf J : Set J)).pCoreIn 2 = (R₂ c).subgroupOf J := by
  let I := c.H ⊓ J
  have hsmall : secondary c ⊔ S c ≤ I :=
    le_inf (sup_le (secondary_le_original.trans (map_subtype_le _)) inf_le_right) hJ
  obtain ⟨P,hP⟩ := c.sylow
  obtain ⟨P',hP'⟩ := P.exists_map_subtype_eq_of_le (show I ≤ c.H from inf_le_left)
    (by rw [hP]; exact le_inf inf_le_right (le_sup_right.trans hJ))
  have he := pCoreIn_normalizer_eq_of_sylow_le P' hsmall
    (by rw [hP',hP]; exact le_sup_right)
  have hEq : I ⊓ normalizer (R₂ c : Set G) = J ⊓ normalizer (R₂ c : Set G) := by
    apply le_antisymm (inf_le_inf_right _ inf_le_right)
    exact le_inf (le_inf (inf_le_right.trans hN) inf_le_left) inf_le_right
  change (I ⊓ normalizer (R₂ c : Set G)).pCoreIn 2 = R₂ c at he
  rw [hEq] at he
  have hRJ : R₂ c ≤ J := (pCoreIn_le 2 _).trans hJ
  apply map_injective J.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
    ←subgroupOf_normalizer_eq hRJ,subgroupOf_map_subtype,inf_comm,he,
    map_subgroupOf_eq_of_le hRJ]

/-- The first bound of 4.3.14(3), for any overgroup of the same K₂S. -/
theorem enlarged_core_le_radical_of_normalizer_le
    (hN : normalizer (R₂ c : Set G) ≤ c.H)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) : J.pCoreIn 2 ≤ R₂ c := by
  have hh := pCore_le_of_pCore_normalizer_le ((R₂ c).subgroupOf J)
    (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype
    (radical_relative_core_of_normalizer_le hN J hJ).le
  have hm := map_mono (f := J.subtype) hh
  rwa [map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hJ)] at hm

namespace RootCoordinates
variable {n : ℕ} {d : MSData c n} (m : RootCoordinates d)
include m

/-- The actual radical centralizes the original root, by whole-radical coverage. -/
theorem radical_centralizes_root {V : Subgroup G} (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    R₂ c ≤ centralizer (root c : Set G) :=
  (m.radical_coverage hn D (d.joinCore_eq hn)).trans
    (sup_le d.core_centralizes_root ((pCoreIn_le 2 _).trans secondary_centralizes_root))

/-- The point-radical fixed line is the literal source root in U. -/
theorem center_fixed_by_radical {V : Subgroup G} (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    U c ⊓ centralizer (R₂ c : Set G) = root c := by
  apply le_antisymm
  · intro z hz
    let u : U c := ⟨z,hz.1⟩
    apply (m.root_coordinates u).mpr
    apply (Matrix.PSL3.LinearThree.pointRadicalSL_fixed_iff d.field.Carrier _).mp
    intro g hg
    have hg' : g ∈ (pCore 2 (secondary c)).map m.secondaryProjection := by
      rw [m.secondary_core_image hn,Matrix.PSL3.LinearThree.pointLocalSL_twoCore_eq]
      exact hg
    obtain ⟨k,hk,hkg⟩ := hg'
    have hkR : (k : G) ∈ R₂ c := secondary_core_le_radical D (mem_map_of_mem _ hk)
    have hc : (k : G) * z * (k : G)⁻¹ = z := by
      rw [mem_centralizer_iff.mp hz.2 _ hkR,mul_inv_cancel_right]
    have he := m.compatible ⟨k,secondary_le_original k.property⟩ u u hc.symm
    rw [←m.secondaryProjection_apply,hkg] at he
    exact he.symm
  · exact le_inf d.root_le_center (le_centralizer_iff.mp (m.radical_centralizes_root hn D))

/-- The intrinsic center of R₂ is exactly the original root, with its ambient map. -/
theorem radical_center_eq_root {V : Subgroup G} (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (center (R₂ c)).map (R₂ c).subtype = root c := by
  have hUQ : U c ≤ Q c := map_subtype_le _
  have hUR : U c ≤ R₂ c := hUQ.trans (core_le_radical c)
  apply le_antisymm
  · rintro z ⟨r,hr,rfl⟩
    have hc : (r : G) ∈ centralizer (R₂ c : Set G) := by
      intro x hx
      exact congrArg Subtype.val (mem_center_iff.mp hr ⟨x,hx⟩)
    have hQ : (r : G) ∈ Q c := by
      rw [←m.join_centralizer_center (d.joinCore_eq hn)]
      exact ⟨(radical_le_sylow c).trans le_sup_right r.property,
        centralizer_le hUR hc⟩
    have hU : (r : G) ∈ U c := by
      refine ⟨⟨r,hQ⟩,mem_center_iff.mpr ?_,rfl⟩
      intro q
      exact Subtype.ext (hc q ((core_le_radical c) q.property))
    exact (m.center_fixed_by_radical hn D).le ⟨hU,hc⟩
  · intro z hz
    have hzR := hUR (d.root_le_center hz)
    refine ⟨⟨z,hzR⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    have hc := (m.center_fixed_by_radical hn D).ge hz |>.2
    exact Subtype.ext (hc r r.property)

/-- Every normalizer of the radical preserves the same original root. -/
theorem radical_normalizer_le_rootNormalizer {V : Subgroup G} (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    normalizer (R₂ c : Set G) ≤ rootNormalizer c := by
  rw [rootNormalizer,←m.radical_center_eq_root hn D]
  exact normalizer_le_normalizer_characteristic_image (R₂ c) (center (R₂ c))

/-- Within H, radical normalization already forces normalization of K₂. -/
theorem radical_normalizer_control {V : Subgroup G} (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hN : normalizer (R₂ c : Set G) ≤ c.H) :
    normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G) :=
  le_inf hN ((le_inf hN (m.radical_normalizer_le_rootNormalizer hn D)).trans
    original_root_normalizer_normalizes_secondary)
end RootCoordinates

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
