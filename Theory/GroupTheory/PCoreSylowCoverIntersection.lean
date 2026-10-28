module
public import Theory.GroupTheory.SubgroupCoverTransport
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Intersecting Sylow covers through a two-group kernel

Let X be normal in G and surject onto D under a map with two-group kernel.
The image of a Sylow subgroup of X is a full Sylow subgroup of D. Subgroup
correspondence therefore shows that intersecting a Sylow cover of G with X
is a cover of the intersected Sylow subgroup. If X also contains O²(G),
this intersection preserves the literal embedded two-residual.

Source application: Aschbacher--Smith, 15.2.23(a), printed p.1117, passing
from XS to the original X in the minimal-parabolic construction.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- If a normal subgroup has the whole image through a two-group kernel,
intersection preserves covers of the prescribed Sylow subgroup. -/
theorem sylow_cover_inf_of_surjective_restriction
    (f : G →* D) (hk : IsPGroup 2 f.ker) (X : Subgroup G) [X.Normal]
    (hX : Function.Surjective (f.comp X.subtype)) (S : Sylow 2 G)
    (P : Subgroup G) (hP : (S : Subgroup G) ⋖ P) :
    (S : Subgroup G) ⊓ X ⋖ P ⊓ X := by
  let q := f.comp X.subtype
  have hf : Function.Surjective f := fun d => by
    obtain ⟨x,hx⟩ := hX d
    exact ⟨x,hx⟩
  have hker := hk.le_sylow_of_normal S
  obtain ⟨SX,hSX⟩ := S.exists_subgroupOf_eq_of_normal X
  have hSXmap : (SX : Subgroup X).map X.subtype = (S : Subgroup G) ⊓ X := by
    rw [hSX,subgroupOf_map_subtype]
  have hqker : IsPGroup 2 q.ker := hk.comap_of_injective X.subtype X.subtype_injective
  have hqSX := hqker.le_sylow_of_normal SX
  have hmaps : (SX : Subgroup X).map q = (S : Subgroup G).map f := by
    have hle : (SX : Subgroup X).map q ≤ (S : Subgroup G).map f := by
      rw [show q = f.comp X.subtype from rfl,←map_map,hSXmap]
      exact map_mono inf_le_left
    exact ((SX.mapSurjective hX).is_maximal' (S.isPGroup'.map f) hle).symm
  have hcov : (S : Subgroup G).map f ⋖ P.map f := by
    apply (comap_covBy_iff_of_surjective f hf _ _).mp
    rw [comap_map_eq_self hker,comap_map_eq_self (hker.trans hP.le)]
    exact hP
  have hQP : (P.subgroupOf X).map q = P.map f := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact mem_map_of_mem f hx
    · rintro y ⟨p,hp,rfl⟩
      obtain ⟨x,hx⟩ := hX (f p)
      have hxp : (x : G) ∈ P := by
        rw [←comap_map_eq_self (f := f) (hker.trans hP.le)]
        change f x ∈ P.map f
        rw [←show q x = f x from rfl,hx]
        exact mem_map_of_mem f hp
      exact ⟨x,hxp,hx⟩
  have hSXQ : (SX : Subgroup X) ≤ P.subgroupOf X := by
    rw [hSX]
    exact comap_mono hP.le
  have hcovX : (SX : Subgroup X) ⋖ P.subgroupOf X := by
    have hh := (comap_covBy_iff_of_surjective q hX _ _).mpr (hmaps.symm ▸ hcov)
    rw [←hQP,comap_map_eq_self hqSX,comap_map_eq_self (hqSX.trans hSXQ)] at hh
    exact hh
  have hh := (covBy_map_subtype_iff X _ _).mpr hcovX
  rwa [hSXmap,subgroupOf_map_subtype] at hh

/-- Intersecting with a subgroup containing the ambient two-residual
preserves the actual embedded two-residual of every subgroup. -/
theorem embedded_twoResidual_inf_eq_of_residual_le
    (X P : Subgroup G) (hX : pResidual 2 G ≤ X) :
    (pResidual 2 (P ⊓ X : Subgroup G)).map (P ⊓ X).subtype =
      (pResidual 2 P).map P.subtype := by
  let Y := (pResidual 2 P).map P.subtype
  have hYX : Y ≤ X := (map_pResidual_le 2 P.subtype).trans hX
  apply le_antisymm (embedded_pResidual_mono 2 inf_le_left)
  have hh := embedded_pResidual_mono 2 (le_inf (map_subtype_le (pResidual 2 P)) hYX)
  rw [(pResidual_eq_top_iff 2 Y).mpr (isPPerfect_embedded_pResidual 2 P),
    ←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

end Subgroup
