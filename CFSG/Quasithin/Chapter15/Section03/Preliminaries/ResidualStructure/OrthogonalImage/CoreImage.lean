module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport

/-!
# The actual intersection-core image in the orthogonal action

The two-core of the intersection lies in the common Sylow two-subgroup and
is normalized by it. These properties survive restriction to `M` and the
actual natural-action map. The kernel calculation converts 14.1.17(1) into
nontriviality of this image, without an order-four hypothesis.

Source: Aschbacher–Smith, Lemma 15.3.7, printed p.1122 (PDF p.1139).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

/-- The literal action image of `O₂(M ∩ Mc)`. -/
@[expose] public def NaturalOrthogonalAction.intersectionCoreImage
    {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (Mc : Subgroup G) :
    Subgroup OrthogonalActor :=
  (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map d.actor

omit [Finite G] in
/-- The intersection core is contained in the common Sylow subgroup. -/
public theorem intersectionCore_le_sylow (M Mc : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc) :
    (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
  have h := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
  rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] at h

/-- Containment uses the source core, not an arbitrary chosen two-subgroup. -/
public theorem NaturalOrthogonalAction.intersectionCoreImage_le_sylowImage
    {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (Mc : Subgroup G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc) :
    d.intersectionCoreImage Mc ≤ (d.sylowImage T hTM : Subgroup OrthogonalActor) := by
  exact map_mono (comap_mono (intersectionCore_le_sylow M Mc T hTM hTMc))

/-- Normalization is inherited from normality of the two-core in the intersection. -/
public theorem NaturalOrthogonalAction.sylowImage_normalizes_intersectionCoreImage
    {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (Mc : Subgroup G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc) :
    (d.sylowImage T hTM : Subgroup OrthogonalActor) ≤
      normalizer (d.intersectionCoreImage Mc : Set OrthogonalActor) := by
  have hn : M ⊓ Mc ≤ normalizer ((M ⊓ Mc).pCoreIn 2 : Set G) := by
    have h := le_normalizer_map (H := pCore 2 ↥(M ⊓ Mc : Subgroup G)) (M ⊓ Mc).subtype
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have ht : (T : Subgroup G) ≤ normalizer ((M ⊓ Mc).pCoreIn 2 : Set G) :=
    (le_inf hTM hTMc).trans hn
  exact (map_mono ((comap_mono ht).trans
    (le_normalizer_comap M.subtype))).trans (le_normalizer_map d.actor)

/-- The image is normal relative to its actual Sylow image. -/
public theorem NaturalOrthogonalAction.intersectionCoreImage_normal
    {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (Mc : Subgroup G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc) :
    ((d.intersectionCoreImage Mc).subgroupOf
      (d.sylowImage T hTM : Subgroup OrthogonalActor)).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    (d.intersectionCoreImage_le_sylowImage Mc T hTM hTMc)).mpr
      (d.sylowImage_normalizes_intersectionCoreImage Mc T hTM hTMc)

omit [Finite G] in
/-- The genuine noncentrality input 14.1.17(1) makes the core image nontrivial. -/
public theorem NaturalOrthogonalAction.intersectionCoreImage_ne_bot
    {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (Mc : Subgroup G)
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    d.intersectionCoreImage Mc ≠ ⊥ := by
  intro h
  have hk := (Subgroup.map_eq_bot_iff _).mp h
  rw [d.ker_actor] at hk
  apply hRc
  intro x hx
  exact hk (show (⟨x, ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left) hx⟩ : M) ∈
    ((M ⊓ Mc).pCoreIn 2).subgroupOf M from hx)

end CFSG.Quasithin.Chapter15.Section03
