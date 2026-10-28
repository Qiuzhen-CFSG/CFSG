module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The faithful binary component in the star quotient

The local factorization and relative Sylow data give H* = L*T*, with L*
normal and T* Sylow. Because O₂(H) lies in T, taking star images preserves
the literal intersection T ∩ L. In particular the component parabolic
contains a Sylow subgroup of L*.

The centralizer of L* embeds in H*/L*: its intersection with L* is trivial
by the checked binary matrix center calculation. The quotient is a two-group,
so that normal centralizer is a two-group. Since O₂(H*) = 1, it is trivial.
Thus faithful component action is derived from the local data, without an
additional centralizer assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1144–1145, (k)–(l) and the binary generation paragraph.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
variable {G : Type*} [Group G]

lemma component_le {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) : L ≤ H := by
  rw [d.factorization_LT]
  exact le_sup_left

lemma sylow_le {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) : T ≤ H := by
  rw [d.factorization_LT]
  exact le_sup_right

lemma star_generation {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    starImage H L ⊔ starImage H T = ⊤ := by
  rw [starImage, starImage, ← Subgroup.map_sup,
    ← subgroupOf_sup (component_le d) (sylow_le d), ← d.factorization_LT]
  rw [subgroupOf_self]
  change (⊤ : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = ⊤
  apply (eq_top_iff' _).mpr
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  exact ⟨y, mem_top _, hy⟩

lemma star_component_normal {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    (starImage H L).Normal := by
  have hn : (L.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (component_le d)).mpr d.normalizes_component
  exact hn.map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)

lemma star_sylow [Finite G] {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    ∃ S : Sylow 2 (H ⧸ pCore 2 H), (S : Subgroup _) = starImage H T := by
  obtain ⟨S, hS⟩ := d.sylow
  refine ⟨S.mapSurjective (f := QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _), ?_⟩
  change (S : Subgroup H).map _ = (T.subgroupOf H).map _
  rw [← hS, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]

lemma star_sylow_isPGroup [Finite G] {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    IsPGroup 2 (starImage H T) := by
  obtain ⟨S, hS⟩ := star_sylow d
  exact hS ▸ S.isPGroup'

variable [Finite G]


omit [Finite G] in
lemma core_le_sylow {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    pCore 2 H ≤ T.subgroupOf H := by
  obtain ⟨S, hS⟩ := d.sylow
  rw [← hS, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  exact pCore_isPGroup.le_sylow_of_normal S

omit [Finite G] in
lemma star_sylow_intersection {H M L Y T : Subgroup G}
    (d : ReducedLocalData H M L Y T) :
    starImage H (T ⊓ L) = starImage H T ⊓ starImage H L := by
  simp only [starImage, subgroupOf, comap_inf]
  rw [inf_comm, map_inf_of_ker_le _ _ _ (by
    rw [QuotientGroup.ker_mk']; exact core_le_sylow d), inf_comm]

lemma component_sylow {H M L Y T : Subgroup G} (d : ReducedLocalData H M L Y T) :
    ∃ S : Sylow 2 (starImage H L),
      (S : Subgroup (starImage H L)) = (starImage H (T ⊓ L)).subgroupOf (starImage H L) := by
  let _ : (starImage H L).Normal := star_component_normal d
  obtain ⟨S, hS⟩ := star_sylow d
  obtain ⟨S₀, hS₀⟩ := S.exists_subgroupOf_eq_of_normal (starImage H L)
  refine ⟨S₀, ?_⟩
  rw [star_sylow_intersection d, hS₀, hS]
  ext x
  exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

lemma component_sylow_le_parabolic {H M L Y T : Subgroup G}
    (d : ReducedLocalData H M L Y T) :
    ∃ S : Sylow 2 (starImage H L),
      (S : Subgroup (starImage H L)) ≤
        (componentParabolic H L Y T).subgroupOf (starImage H L) := by
  obtain ⟨S, hS⟩ := component_sylow d
  refine ⟨S, ?_⟩
  rw [hS]
  exact comap_mono le_sup_right

omit [Finite G] in
lemma parabolic_eq_base_of_inner {H M L Y T : Subgroup G}
    (d : ReducedLocalData H M L Y T) (hinner : starImage H T ≤ starImage H L) :
    componentParabolic H L Y T = starImage H Y ⊔ starImage H T := by
  rw [componentParabolic, star_sylow_intersection d, inf_eq_left.mpr hinner]

lemma star_core_eq_bot (H : Subgroup G) : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hc := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
  have hm := congrArg (Subgroup.map q) hc
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

private lemma centerless_normal_centralizer {X : Type*} [Group X]
    (K S : Subgroup X) [K.Normal] (hgen : K ⊔ S = ⊤)
    (hS : IsPGroup 2 S) (hcenter : center K = ⊥) (hcore : pCore 2 X = ⊥) :
    centralizer (K : Set X) = ⊥ := by
  let q := QuotientGroup.mk' K
  have hsurj : Function.Surjective (q.domRestrict S) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K z
    obtain ⟨k, hk, s, hs, rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top x)
    refine ⟨⟨s, hs⟩, ?_⟩
    change q s = q (k * s)
    rw [map_mul, show q k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, one_mul]
  have hpq : IsPGroup 2 (X ⧸ K) := hS.of_surjective _ hsurj
  have hinj : Function.Injective (q.domRestrict (centralizer (K : Set X))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxK : (x : X) ∈ K := (QuotientGroup.eq_one_iff (x : X)).mp hx
    have hxc : (⟨x, hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (x.property k k.property)
    rw [hcenter, mem_bot] at hxc
    exact Subtype.ext (congrArg (fun k : K => (k : X)) hxc)
  have hp : IsPGroup 2 (centralizer (K : Set X)) := hpq.of_injective _ hinj
  exact le_bot_iff.mp ((le_sSup ⟨inferInstance, hp⟩ : centralizer (K : Set X) ≤ pCore 2 X).trans hcore.le)

lemma star_component_centralizer {H M L Y T : Subgroup G} {n : ℕ} [NeZero n]
    (d : BinaryLocalData H M L Y T n) :
    centralizer (starImage H L : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let _ : (starImage H L).Normal := star_component_normal d.reduced
  exact centerless_normal_centralizer (starImage H L) (starImage H T)
    (star_generation d.reduced) (star_sylow_isPGroup d.reduced)
    (Chapter2.ComponentRefinement.LieType.Binary.center_eq_bot d.position.model)
    (star_core_eq_bot H)
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
