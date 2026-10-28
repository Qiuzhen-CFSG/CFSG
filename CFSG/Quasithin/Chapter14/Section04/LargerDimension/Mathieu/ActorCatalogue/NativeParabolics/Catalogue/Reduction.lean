module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Cubic
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Residuals
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Reducing the native residual catalogue to actual Sylow overgroups

A two-perfect actor normalized by the ambient Sylow subgroup has its two-core
in that Sylow subgroup. The index-three condition therefore makes their join
an index-three overgroup, and taking the residual recovers the actor. This
identifies the literal X-family with the residual image of all these overgroups.

In the native triple extension, an index-three overgroup containing the cubic
kernel must equal its join with the Sylow subgroup. Every other such overgroup
is disjoint from the kernel and preserves its relative index under the actual
design projection. Thus exhaustion requires actual subgroups over the specified
Sylow, not just a list of conjugacy types.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012. The design catalogue
and the binary distinction between its two parabolic types remain separate
inputs to the final assembly.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
section
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private lemma residual_eq_iff (X : Subgroup G) :
    twoResidual X = X ↔ IsPPerfect 2 X := by
  have hh := (map_injective X.subtype_injective).eq_iff (a := pResidual 2 X) (b := ⊤)
  simpa only [twoResidual, ← MonoidHom.range_eq_map, range_subtype] using
    hh.trans (pResidual_eq_top_iff 2 X)

omit [Finite G] in
lemma actor_residual_sup_sylow (S : Sylow 2 G) {X : Subgroup G}
    (hX : ThreeExtension ⊤ (S : Subgroup G) X) :
    twoResidual (X ⊔ (S : Subgroup G)) = X :=
  embedded_pResidual_join_pGroup X S ((residual_eq_iff X).mp hX.residual_eq)
    S.isPGroup' hX.T_normalizes

lemma actor_sup_sylow_index_three (S : Sylow 2 G) {X : Subgroup G}
    (hX : ThreeExtension ⊤ (S : Subgroup G) X) :
    (S : Subgroup G).relIndex (X ⊔ (S : Subgroup G)) = 3 := by
  have hn : (S : Subgroup G) ≤ normalizer (twoCore X : Set G) :=
    hX.T_normalizes.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hcore : twoCore X ≤ (S : Subgroup G) :=
    (pCore_isPGroup.map X.subtype).le_sylow_of_normalized S hn
  have hd := relIndex_dvd_of_le_left X hcore
  rw [hX.index_three] at hd
  rw [relIndex_sup_of_normalizes X (S : Subgroup G) hX.T_normalizes]
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · have hXS : X ≤ (S : Subgroup G) := relIndex_eq_one.mp h
    have hp : IsPGroup 2 X := S.isPGroup'.to_le hXS
    have he : pCore 2 X = ⊤ := top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
    have he' : twoCore X = X := by
      simp only [twoCore, he, ← MonoidHom.range_eq_map, range_subtype]
    have hi := hX.index_three
    rw [he', relIndex_self] at hi
    omega
  · exact h

end

abbrev rankOneOvergroups {G : Type*} [Group G] (S : Sylow 2 G) : Set (Subgroup G) :=
  {P | (S : Subgroup G) ≤ P ∧ (S : Subgroup G).relIndex P = 3}

lemma XFamily_eq_residual_image (S : Sylow 2 Model) :
    XFamily ⊤ (S : Subgroup Model) = twoResidual '' rankOneOvergroups S := by
  ext X
  constructor
  · intro hX
    exact ⟨X ⊔ (S : Subgroup Model), ⟨le_sup_right, actor_sup_sylow_index_three S hX⟩,
      actor_residual_sup_sylow S hX⟩
  · rintro ⟨P, ⟨hSP, hi⟩, rfl⟩
    exact residual_threeExtension_of_index_three S P hSP hi

lemma cubic_sup_mem_rankOneOvergroups (S : Sylow 2 Model) : cubic ⊔ (S : Subgroup Model) ∈ rankOneOvergroups S := by
  have h := actor_sup_sylow_index_three S (firstActor_threeExtension S)
  rw [firstActor_eq_cubic] at h
  exact ⟨le_sup_right, h⟩

lemma residual_cubic_sup_sylow (S : Sylow 2 Model) : twoResidual (cubic ⊔ (S : Subgroup Model)) = cubic := by
  have h := actor_residual_sup_sylow S (firstActor_threeExtension S)
  simpa only [firstActor_eq_cubic] using h

lemma eq_cubic_sup_or_disjoint (S : Sylow 2 Model) {P : Subgroup Model}
    (hP : P ∈ rankOneOvergroups S) : P = cubic ⊔ (S : Subgroup Model) ∨ Disjoint cubic P := by
  let : Fact (Nat.card cubic).Prime := ⟨cubic_card ▸ Nat.prime_three⟩
  rcases (P.subgroupOf cubic).eq_bot_or_eq_top_of_prime_card with hb | ht
  · right
    rw [disjoint_iff, inf_comm, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
  · left
    have hc : cubic ≤ P := subgroupOf_eq_top.mp ht
    have hle : cubic ⊔ (S : Subgroup Model) ≤ P := sup_le hc hP.1
    have hi := relIndex_mul_relIndex (S : Subgroup Model) (cubic ⊔ (S : Subgroup Model)) P
      le_sup_right hle
    rw [(cubic_sup_mem_rankOneOvergroups S).2, hP.2] at hi
    exact le_antisymm (relIndex_eq_one.mp (by omega)) hle

lemma designProjection_injective_of_disjoint {P : Subgroup Model} (hd : Disjoint cubic P) :
    Function.Injective (designProjection.comp P.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← MonoidHom.comap_ker, designProjection_ker]
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact hd.le_bot ⟨hx, x.property⟩

lemma relIndex_image_of_disjoint (S : Sylow 2 Model) {P : Subgroup Model}
    (hSP : (S : Subgroup Model) ≤ P) (hd : Disjoint cubic P) :
    ((S : Subgroup Model).map designProjection).relIndex (P.map designProjection) =
      (S : Subgroup Model).relIndex P := by
  have h := relIndex_map_map_of_injective ((S : Subgroup Model).subgroupOf P) ⊤
    (designProjection_injective_of_disjoint hd)
  have hs : ((S : Subgroup Model).subgroupOf P).map (designProjection.comp P.subtype) =
      (S : Subgroup Model).map designProjection := by
    rw [← map_map, map_subgroupOf_eq_of_le hSP]
  have hp : (⊤ : Subgroup P).map (designProjection.comp P.subtype) = P.map designProjection := by
    rw [← map_map, ← MonoidHom.range_eq_map, range_subtype]
  rw [hs, hp, relIndex_top_right] at h
  exact h

lemma XFamily_eq_of_rankOneOvergroups (S : Sylow 2 Model) (P B : Subgroup Model)
    (he : rankOneOvergroups S = {cubic ⊔ (S : Subgroup Model), P, B}) :
    XFamily ⊤ (S : Subgroup Model) =
      {twoResidual (pCore 3 Model), twoResidual P, twoResidual B} := by
  rw [XFamily_eq_residual_image, he, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    residual_cubic_sup_sylow, firstActor_eq_cubic]

lemma component_sup_sylow (S : Sylow 2 Model) : component ⊔ (S : Subgroup Model) = ⊤ := by
  let q := QuotientGroup.mk' component
  have hp : IsPGroup 2 (Model ⧸ component) := IsPGroup.of_card (n := 1)
    (by simpa only [pow_one, ← index_eq_card] using component_index)
  have hs : (S : Subgroup Model).map q = ⊤ :=
    top_unique ((hp.to_subgroup ⊤).le_sylow_of_normal
      (S.mapSurjective (QuotientGroup.mk'_surjective component)))
  have h := congrArg (Subgroup.comap q) hs
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using h


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
