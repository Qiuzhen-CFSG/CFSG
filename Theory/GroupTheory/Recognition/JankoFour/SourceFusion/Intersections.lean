module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Defs
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Orbits
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairSpaces

/-!
# Intersections of Todd radicals under the second centralizer

If g centralizes t but lies outside M=N_G(E), then t belongs to the distinct
intersection E ∩ Eᵍ. A marker-class element there would activate the exact
standing hypothesis of (6.2)(3), forcing t into the marker class. Nonfusion
excludes that possibility; the two Todd orbits then give the second class.
Transport of the native pair-subspace bound gives order at most four and
binary rank at most two for this same original intersection.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(d), p.602.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The first conclusion of (6.3)(d). The marker-class premise of (6.2)
is supplied only in the rejected marker-orbit branch. -/
theorem centralizer_intersection_second (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (u : G) (hu : u ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom)
    (hu1 : u ≠ 1) : ∃ m ∈ a.P.M, MulAut.conj m (second a) = u := by
  have ht : second a ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom := by
    refine ⟨second_mem a,second a,second_mem a,?_⟩
    change g * second a * g⁻¹ = second a
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgc)
  have hne : a.P.E.map (MulAut.conj g).toMonoidHom ≠ a.P.E := by
    intro he
    apply hgm
    rw [←a.point_normalizer]
    exact mem_normalizer_iff_map_conj_eq.mpr he
  rcases E_orbits a u hu.1 hu1 with ⟨m,hm,he⟩ | hc
  · have hz : IsConj z u := isConj_iff.mpr ⟨m,he⟩
    exact (not_isConj_second a (hi g hne ⟨u,hu,hz⟩ (second a) ht (second_ne_one a))).elim
  · exact hc

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- Transport the native pair-subspace bound through the actual embedding. -/
theorem pair_subgroup_card_le_four (P : PointData z) (U : Subgroup G) (hUE : U ≤ P.E)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ B : PointPair,
      P.vectorEmbedding (Multiplicative.ofAdd (pairVector B)) = u) : Nat.card U ≤ 4 := by
  let W := AddSubgroup.toZModSubmodule 2 (U.comap P.vectorEmbedding).toAddSubgroup'
  let f : W → U := fun v => ⟨P.vectorEmbedding (Multiplicative.ofAdd v.val),v.property⟩
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨v,hv⟩ := hUE u.property
    have hw : v.toAdd ∈ W := by
      change P.vectorEmbedding v ∈ U
      rw [hv]
      exact u.property
    exact ⟨⟨v.toAdd,hw⟩,Subtype.ext hv⟩
  apply (Nat.card_le_card_of_surjective f hf).trans
  apply MathieuCode.J4Fusion.pair_space_card_le_four W
  intro v hv hv0
  have hne : P.vectorEmbedding (Multiplicative.ofAdd v) ≠ 1 := by
    intro he
    exact hv0 (congrArg Multiplicative.toAdd
      (P.vectorEmbedding_injective (he.trans (map_one _).symm)))
  obtain ⟨B,hB⟩ := hp _ hv hne
  exact ⟨B,(congrArg Multiplicative.toAdd (P.vectorEmbedding_injective hB)).symm⟩

/-- AS91 (6.3)(d): the actual radical intersection has order at most four. -/
theorem centralizer_intersection_card_le_four (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M) :
    Nat.card (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 4 := by
  apply pair_subgroup_card_le_four a.P _ inf_le_left
  intro u hu hu1
  obtain ⟨m,hm,he⟩ := centralizer_intersection_second a hi g hgc hgm u hu hu1
  rw [second,vector_conj a.P ⟨m,hm⟩,pairVector_equivariant] at he
  exact ⟨_,he⟩

/-- The binary rank convention in the source, on that same intersection. -/
theorem centralizer_intersection_rank_le_two (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M) :
    Nat.log 2 (Nat.card (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 2 :=
  (Nat.log_mono_right (centralizer_intersection_card_le_four a hi g hgc hgm)).trans
    (by decide : Nat.log 2 4 ≤ 2)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
