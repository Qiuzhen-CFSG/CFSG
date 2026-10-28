module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals

/-!
# The literal marked parabolic in the large G₂ source row

The original star radical is radical with its full normalizer in the
marked local intersection. The intrinsic G₂ radical theorem gives a full
root parabolic or a Sylow subgroup. Maximality identifies the parabolic;
the Sylow alternative would give a chi-zero block of cubic rank at most
one, contrary to the actual G₂ component.

Source: Aschbacher--Smith C.2.7(3), C.4.1 and 12.7.5, printed pp.146,
151 and 840. All subgroups retain the original star map and marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The full G₂ local intersection is one of the two parabolics under
the same supplied marking and one conjugation. -/
theorem star_g2_marked_parabolic_from_source
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* Model F) (hF : 4 ≤ Nat.card F) :
    ∃ g : Model F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = parabolic₁ ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = parabolic₂ := by
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  let P := (starM K R M).subgroupOf C
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model]
    have h6 := Nat.pow_le_pow_left hF 6
    have h2 := Nat.pow_le_pow_left hF 2
    exact lt_of_lt_of_le (by norm_num : 40320 < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1))
      (Nat.mul_le_mul (Nat.mul_le_mul h6 (Nat.sub_le_sub_right h6 1))
        (Nat.sub_le_sub_right h2 1))
  obtain ⟨hU,hN⟩ := star_intersection_placement_from_source_of_large_order h hlarge
  have hp : P ≠ ⊤ := by
    intro ht
    exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp ht)
  rcases Atlas.G2.radical_normalizer_parabolic_or_sylow
      (U.map e.toMonoidHom) (hU.map_equiv e) with ⟨g,hg⟩ | ⟨S,hS⟩
  · let a := MulAut.conj g
    let Q := (P.map e.toMonoidHom).map a.toMonoidHom
    have hQ : Q ≠ ⊤ := by
      intro ht
      apply hp
      have hh := congrArg (comap (e.trans a).toMonoidHom) ht
      have he : (e.trans a).toMonoidHom = a.toMonoidHom.comp e.toMonoidHom := by
        ext x
        rfl
      simpa only [Q,map_map,←he,
        comap_map_eq_self_of_injective (f := (e.trans a).toMonoidHom)
          (e.trans a).injective,comap_top] using hh
    have hNQ : (normalizer (U.map e.toMonoidHom : Set (Model F))).map a.toMonoidHom ≤ Q := by
      rw [←map_equiv_normalizer_eq]
      exact map_mono (map_mono hN)
    refine ⟨g,?_⟩
    rcases hg with hg | hg
    · exact Or.inl ((HigherFieldResiduals.parabolic₁_isCoatom.le_iff_eq hQ).mp (hg ▸ hNQ))
    · exact Or.inr ((HigherFieldResiduals.parabolic₂_isCoatom.le_iff_eq hQ).mp (hg ▸ hNQ))
  · let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hs' : (S' : Subgroup C) = U := by
      change (S : Subgroup (Model F)).map e.symm.toMonoidHom = U
      rw [hS]
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
    have hSR : (S' : Subgroup C).map C.subtype ≤ starImage K R R := by
      rw [hs',subgroupOf_map_subtype]
      exact inf_le_left
    let : (K.subgroupOf (K ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
    obtain ⟨T,hT⟩ := radical_sylow_of_star_component_sylow (source_join_input h) S' hSR
    have hs : Chapter1.IsSylowIn 2 R (K ⊔ R) := by
      refine ⟨T,?_⟩
      rw [hT,map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]
    have hhigh := chiZero_star_threeRank_le_one (R := R) (source_chiZero_of_sylow_input h hs).2
    change primeRank 3 C ≤ 1 at hhigh
    have hlow : 2 ≤ primeRank 3 C := by
      rw [primeRank_congr 3 e]
      exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Model F)).subtype
          (commutator (Model F)).subtype_injective)
    omega

end CFSG.Quasithin.ChapterC.C27Source
