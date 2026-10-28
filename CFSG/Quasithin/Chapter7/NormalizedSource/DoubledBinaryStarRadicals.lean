module
public import Theory.GroupTheory.PerfectSylowTwo
public import FeitThompson.FinalTheorem
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow
public import Theory.SpecificGroups.SL2.RadicalSubgroups
public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Radical-index exclusions on the original doubled star component

The original Q has index two in a Sylow of H. Restricting that Sylow to the
subnormal component and taking its actual star image gives index at most
two for Q* ∩ K*. This intersection is nontrivial: otherwise a Sylow of the
nontrivial perfect K* has order at most two, contrary to odd-order theory
and transfer.

Every nontrivial radical in SL₂(2ⁿ) is Sylow. In G₂(2ⁿ), the exact radical
normalizer theorem leaves either a Sylow or a parabolic radical of order
q⁵. Since a component Sylow has order q⁶, the index bound excludes the
parabolic option for q > 2. The full star-kernel lifting theorem then makes
the original Q Sylow in KQ in both model families, contradicting 7.7.9(2).
Combining these tests with the earlier nonbinary SL₃/Sp₄ and A₅ exclusions
leaves an exhaustive finite catalogue, with the triple-cover center retained.

NonFFSourceDoubledBinaryStarRadicals supplies all premises on the same chosen
orbit and component. The remaining quotient models do not yet identify the
full component or prove ambient paired-plane containment.
Source: Aschbacher--Smith 7.7.9--10, pp.708--709, C.2.7, pp.145--147,
refs/quasithin.pdf. The imported G₂ root calculations retain their licensed
ATLAS attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarRadicals
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

private theorem image_intersection_sylow_index
    {A : Type*} [Group A] [Finite A]
    (C Q : Subgroup G) (hC : C.IsSubnormal) (P : Sylow 2 G)
    (hindex : Q.relIndex (P : Subgroup G) ≤ 2)
    (q : C →* A) (hq : Function.Surjective q) :
    ∃ S : Sylow 2 A, ((Q.subgroupOf C).map q).relIndex (S : Subgroup A) ≤ 2 := by
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC
  refine ⟨S.mapSurjective hq,?_⟩
  change ((Q.subgroupOf C).map q).relIndex ((S : Subgroup C).map q) ≤ 2
  rw [←relIndex_comap]
  apply le_trans (relIndex_le_of_le_left (le_comap_map _ _) index_ne_zero_of_finite)
  rw [hS,←inf_subgroupOf_right (P : Subgroup G) C,
    relIndex_subgroupOf (show (P : Subgroup G) ⊓ C ≤ C from inf_le_right)]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hindex

variable {H K Q M : Subgroup G}

/-- The original index-two bound survives on the literal star intersection. -/
theorem star_intersection_sylow_index
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2) :
    ∃ S : Sylow 2 (starImage K Q K),
      ((starImage K Q Q).subgroupOf (starImage K Q K)).relIndex
        (S : Subgroup (starImage K Q K)) ≤ 2 := by
  let K₀ := K.subgroupOf H
  let e : K₀ ≃* K := subgroupOfEquivOfLe h.component.1
  let C := starImage K Q K
  let f : K₀ →* C := (toStarImage K Q).comp e.toMonoidHom
  obtain ⟨S,hS⟩ := image_intersection_sylow_index K₀ (Q.subgroupOf H)
    h.component.2.subnormal P hindex f ((toStarImage_surjective K Q).comp e.surjective)
  refine ⟨S,le_trans (relIndex_le_of_le_left ?_ index_ne_zero_of_finite) hS⟩
  rintro _ ⟨k,hk,rfl⟩
  exact ⟨inclusion (show K ≤ K ⊔ Q from le_sup_left) (e k),hk,rfl⟩

/-- The original half-Sylow radical has nontrivial intersection with the
perfect star component, even if the star radical has outer elements. -/
theorem star_intersection_ne_bot
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2) :
    (starImage K Q Q).subgroupOf (starImage K Q K) ≠ ⊥ := by
  let C := starImage K Q K
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let : IsQuasisimple C := (star_fitting_quasisimple (source_join_input h)).2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  obtain ⟨S,hS⟩ := star_intersection_sylow_index h P hindex
  intro hz
  rw [hz,relIndex_bot_left] at hS
  have heven : Even (Nat.card C) := by
    by_contra he
    exact Group.IsPerfect.not_isSolvable C
      (odd_order_theorem C (Nat.not_even_iff_odd.mp he))
  exact (not_lt_of_ge hS) (perfect_sylow_two_card_gt_two S heven)

/-- Every rank-one star model forces the original radical to be Sylow. -/
theorem rankOne_star_core_sylow
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : starImage K Q K ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    Chapter1.IsSylowIn 2 Q (K ⊔ Q) := by
  let C := starImage K Q K
  let U := (starImage K Q Q).subgroupOf C
  have hr := star_intersection_radical_from_source h (star_intersection_ne_bot h P hindex)
  obtain ⟨S,hS⟩ := Matrix.SpecialLinearGroup.radical_eq_sylow (U.map e.toMonoidHom)
    (hr.map_equiv e)
  let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hs' : (S' : Subgroup C) = U := by
    change (S : Subgroup _).map e.symm.toMonoidHom = U
    rw [hS]
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  have hSQ : (S' : Subgroup C).map C.subtype ≤ starImage K Q Q := by
    rw [hs',subgroupOf_map_subtype]
    exact inf_le_left
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  obtain ⟨T,hT⟩ := radical_sylow_of_star_component_sylow (source_join_input h) S' hSQ
  exact ⟨T,by rw [hT,map_subgroupOf_eq_of_le (show Q ≤ K ⊔ Q from le_sup_right)]⟩

open Atlas.G2 Atlas.G2.LieParabolicSetup in
/-- A nonbinary G₂ radical occupying at least half a Sylow is the full Sylow. -/
theorem g2_radical_of_small_index
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree)
    (R : Subgroup (Model F.Carrier)) (hr : R.IsPRadical 2)
    (S : Sylow 2 (Model F.Carrier)) (hi : R.relIndex (S : Subgroup _) ≤ 2) :
    ∃ T : Sylow 2 (Model F.Carrier), (T : Subgroup _) = R := by
  rcases radical_normalizer_parabolic_or_sylow R hr with ⟨g,hg⟩ | hs
  · have hcore : (normalizer (R : Set (Model F.Carrier))).pCoreIn 2 = R := hr.2
    have hm := map_pCoreIn_of_injective 2 (normalizer (R : Set (Model F.Carrier)))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rw [hcore] at hm
    have hc : Nat.card R = Nat.card F.Carrier ^ 5 := by
      rw [Nat.card_congr (R.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv,hm]
      rcases hg with hg | hg
      · rw [hg,EvenLocal.parabolic₁_pCoreIn,card_radical₁]
      · rw [hg,EvenLocal.parabolic₂_pCoreIn,card_radical₂]
    have hS : Nat.card S = Nat.card F.Carrier ^ 6 := by
      rw [Nat.card_congr (S.equiv (sylow (F := F.Carrier))).toEquiv]
      exact card_unipotent
    let j : R.subgroupOf (S : Subgroup _) → R := fun r => ⟨r.val.val,r.property⟩
    have hj : Function.Injective j := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun r : R => (r : Model F.Carrier)) he
    have hb : Nat.card S ≤ Nat.card R * 2 := by
      calc
        Nat.card S = Nat.card (R.subgroupOf (S : Subgroup _)) *
            (R.subgroupOf (S : Subgroup _)).index := (card_mul_index _).symm
        _ ≤ Nat.card R * 2 := Nat.mul_le_mul (Nat.card_le_card_of_injective j hj) hi
    rw [hc,hS,pow_succ] at hb
    have hq : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (by decide : 2 < 2 ^ 2).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree))
    have hp : 0 < Nat.card F.Carrier ^ 5 := pow_pos (by omega) _
    nlinarith
  · exact hs


/-- The original half-Sylow bound excludes the parabolic-radical option
in every nonbinary G₂ star model and lifts Sylow status through the full kernel. -/
theorem g2_star_core_sylow
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree)
    (e : starImage K Q K ≃* Atlas.G2.Model F.Carrier) :
    Chapter1.IsSylowIn 2 Q (K ⊔ Q) := by
  let C := starImage K Q K
  let U := (starImage K Q Q).subgroupOf C
  have hr := star_intersection_radical_from_source h (star_intersection_ne_bot h P hindex)
  obtain ⟨S,hS⟩ := star_intersection_sylow_index h P hindex
  let Se := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (U.map e.toMonoidHom).relIndex (Se : Subgroup _) ≤ 2 := by
    change (U.map e.toMonoidHom).relIndex ((S : Subgroup C).map e.toMonoidHom) ≤ 2
    rwa [relIndex_map_map_of_injective _ _ e.injective]
  obtain ⟨T,hT⟩ := g2_radical_of_small_index F hn (U.map e.toMonoidHom)
    (hr.map_equiv e) Se he
  let T' := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have ht' : (T' : Subgroup C) = U := by
    change (T : Subgroup _).map e.symm.toMonoidHom = U
    rw [hT]
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  have hTQ : (T' : Subgroup C).map C.subtype ≤ starImage K Q Q := by
    rw [ht',subgroupOf_map_subtype]
    exact inf_le_left
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  obtain ⟨R,hR⟩ := radical_sylow_of_star_component_sylow (source_join_input h) T' hTQ
  exact ⟨R,by rw [hR,map_subgroupOf_eq_of_le (show Q ≤ K ⊔ Q from le_sup_right)]⟩

open ChapterB.QuasisimpleSource in
/-- The finite star-model frontier after the original radical-index tests.
Every alternative retains the literal group isomorphisms and the triple-six center. -/
@[expose] def RemainingStarModel (A : Type*) [Group A] : Prop :=
  (∃ F : BinaryField, F.degree = 1 ∧
    Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ∨
  (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (A ≃* alternatingGroup (Fin n))) ∨
  Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
  Nonempty (center A ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((A ⧸ center A) ≃* alternatingGroup (Fin 6))

/-- The original C.2.7 star catalogue reduces to the remaining finite catalogue
once the previously proved nonbinary linear and symplectic tests are supplied. -/
theorem remaining_star_models
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2)
    (hnot : ¬ Chapter1.IsSylowIn 2 Q (K ⊔ Q))
    (hfive : ¬ Nonempty (starImage K Q K ≃* alternatingGroup (Fin 5)))
    (hlinear : ∀ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree →
      ¬ Nonempty (starImage K Q K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hsymplectic : ∀ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree →
      ¬ Nonempty (starImage K Q K ≃* Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)) :
    RemainingStarModel (starImage K Q K) := by
  cases star_model_from_source h with
  | linearTwo F e => exact (hnot (rankOne_star_core_sylow h P hindex F e)).elim
  | linearThree F e =>
    by_cases hn : 1 < F.degree
    · exact (hlinear F hn ⟨e⟩).elim
    · exact Or.inl ⟨F,by have := F.degree_pos; omega,⟨e⟩⟩
  | symplectic F hn e => exact (hsymplectic F hn ⟨e⟩).elim
  | g2 F hn e => exact (hnot (g2_star_core_sylow h P hindex F hn e)).elim
  | g2DerivedTwo e => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | alternating n hn e =>
    rcases hn with rfl | h6 | h7 | h8
    · exact (hfive ⟨e⟩).elim
    · exact Or.inr (Or.inl ⟨n,Or.inl h6,⟨e⟩⟩)
    · exact Or.inr (Or.inl ⟨n,Or.inr (Or.inl h7),⟨e⟩⟩)
    · exact Or.inr (Or.inl ⟨n,Or.inr (Or.inr h8),⟨e⟩⟩)
  | linearFiveTwo e => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | tripleSix ce qe => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨ce⟩,⟨qe⟩⟩)))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarRadicals
