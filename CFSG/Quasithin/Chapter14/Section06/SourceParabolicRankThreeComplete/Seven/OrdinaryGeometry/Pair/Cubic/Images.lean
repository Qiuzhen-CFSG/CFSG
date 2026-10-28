module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Inputs
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.LocalStructure
public import Theory.Alternating.Aut
/-!
# Images of the original cubic parabolic pair

The common Sylow has index three in each vertex. Under a homomorphism to
a nonsolvable image, this index cannot collapse to one: otherwise one
solvable vertex would cover the whole image. Thus the literal images retain
a common Sylow, cubic indices and generation. The alternating subgroup
inside the actual image supplies nonsolvability.

Consumer: the simultaneous seven-letter recognition in Cubic.Source.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF
variable {K L : Type*} [Group K] [Group L] [Finite K] [Finite L]

lemma pair_local_index {A B : Subgroup K} (h : IsGoldschmidtTriple A B) :
    (A ⊓ B).relIndex A = 3 := by
  let Q := (pCore 2 A).map A.subtype
  have hq : Q.relIndex A = 6 := by
    have hh := relIndex_map_map_of_injective (pCore 2 A) (⊤ : Subgroup A)
      A.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at hh
    rw [hh]
    change Nat.card (A ⧸ pCore 2 A) = 6
    rw [Nat.card_congr h.quotient_left.some.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hh := relIndex_mul_relIndex Q (A ⊓ B) A h.local_twoCore_le_intersection inf_le_left
  rw [h.left_core_index, hq] at hh
  omega

omit [Finite K] [Finite L] in
lemma pair_map_index_dvd (f : K →* L) (S A : Subgroup K) (hSA : S ≤ A) :
    (S.map f).relIndex (A.map f) ∣ S.relIndex A := by
  have he : (S.subgroupOf A).map (f.subgroupMap A) =
      (S.map f).subgroupOf (A.map f) := by
    ext x
    constructor
    · rintro ⟨s,hs,he⟩
      exact ⟨s.val,hs,congrArg Subtype.val he⟩
    · rintro ⟨s,hs,he⟩
      exact ⟨⟨s,hSA hs⟩,hs,Subtype.ext he⟩
  change ((S.map f).subgroupOf (A.map f)).index ∣ (S.subgroupOf A).index
  rw [←he]
  exact (S.subgroupOf A).index_map_dvd (f.subgroupMap_surjective A)

omit [Finite L] in
lemma pair_image_index {A B : Subgroup K} (h : IsGoldschmidtTriple A B)
    (f : K →* L) (hf : Function.Surjective f) (hn : ¬ Group.IsSolvable L) :
    ((A ⊓ B).map f).relIndex (A.map f) = 3 := by
  have hdiv := pair_map_index_dvd f (A ⊓ B) A inf_le_left
  rw [pair_local_index h] at hdiv
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hi | hi
  · have hle : A.map f ≤ B.map f :=
      (relIndex_eq_one.mp hi).trans (map_mono inf_le_right)
    have hb : B.map f = ⊤ := by
      rw [←sup_eq_right.mpr hle, ←Subgroup.map_sup, h.generated,
        map_top_of_surjective _ hf]
    have hfB : Function.Surjective (f.comp B.subtype) :=
      MonoidHom.range_eq_top.mp (by rw [MonoidHom.range_comp,range_subtype,hb])
    let := h.symm.local_solvable
    exact (hn (Group.isSolvable_of_surjective hfB)).elim
  · exact hi

omit [Finite L] in
lemma pair_image_cubic_data {A B : Subgroup K} (h : IsGoldschmidtTriple A B)
    (f : K →* L) (hf : Function.Surjective f) (hn : ¬ Group.IsSolvable L) :
    ∃ S : Sylow 2 L, (S : Subgroup L) ≤ A.map f ∧ (S : Subgroup L) ≤ B.map f ∧
      (S : Subgroup L).relIndex (A.map f) = 3 ∧
      (S : Subgroup L).relIndex (B.map f) = 3 ∧ A.map f ⊔ B.map f = ⊤ := by
  obtain ⟨T,hT⟩ := h.intersection_sylow
  refine ⟨T.mapSurjective hf,?_,?_,?_,?_,?_⟩
  · exact map_mono (hT.symm.le.trans inf_le_left)
  · exact map_mono (hT.symm.le.trans inf_le_right)
  · change ((T : Subgroup K).map f).relIndex (A.map f) = 3
    rw [←hT]
    exact pair_image_index h f hf hn
  · change ((T : Subgroup K).map f).relIndex (B.map f) = 3
    rw [←hT,inf_comm]
    exact pair_image_index h.symm f hf hn
  · rw [←Subgroup.map_sup,h.generated,map_top_of_surjective _ hf]

end CFSG.Quasithin.ChapterF

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
theorem nonsolvable_range {K : Type*} [Group K]
    (f : K →* Equiv.Perm (Fin 7)) (hf : alternatingGroup (Fin 7) ≤ f.range) :
    ¬ Group.IsSolvable f.range := by
  intro hs
  let := hs
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hn := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7))
  exact hn (Group.isSolvable_of_isSolvable_injective (inclusion_injective hf))
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
