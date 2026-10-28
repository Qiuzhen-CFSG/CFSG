module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FactorStabilizers
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedLinePermutation

/-!
# Centralizers of the original factor fixed-line points

The image of the Baumann subgroup is a Sylow two-subgroup of the actual
solvable offender product. Its fixed space in each natural factor has
order two. Since the original Sylow subgroup normalizes Baumann, fixing
the nonzero point is equivalent to normalizing that factor. Pulling this
back along the literal quotient H → H/C_H(U_H) and inclusion H → G
identifies its centralizer in T with Baum(T).

The source hypotheses and the selected factors are unchanged. This proves
the point-centralizer assertion of Aschbacher–Smith 13.2.11(4), printed
p.881, retaining the earlier Baumann-normalizer and solvability inputs.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_solvable_paired_fixed_line_centralizers
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      let E := fun i => c.toSolvableFFFactors.factorFixedSpace
        ((ChapterB.baumann (S : Subgroup H)).map q) i
      (∀ i, Nat.card (E i) = 2) ∧
      ∀ i (u : U), Additive.ofMul u ∈ E i → u ≠ 1 →
        (T : Subgroup G) ⊓ centralizer ({((u : H) : G)} : Set G) =
          ChapterB.baumann (T : Subgroup G) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht,hn⟩ := source_solvable_paired_factor_normalizers d hH hB hZ hs hz
  let D := c.toSolvableFFFactors
  let A := (ChapterB.baumann (S : Subgroup H)).map q
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hUT : U ≤ (S : Subgroup H) :=
    hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  have hBq := (ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot hUT hj c hc ht).2
  let O := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨P,hP⟩ := (S.mapSurjective (QuotientGroup.mk'_surjective C)).exists_sylow_map_eq_inf_of_normal O
  have hPA : (P : Subgroup O).map O.subtype = A := hP.trans hBq.symm
  have hcard (i) : Nat.card (D.factorFixedSpace A i) = 2 := by
    rw [← hPA]
    exact D.factorFixedSpace_card P i
  have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  refine ⟨c,hc,ht,hcard,?_⟩
  intro i u hu hu1
  have hu0 : Additive.ofMul u ≠ (0 : Additive U) := hu1
  have hnorm : (normalizer (((c.factor i).comap q).map H.subtype : Set G)).comap H.subtype =
      normalizer ((c.factor i).comap q : Set H) := by
    have hrng : ((c.factor i).comap q).map H.subtype ≤ H.subtype.range :=
      (map_subtype_le _).trans_eq H.range_subtype.symm
    rw [comap_normalizer_eq_of_le_range hrng,comap_map_eq_self_of_injective H.subtype_injective]
  rw [← hn i]
  apply le_antisymm
  all_goals
    intro t htm
    obtain ⟨t,htS,rfl⟩ := hSm.ge htm.1
    have htA : q t ∈ normalizer (A : Set (H ⧸ C)) :=
      (ChapterB.baumann (S : Subgroup H)).le_normalizer_map q
        (mem_map_of_mem q (normalizer_le_normalizer_baumann _
          ((S : Subgroup H).le_normalizer htS)))
    have hiff := D.factorFixedSpace_fixed_iff_normalizes_factor A (q t) htA
      i (hcard i) (Additive.ofMul u) hu hu0
    have hconj : ρ (q t) (Additive.ofMul u) = Additive.ofMul u ↔
        (t : G) ∈ centralizer ({((u : H) : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro hf
        have he := congrArg (fun w : Additive U => (w.toMul : H)) hf
        change ((ρ (q t) (Additive.ofMul u)).toMul : H) = (u : H) at he
        rw [NormalElementaryQuotient.representation_apply] at he
        exact congrArg H.subtype (mul_inv_eq_iff_eq_mul.mp he)
      · intro he
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [NormalElementaryQuotient.representation_apply]
        apply mul_inv_eq_iff_eq_mul.mpr
        apply H.subtype_injective
        exact he
    have hniff : (t : G) ∈ normalizer (((c.factor i).comap q).map H.subtype : Set G) ↔
        q t ∈ normalizer (c.factor i : Set (H ⧸ C)) := by
      change t ∈ (normalizer (((c.factor i).comap q).map H.subtype : Set G)).comap H.subtype ↔ _
      rw [hnorm,← comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective C)]
      rfl
    first
    | exact ⟨htm.1,hniff.mpr (hiff.mp (hconj.mpr htm.2))⟩
    | exact ⟨htm.1,hconj.mp (hiff.mpr (hniff.mp htm.2))⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
