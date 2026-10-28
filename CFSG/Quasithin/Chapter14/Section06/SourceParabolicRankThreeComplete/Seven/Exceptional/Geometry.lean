module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7Displacement
public import Theory.GroupTheory.PlaneConjugateSpan
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The exceptional A₇ four-space in the second-parabolic argument

The action on the actual block commutator module is faithful modulo O₂(C),
and every nontrivial involution moves a plane. Suppose the second-parabolic
span of V filled this four-space. The group R = C ∩ O₂(J) preserves V and
its point Z, so [V,R] ≤ Z. Normalization extends this bound to the whole
span. The checked A₇ line-displacement theorem then gives R ≤ O₂(C).

A Sylow two-subgroup of C contained in J would consequently have image of
order at most six in C/O₂(C), whereas its actual image has order eight.
Thus the span is proper. Movement of V and the order-sixteen bound give
order eight and rank three, without compatible flag coordinates.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029; the
faithful four-dimensional block action is constructed in C.1.22's
ExceptionalRestrictions.A7 and A7Displacement modules.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Exceptional
variable {G : Type*} [Group G] [Finite G]

private theorem component_sylow_index (C : Subgroup G) (hC : ChapterC.IsExceptionalA7Block C)
    (P : Sylow 2 C) :
    (C.pCoreIn 2).relIndex ((P : Subgroup C).map C.subtype) = 8 := by
  obtain ⟨a⟩ := hC.2.1
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  change ((pCore 2 C).map C.subtype).relIndex ((P : Subgroup C).map C.subtype) = 8
  rw [relIndex_map_map_of_injective _ _ C.subtype_injective,←hk,relIndex_ker]
  change Nat.card (P.mapSurjective hf) = 8
  rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 2520 = 315 * 2^3 by decide,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

private theorem span_ne_whole (C J V Z : Subgroup G)
    (hC : ChapterC.IsExceptionalA7Block C)
    (hJC : J ≤ normalizer (C : Set G))
    (hV : V ≤ (ChapterC.blockU C).map C.subtype) (hZV : Z ≤ V)
    (hVc : Nat.card V = 4) (hZc : Nat.card Z = 2)
    (hcoreV : J.pCoreIn 2 ≤ normalizer (V : Set G))
    (hJZ : J ≤ centralizer (Z : Set G))
    (P : Sylow 2 C) (hPJ : (P : Subgroup C).map C.subtype ≤ J)
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :
    conjugateSpanBy V J ≠ (ChapterC.blockU C).map C.subtype := by
  let W := (ChapterC.blockU C).map C.subtype
  let R := C ⊓ J.pCoreIn 2
  let := hC.1.elementary.map C.subtype
  have hJW : J ≤ normalizer (W : Set G) := hJC.trans
    (normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C))
  have hWZ : W ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mpr ((hZV.trans hV).trans W.le_centralizer)).trans
      (centralizer_le_normalizer _)
  have hJR : J ≤ normalizer (R : Set G) :=
    (le_inf hJC (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
        inf_normalizer_le_normalizer_inf
  have hRJ : R ≤ J := inf_le_right.trans (pCoreIn_le 2 J)
  have hcomm := plane_span_commutator V Z W J R hV hZV hVc hZc
    (inf_le_right.trans hcoreV) hWZ hJW hJR
    (hJZ.trans (centralizer_le_normalizer _)) hRJ
  intro he
  rw [he] at hcomm
  have hZC : Z ≤ C := (hZV.trans hV).trans (map_subtype_le _)
  have hRC : R ≤ C.pCoreIn 2 := by
    intro r hr
    refine ⟨⟨r,hr.1⟩,?_,rfl⟩
    apply hC.mem_core_of_line_displacement (Z.subgroupOf C)
      ((Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).trans hZc) ⟨r,hr.1⟩
    · intro z hz
      exact Subtype.ext (hJZ (hRJ hr) z hz)
    · intro v
      change ⁅r,((v : C) : G)⁆ ∈ Z
      have hm : ((v : C) : G) ∈ W := mem_map_of_mem C.subtype v.property
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator hr hm)
  let Q := (P : Subgroup C).map C.subtype
  have heR : R.relIndex Q = (J.pCoreIn 2).relIndex Q := by
    rw [←inf_relIndex_right R Q,show R ⊓ Q = J.pCoreIn 2 ⊓ Q by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.2,hx.2⟩
      · exact fun hx => ⟨⟨(map_subtype_le (P : Subgroup C)) hx.2,hx.1⟩,hx.2⟩,
      inf_relIndex_right]
  have hiJ : (J.pCoreIn 2).relIndex J = 6 := by
    calc
      _ = ((pCore 2 J).map J.subtype).relIndex ((⊤ : Subgroup J).map J.subtype) := by
        rw [←MonoidHom.range_eq_map,range_subtype]
        rfl
      _ = (pCore 2 J).index := by
        rw [relIndex_map_map_of_injective _ _ J.subtype_injective,relIndex_top_right]
      _ = 6 := SymmetricThreeTwoCore.core_index e
  have hi := (relIndex_le_of_le_left (L := Q) hRC
    (R.subgroupOf Q).index_ne_zero_of_finite).trans
      (heR.le.trans (relIndex_le_of_le_right hPJ (hiJ ▸ by decide)))
  rw [component_sylow_index C hC P,hiJ] at hi
  omega

/-- A moving plane with its fixed source point generates a three-space. -/
theorem span_rank_three (C J V Z : Subgroup G)
    (hC : ChapterC.IsExceptionalA7Block C)
    (hJC : J ≤ normalizer (C : Set G))
    (hV : V ≤ (ChapterC.blockU C).map C.subtype) (hZV : Z ≤ V)
    (hVc : Nat.card V = 4) (hZc : Nat.card Z = 2)
    (hcoreV : J.pCoreIn 2 ≤ normalizer (V : Set G))
    (hJZ : J ≤ centralizer (Z : Set G))
    (P : Sylow 2 C) (hPJ : (P : Subgroup C).map C.subtype ≤ J)
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3))
    (hmove : ¬ J ≤ normalizer (V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpanBy V J) ∧
      Nat.card (conjugateSpanBy V J) = 8 ∧ primeRank 2 (conjugateSpanBy V J) = 3 := by
  let W := (ChapterC.blockU C).map C.subtype
  let U := conjugateSpanBy V J
  have hJW : J ≤ normalizer (W : Set G) := hJC.trans
    (normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C))
  have hUW : U ≤ W := conjugateSpanBy_le hV hJW
  have hWc : Nat.card W = 16 := (card_map_of_injective C.subtype_injective).trans hC.u_card
  have hlo : 4 < Nat.card U := by
    apply lt_of_not_ge
    intro hc
    have he : V = U := eq_of_le_of_card_ge (le_conjugateSpanBy V J) (by simpa [hVc] using hc)
    exact hmove (he ▸ le_normalizer_conjugateSpanBy V J)
  have hne : Nat.card U ≠ 16 := by
    intro hc
    exact span_ne_whole C J V Z hC hJC hV hZV hVc hZc hcoreV hJZ P hPJ e
      (eq_of_le_of_card_ge hUW (by rw [hc,hWc]))
  have hd : Nat.card U ∣ 2^4 := by
    simpa only [hWc,show (2:ℕ)^4=16 by decide] using card_dvd_of_le hUW
  obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hUc : Nat.card U = 8 := by
    interval_cases n <;> norm_num only [pow_zero,pow_one,
      show (2:ℕ)^2=4 by decide,show (2:ℕ)^3=8 by decide,
      show (2:ℕ)^4=16 by decide] at hc <;> omega
  let : IsElementaryAbelian 2 W := hC.1.elementary.map C.subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion hUW) (inclusion_injective hUW)
  refine ⟨inferInstance,hUc,le_antisymm ?_ ?_⟩
  · exact IsElementaryAbelian.primeRank_le_of_card_le U (n := 3) (by rw [hUc]; decide)
  · let : IsElementaryAbelian 2 (⊤ : Subgroup U) := IsElementaryAbelian.of_injective
      (⊤ : Subgroup U).subtype (⊤ : Subgroup U).subtype_injective
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup U)
      ((Nat.card_congr (topEquiv : (⊤ : Subgroup U) ≃* U).toEquiv).trans hUc)

end CFSG.Quasithin.Chapter14.Section06.Seven.Exceptional
