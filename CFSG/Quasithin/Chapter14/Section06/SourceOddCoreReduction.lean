module
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalizer
public import CFSG.Quasithin.Chapter14.Section06.SourceQuadraticBound
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupAction.MinimalNormal
public import FeitThompson.FinalTheorem

/-!
# Odd-core reduction in the original abelian plane branch

A nontrivial odd core in H/O₂(H) lifts to a solvable normal subgroup.
Its two-residual is nontrivial, and original 14.6.1(4) makes its join with
T an outside subgroup. Minimal descent gives an actual solvable member
of HStar. The solvable minimal-parabolic theorem and the literal quadratic
bound then force its odd prime to be 3 or 5, with odd rank at most two.
The star-section result also retains the actual irreducible Sylow action.

Source: Aschbacher--Smith, 14.6.11--12, printed pp.1030--1031. These are
the opening reduction and 14.6.12(1); the later two-factor geometry and
odd-core contradiction remain separate assertions.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem oddCore_preimage_solvable_residual
    (H : Subgroup G) (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ X : Subgroup G, X ≤ H ∧ H ≤ normalizer (X : Set G) ∧
      IsPPerfect 2 X ∧ X ≠ ⊥ ∧ Group.IsSolvable X := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let P := pPrimeCore 2 (H ⧸ pCore 2 H)
  let A₀ := P.comap q
  let A := A₀.map H.subtype
  let X := (pResidual 2 A).map A.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hHA : H ≤ normalizer (A : Set G) := by
    have hh := A₀.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  let : Group.IsSolvable P := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    infer_instance
  let : Group.IsSolvable A₀ := isSolvable_comap_of_solvable_ker q P
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (f := (equivMapOfInjective A₀ H.subtype H.subtype_injective).toMonoidHom)
    (equivMapOfInjective A₀ H.subtype H.subtype_injective).surjective
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (equivMapOfInjective (pResidual 2 A) A.subtype A.subtype_injective).toMonoidHom)
    (equivMapOfInjective (pResidual 2 A) A.subtype A.subtype_injective).surjective
  refine ⟨X,(map_subtype_le _).trans hAH,
    hHA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A)),
    isPPerfect_embedded_pResidual 2 A,?_,inferInstance⟩
  intro hz
  have hr : pResidual 2 A = ⊥ :=
    (map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz
  have hAp : IsPGroup 2 A := (isPGroup_quotient_pResidual (G := A) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 A)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hr])
  have hA₀p : IsPGroup 2 A₀ := hAp.of_equiv
    (equivMapOfInjective A₀ H.subtype H.subtype_injective).symm
  have hPp : IsPGroup 2 P := by
    have hh := hA₀p.map q
    change IsPGroup 2 ((P.comap q).map q) at hh
    have he : (P.comap q).map q = P := by
      rw [map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), top_inf_eq]
    exact he ▸ hh
  rcases hPp.card_eq_or_dvd with hc | hc
  · exact hne ((eq_bot_iff_card P).mpr hc)
  · exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) hc

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

theorem source_solvable_minimal_outside_of_oddCore
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ J : Subgroup G, J ≤ H ∧ J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Group.IsSolvable J := by
  obtain ⟨X,hXH,hHX,hp,hXne,hs⟩ := oddCore_preimage_solvable_residual H hne
  have hXT := source_lemma_14_6_1_4 hG T hempty hM hu hmany hcard e hab H hH
    X hXH hHX hp hXne
  let := hs
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (X ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes X (T : Subgroup G) (hH.1.2.trans hHX)
  obtain ⟨J,hJ,hJX,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun J => J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) _ hXT
  refine ⟨J,hJX.trans (sup_le hXH hH.1.2),⟨hJ,?_⟩,?_⟩
  · intro K hK hKJ
    exact (hmin K hK hKJ).ge
  · exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion hJX) (inclusion_injective _)


theorem source_minimal_odd_section_of_oddCore
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver (T.subtype hJ.1.1.2) ⊤,
      ∃ p : ℕ, p.Prime ∧ Odd p ∧
        IsElementaryAbelian p (pResidual 2
          (ChapterB.minimalParabolicStarQuotient (T.subtype hJ.1.1.2) hP)) ∧
        Stellmacher.IsIrreducibleSection
          (ChapterB.minimalParabolicStarSylow (T.subtype hJ.1.1.2) hP) ⊥
          (pResidual 2 (ChapterB.minimalParabolicStarQuotient (T.subtype hJ.1.1.2) hP)) := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  have hP := (Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ).2.1
  obtain ⟨p,hp,ho,hE,hi,_⟩ :=
    ChapterB.minimalParabolic_solvable_star_structure (T.subtype hJ.1.1.2) hP hs
  exact ⟨J,hJ,hJH,hs,hP,p,hp,ho,hE,hi⟩


theorem source_solvable_minimal_prime
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J) :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
      pResidual 2 (J ⧸ pCore 2 J) = pCore p (J ⧸ pCore 2 J) ∧
      IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ pCore p (J ⧸ pCore 2 J)) ∧
      primeRank p (J ⧸ pCore 2 J) ≤ 2 := by
  obtain ⟨_,hP,_,hsq,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  obtain ⟨p,hp,ho,hr,hq,_,_,_⟩ :=
    ChapterB.minimalParabolic_solvable_structure (T.subtype hJ.1.1.2) hP hs
  let : Fact p.Prime := ⟨hp⟩
  have hthree := source_rankTwo_odd_prime_restriction hG T hempty hM hu hmany hcard e
    hab J hJ.1 ho hq
  exact ⟨p,hthree,hr,hq,(primeRank_quotient_le_of_isTwoGroup p ho
    (pCore 2 J) pCore_isPGroup).trans (hsq.stronglyQuasithin p hp ho)⟩

theorem source_oddCore_counterexample_three_or_five
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
        pResidual 2 (J ⧸ pCore 2 J) = pCore p (J ⧸ pCore 2 J) ∧
        IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ pCore p (J ⧸ pCore 2 J)) ∧
        primeRank p (J ⧸ pCore 2 J) ≤ 2 := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  exact ⟨J,hJ,hJH,hs,source_solvable_minimal_prime
    hG T hempty hM hu hmany hcard e hab J hJ hs⟩

end CFSG.Quasithin.Chapter14.Section06
