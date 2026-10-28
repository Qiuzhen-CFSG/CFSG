module

public import CFSG.Quasithin.Chapter14.Section06.MaximalOvergroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# Sylow intersections for suitable involutions

The normalizers from 14.6.3 form the two-step chain
`Tᵤ < T₀ < T`, with both indices two. A member of the original local
family containing `Tᵤ`, but lying in neither `M` nor `G₁`, cannot contain
`T`: its nontrivial two-core would put it in one of those two maximal
two-local overgroups. The normalizer condition in finite two-groups then
forces its intersection with `T` to be `Tᵤ` or `T₀`. Either intersection
is self-normalizing inside the local subgroup, hence Sylow and nonnormal.

This proves Lemma 14.6.6(1), (2), and (7) from the earlier normalizer and
index conclusions of 14.6.3. These clauses do not need the maximality
condition defining `I⁎`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, pp. 1023–1024.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section06

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem intermediate_eq_of_relIndex_two {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hindex : A.relIndex C = 2) :
    B = A ∨ B = C := by
  have hp : (A.relIndex B * B.relIndex C).Prime := by
    rw [relIndex_mul_relIndex A B C hAB hBC, hindex]
    exact Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hi⟩ | ⟨_, hi⟩
  · exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hi))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hi) hAB)

/-- Lemma 14.6.6(1), (2), and (7), for the literal `H(Tᵤ)` family.
The earlier source input consists of 14.6.3's two index and two normalizer
equalities and 14.2.2(5)'s maximal two-local overgroups. -/
theorem suitable_involution_intersection_sylow
    (T : Sylow 2 G) (Tu T0 M Mc I : Subgroup G)
    (hTuIndex : Tu.relIndex T0 = 2)
    (hT0Index : T0.relIndex (T : Subgroup G) = 2)
    (hNTu : normalizer (Tu : Set G) = T0)
    (hNT0 : normalizer (T0 : Set G) = (T : Subgroup G))
    (hpair : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc})
    (hI : I ∈ outsideOvergroups (Chapter1.H G) Tu Mc M) :
    ((T : Subgroup G) ⊓ I = Tu ∨ (T : Subgroup G) ⊓ I = T0) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I ∧
      ¬ (((T : Subgroup G) ⊓ I).subgroupOf I).Normal := by
  have hTuT0 : Tu ≤ T0 := hNTu ▸ Tu.le_normalizer
  have hT0T : T0 ≤ (T : Subgroup G) := hNT0 ▸ T0.le_normalizer
  have hTM : (T : Subgroup G) ≤ M :=
    (show M ∈ maximalTwoLocalOvergroups (T : Subgroup G) from
      hpair ▸ Set.mem_insert M {Mc}).2
  have hnotTI : ¬ (T : Subgroup G) ≤ I := by
    intro hTI
    have hcore : pCore 2 I ≠ ⊥ := by
      intro hb
      apply hI.1
      change (pCore 2 I).map I.subtype = ⊥
      rw [hb, Subgroup.map_bot]
    obtain ⟨J, hJ, hIJ⟩ :=
      exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
    have hmem : J ∈ ({M, Mc} : Set (Subgroup G)) :=
      hpair ▸ (show J ∈ maximalTwoLocalOvergroups (T : Subgroup G) from
        ⟨hJ, hTI.trans hIJ⟩)
    rcases Set.mem_insert_iff.mp hmem with hJM | hJMc
    · exact hI.2.2.2 (hJM ▸ hIJ)
    · exact hI.2.2.1 (Set.mem_singleton_iff.mp hJMc ▸ hIJ)
  let R : Subgroup G := (T : Subgroup G) ⊓ I
  have hTuR : Tu ≤ R := le_inf (hTuT0.trans hT0T) hI.2.1
  have hRtwo : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hcases : R = Tu ∨ R = T0 := by
    have hTuN : Tu ≤ R ⊓ normalizer (Tu : Set G) :=
      le_inf hTuR Tu.le_normalizer
    have hNT0' : R ⊓ normalizer (Tu : Set G) ≤ T0 :=
      inf_le_right.trans_eq hNTu
    rcases intermediate_eq_of_relIndex_two hTuN hNT0' hTuIndex with hn | hn
    · left
      let : Group.IsNilpotent R := hRtwo.isNilpotent
      have hself : normalizer (Tu.subgroupOf R : Set R) = Tu.subgroupOf R := by
        rw [← subgroupOf_normalizer_eq hTuR]
        ext x
        change (x : G) ∈ normalizer (Tu : Set G) ↔ (x : G) ∈ Tu
        constructor
        · intro hx
          exact hn ▸ (show (x : G) ∈ R ⊓ normalizer (Tu : Set G) from ⟨x.property, hx⟩)
        · exact fun hx => Tu.le_normalizer hx
      have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
        (Group.normalizerCondition_of_isNilpotent (G := R)) _ hself
      exact le_antisymm (subgroupOf_eq_top.mp htop) hTuR
    · have hT0R : T0 ≤ R := hn ▸ inf_le_left
      rcases intermediate_eq_of_relIndex_two hT0R
        (show R ≤ (T : Subgroup G) from inf_le_left) hT0Index with h | h
      · exact Or.inr h
      · exact (hnotTI (h ▸ (show R ≤ I from inf_le_right))).elim
  have hNR : normalizer (R : Set G) ≤ (T : Subgroup G) := by
    rcases hcases with h | h
    · rw [h, hNTu]
      exact hT0T
    · rw [h, hNT0]
  have hself : normalizer (R.subgroupOf I : Set I) = R.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq (show R ≤ I from inf_le_right)]
    apply le_antisymm
    · intro x hx
      exact ⟨hNR hx, x.property⟩
    · exact comap_mono R.le_normalizer
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq
    (R.subgroupOf I) hRtwo.comap_subtype hself
  refine ⟨hcases, ⟨P, ?_⟩, ?_⟩
  · rw [hP, map_subgroupOf_eq_of_le (show R ≤ I from inf_le_right)]
  · intro hn
    have hIN := (normal_subgroupOf_iff_le_normalizer
      (show R ≤ I from inf_le_right)).mp hn
    exact hI.2.2.2 ((hIN.trans hNR).trans hTM)

end CFSG.Quasithin.Chapter14.Section06
