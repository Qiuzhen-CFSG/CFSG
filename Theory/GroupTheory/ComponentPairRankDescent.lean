module
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Prime-rank descent in a component-pair action quotient

An elementary plane in the image of a subgroup lifts through its coprime
restricted kernel. Its lift is disjoint from the full kernel. An ambient
prime-rank bound of two forces that full kernel to have coprime order by
orbit counting. Distinct commuting factors with orders divisible by the
prime construct the required plane. Separately, normality of a pair of
ordinary components bounds each component's orbit by two.

Source: Aschbacher--Smith, A.1.27 and 1.2.2(a), printed pp.26 and504;
applied to the literal action quotient in 13.6.14, p.929.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.ComponentPairRankDescent
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- A plane in the image of a subgroup with coprime kernel forces the
entire kernel to be coprime under the ambient rank-two bound. -/
theorem coprime_ker_of_plane_in_restricted_range {p : ℕ} [Fact p.Prime]
    (f : G →* H) (J : Subgroup G) (hr : primeRank p G ≤ 2)
    (hk : Nat.Coprime p (Nat.card (f.comp J.subtype).ker))
    (P : Subgroup (f.comp J.subtype).range) [IsElementaryAbelian p P]
    (hc : Nat.card P = p ^ 2) : Nat.Coprime p (Nat.card f.ker) := by
  let r := (f.comp J.subtype).rangeRestrict
  have hkr : r.ker = (f.comp J.subtype).ker := (f.comp J.subtype).ker_rangeRestrict
  obtain ⟨D,hD,hmap,hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    r (f.comp J.subtype).rangeRestrict_surjective (hkr.symm ▸ hk) P
  let := hD
  let E := D.map J.subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map_subtype
  have he : Nat.card E = p ^ 2 := by
    rw [card_map_of_injective J.subtype_injective]
    exact hcard.trans hc
  have hdi : Disjoint E f.ker := by
    apply disjoint_def.mpr
    rintro x ⟨d,hd,rfl⟩ hx
    have hdker : d ∈ (f.comp J.subtype).ker := hx
    have hinj := injective_comp_subtype_of_coprime_ker (f.comp J.subtype) hk D
      (IsElementaryAbelian.isPGroup p D)
    have hh : (⟨d,hd⟩ : D) = 1 := hinj (by
      change (f.comp J.subtype) d = (f.comp J.subtype) 1
      rw [map_one]
      exact hdker)
    exact congrArg (fun a : D => (a : G)) hh
  exact coprime_card_of_normalized_disjoint_plane hr E f.ker he le_normalizer_of_normal hdi

/-- Two disjoint commuting factors divisible by p contain an elementary
plane, with its actual subgroup inclusion retained. -/
theorem exists_plane_in_pair {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hd : Disjoint A B)
    (hcomm : A ≤ centralizer (B : Set G))
    (ha : p ∣ Nat.card A) (hb : p ∣ Nat.card B) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧ E ≤ A ⊔ B := by
  obtain ⟨a,haorder⟩ := exists_prime_orderOf_dvd_card' p ha
  obtain ⟨b,hborder⟩ := exists_prime_orderOf_dvd_card' p hb
  let P := zpowers (a : G)
  let Q := zpowers (b : G)
  have hP : P ≤ A := zpowers_le.mpr a.property
  have hQ : Q ≤ B := zpowers_le.mpr b.property
  have hao : orderOf (a : G) = p := (orderOf_injective A.subtype A.subtype_injective a).trans haorder
  have hbo : orderOf (b : G) = p := (orderOf_injective B.subtype B.subtype_injective b).trans hborder
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one (hao ▸ pow_orderOf_eq_one (a : G))
  let : IsElementaryAbelian p Q := IsElementaryAbelian.zpowers_of_pow_eq_one (hbo ▸ pow_orderOf_eq_one (b : G))
  have hPQ : P ≤ centralizer (Q : Set G) := hP.trans (hcomm.trans (centralizer_le hQ))
  let : IsElementaryAbelian p (P ⊔ Q : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hPQ)
  refine ⟨P ⊔ Q,inferInstance,?_,sup_le_sup hP hQ⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint P Q
    ((le_centralizer_iff.mp hPQ).trans (centralizer_le_normalizer _)) (hd.mono hP hQ),
    Nat.card_zpowers,Nat.card_zpowers,hao,hbo,pow_two]

/-- A normal pair of distinct components admits exactly two conjugates. -/
theorem component_normalizer_index_two_of_normal_pair
    (A : Subgroup G) (hA : IsComponent G A) (t : G)
    (hne : A ≠ A.conjBy t) [(A ⊔ A.conjBy t).Normal] :
    (normalizer (A : Set G)).index = 2 := by
  let B := A.conjBy t
  have hB : IsComponent G B := hA.map_conj t
  have hpair (g : G) : A.conjBy g = A ∨ A.conjBy g = B := by
    let C := A.conjBy g
    by_cases hCA : C = A
    · exact Or.inl hCA
    by_cases hCB : C = B
    · exact Or.inr hCB
    exfalso
    have hC : IsComponent G C := hA.map_conj g
    have hCP : C ≤ A ⊔ B := by
      rintro x ⟨a,ha,rfl⟩
      exact (inferInstance : (A ⊔ B).Normal).conj_mem a (mem_sup_left ha) g
    have hCC : C ≤ centralizer (C : Set G) := by
      apply le_trans ?_ (centralizer_le hCP)
      apply le_centralizer_iff.mpr
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne hC (Ne.symm hCA)))
        (commutator_eq_bot_iff_le_centralizer.mp (hB.commutator_eq_bot_of_ne hC (Ne.symm hCB)))
    let : IsQuasisimple C := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    have hab : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext ((hCC x.property y y.property).symm)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative C hab
  have hsub : (Set.range fun g : G => A.map (MulAut.conj g).toMonoidHom) ⊆ {A,B} := by
    rintro _ ⟨g,rfl⟩
    change A.conjBy g = A ∨ A.conjBy g = B
    exact hpair g
  have hi : (normalizer (A : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hne)
  have hnt : normalizer (A : Set G) ≠ ⊤ := by
    intro he
    exact hne (mem_normalizer_iff_map_conj_eq.mp (he ▸ mem_top t)).symm
  have hlo := (normalizer (A : Set G)).one_lt_index_of_ne_top hnt
  omega

end Theory.GroupTheory.ComponentPairRankDescent
