module

public import Theory.SpecificGroups.Alternating.E9A4LocalRank
public import Theory.SpecificGroups.AlternatingSix.ElementaryAbelian
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Commuting A₆ subgroups and quasithin local rank

Two commuting copies of A₆ have trivial intersection because A₆ is centerless.
The first supplies an elementary abelian subgroup of order nine; the second
supplies the natural A₄ on four of its six letters. Their product has a normal
four-group and an elementary abelian subgroup of order 27, so its embedding
forces two-local three-rank at least three. Consequently every A₆ component
of a quasithin group is normal.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569. The normality argument
also supplies the A₆ case of the invocation of 1.2.1(3) there. No component
normality, ambient direct-product embedding, or local-rank bound is assumed.
-/

public section

open Subgroup Equiv
open scoped IsMulCommutative
namespace alternatingGroup

private def a4Sum : alternatingGroup (Fin 4) →* alternatingGroup (Fin 4 ⊕ Fin 2) :=
  ((Perm.sumCongrHom (Fin 4) (Fin 2)).comp
    ((alternatingGroup (Fin 4)).subtype.prod (1 : alternatingGroup (Fin 4) →* Perm (Fin 2)))).codRestrict _
      (by
        intro a
        change Perm.sign (Equiv.sumCongr (a : Perm (Fin 4)) 1) = 1
        rw [Perm.sign_sumCongr, Perm.mem_alternatingGroup.mp a.property, map_one, mul_one])

private def a4Embedding : alternatingGroup (Fin 4) →* alternatingGroup (Fin 6) :=
  (Equiv.altCongrHom finSumFinEquiv).toMonoidHom.comp a4Sum

private theorem a4Embedding_injective : Function.Injective a4Embedding := by
  intro a b h
  have he := (Equiv.altCongrHom finSumFinEquiv).injective h
  have hp := Perm.sumCongrHom_injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg Prod.fst hp)

private theorem three_le_localRank_of_nine_prod_a4_embedding
    {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (f : P × alternatingGroup (Fin 4) →* G) (hf : Function.Injective f) :
    3 ≤ twoLocalPrimeRank 3 G := by
  let : CommGroup P := { (inferInstance : Group P) with mul_comm := mul_comm' }
  let A := alternatingGroup (Fin 4)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A) 3
    (by rw [alternatingGroup.card_of_card_eq_four (by simp)]; decide)
  let C := zpowers z
  let : CommGroup C := IsCyclic.commGroup
  have hc : Nat.card C = 3 := (Nat.card_zpowers z).trans hz
  have hr : 3 ≤ primeRank 3 (P × A) := by
    apply primeRank_ge_of_elementary_embedding (A := P × C)
      (f := (MonoidHom.id P).prodMap C.subtype)
    · intro a
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 P) a.1
      · change a.2 ^ 3 = 1
        simpa only [hc] using pow_card_eq_one' (x := a.2)
    · rw [Nat.card_prod, hP, hc]
      norm_num
    · intro a b h
      apply Prod.ext
      · exact congrArg (fun x : P × A => x.1) h
      · exact Subtype.ext (congrArg (fun x : P × A => x.2) h)
  let D := alternatingGroup.kleinFour (Fin 4)
  let : D.Normal := alternatingGroup.normal_kleinFour (by simp)
  let Q : Subgroup (P × A) := (⊥ : Subgroup P).prod D
  have hq : Nat.card Q = 4 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, one_mul]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hq
    contradiction
  exact hr.trans (Theory.Quasithin.primeRank_le_twoLocalPrimeRank_of_embedding
    f hf Q hne (IsPGroup.of_card (n := 2) hq) 3)

/-- Commuting copies of A₆ supply a genuine two-local rank-three witness. -/
theorem three_le_twoLocalPrimeRank_of_commuting_a6
    {G : Type*} [Group G] [Finite G] (K L : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 6)) (eL : L ≃* alternatingGroup (Fin 6))
    (hc : K ≤ centralizer (L : Set G)) : 3 ≤ twoLocalPrimeRank 3 G := by
  have hdisj : Disjoint K L := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    have haz : (⟨a, ha.1⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      exact (hc k.property a ha.2).symm
    have hez := (Subgroup.centerCongr eK ⟨⟨a, ha.1⟩, haz⟩).property
    change eK ⟨a, ha.1⟩ ∈ center (alternatingGroup (Fin 6)) at hez
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    have haone : (⟨a, ha.1⟩ : K) = 1 := eK.injective (hez.trans eK.map_one.symm)
    exact congrArg Subtype.val haone
  obtain ⟨P, hP, hp⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv eK
  let := hP
  have hcomm : ∀ k : K, ∀ l : L, Commute (k : G) (l : G) :=
    fun k l => (hc k.property l l.property).symm
  let m : K × L →* G := K.subtype.noncommCoprod L.subtype hcomm
  have hm : Function.Injective m := Subgroup.mul_injective_of_disjoint hdisj
  let j : P × alternatingGroup (Fin 4) →* K × L :=
    P.subtype.prodMap (eL.symm.toMonoidHom.comp a4Embedding)
  have hj : Function.Injective j := by
    intro a b h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact a4Embedding_injective (eL.symm.injective (congrArg Prod.snd h))
  exact three_le_localRank_of_nine_prod_a4_embedding hp (m.comp j) (hm.comp hj)

/-- Two A₆ subgroups cannot commute in a quasithin group. -/
theorem not_commuting_a6_of_quasithin
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    (K L : Subgroup G) (eK : K ≃* alternatingGroup (Fin 6))
    (eL : L ≃* alternatingGroup (Fin 6)) : ¬ K ≤ centralizer (L : Set G) := by
  intro hc
  have hge := three_le_twoLocalPrimeRank_of_commuting_a6 K L eK eL hc
  have hle := isQuasithin_iff_twoLocalPrimeRank.mp hG 3 (by decide) (by decide)
  omega

/-- An A₆ component of a quasithin group is normal: otherwise it commutes
with a distinct conjugate, contradicting the embedded E₉ × A₄ obstruction. -/
theorem normal_of_component_a6_of_quasithin
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    (K : Subgroup G) (eK : K ≃* alternatingGroup (Fin 6))
    (hK : Theory.GroupTheory.IsComponent G K) : K.Normal := by
  apply (Subgroup.normalizer_eq_top_iff).mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := hK.commutator_eq_bot_of_ne (hK.map_conj g) (Ne.symm he)
  exact not_commuting_a6_of_quasithin hG K (K.map (MulAut.conj g).toMonoidHom)
    eK (((MulAut.conj g).subgroupMap K).symm.trans eK)
    (commutator_eq_bot_iff_le_centralizer.mp hc)

end alternatingGroup
