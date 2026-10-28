module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Lifts
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Counting genuine local factors by prime rank

Independent action images and faithfulness on each factor imply independence
of the factors themselves. From a commuting family of cyclic lifts we choose
one subgroup of order p in each lift. Their multiplication map is injective,
and its image lies in N_G(U). Quasithinness bounds this elementary abelian
subgroup's rank by two.

The existence of commuting cyclic lifts is deliberately separate from this
rank calculation: commuting images do not imply commuting lifts.
Source: Aschbacher–Smith, E.6.25, printed p.255 (PDF p.266).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A genuine family of cyclic subgroups in N_G(V), also lying in N_G(U).
This is a construction target, not an assertion that lifts exist. -/
structure CyclicLifts {V : Subgroup G} [IsElementaryAbelian 2 V]
    (U X : Subgroup G)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X)) where
  subgroup : Fin D.size → Subgroup (normalizer (V : Set G))
  local_containment : ∀ i, (subgroup i).map (normalizer (V : Set G)).subtype ≤
    normalizer (U : Set G)
  cyclic : ∀ i, IsCyclic (subgroup i)
  card_eq : ∀ i, Nat.card (subgroup i) = Nat.card X
  faithful : ∀ i, Function.Injective
    (V.normalizerMonoidHom.rangeRestrict.comp (subgroup i).subtype)
  image_le : ∀ i, (subgroup i).map V.normalizerMonoidHom.rangeRestrict ≤ D.factor i
  commuting : Pairwise fun i j => ∀ a ∈ subgroup i, ∀ b ∈ subgroup j, Commute a b

private theorem independent_of_images {A B : Type*} [Group A] [Group B]
    {ι : Type*} (C : ι → Subgroup A) (f : A →* B)
    (hind : iSupIndep fun i => (C i).map f)
    (hinj : ∀ i, Function.Injective (f.comp (C i).subtype)) : iSupIndep C := by
  intro i
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rintro x ⟨hxi, hxo⟩
  have ho : f x ∈ ⨆ (j) (_ : j ≠ i), (C j).map f := by
    have hm := mem_map_of_mem f hxo
    simpa only [Subgroup.map_iSup] using hm
  have he : f x = 1 := (hind i).le_bot ⟨mem_map_of_mem f hxi, ho⟩
  have hh : (⟨x, hxi⟩ : C i) = 1 := hinj i (by simpa using he)
  exact congrArg Subtype.val hh

/-- Independence is proved from the supplied decomposition and individual faithfulness. -/
theorem CyclicLifts.independent {V U X : Subgroup G} [IsElementaryAbelian 2 V]
    {D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X)}
    (F : CyclicLifts U X D) : iSupIndep F.subgroup :=
  independent_of_images F.subgroup V.normalizerMonoidHom.rangeRestrict
    (D.group_independent.mono F.image_le) F.faithful

variable [Finite G]

/-- The actual local direct product gives the factor bound; this theorem does
not construct the cyclic lifts from the E.6.11 local component. -/
theorem factor_count_le_two_of_cyclicLifts {K : GroupClass} {T : Sylow 2 G}
    {M V U X : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hX : RegularCyclicSection M V U X) (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (F : CyclicLifts U X D) : D.size ≤ 2 := by
  have hcard : 1 < Nat.card X := by
    rw [hX.card_eq]
    have hpow : 2 ^ 2 ≤ 2 ^ subgroupCorank V U :=
      Nat.pow_le_pow_right (by decide) hr
    norm_num at hpow
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  let _ : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    exact (Nat.not_even_iff_odd.mpr (regularCyclicSection_odd hX (by omega)))
      (even_iff_two_dvd.mpr hpd))
  let N := normalizer (V : Set G)
  choose a ha using fun i => exists_prime_orderOf_dvd_card' (G := F.subgroup i) p
    (by rw [F.card_eq i]; exact hpd)
  let E (i : Fin D.size) : Subgroup N := (zpowers (a i)).map (F.subgroup i).subtype
  have hEC (i) : E i ≤ F.subgroup i := map_subtype_le _
  have hEcard (i) : Nat.card (E i) = p := by
    rw [← Nat.card_congr ((zpowers (a i)).equivMapOfInjective
      (F.subgroup i).subtype (F.subgroup i).subtype_injective).toEquiv]
    exact (Nat.card_zpowers (a i)).trans (ha i)
  let _ (i) : IsElementaryAbelian p (E i) := by
    let _ : IsElementaryAbelian p (zpowers (a i)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one ((ha i) ▸ pow_orderOf_eq_one (a i))
    exact IsElementaryAbelian.map (F.subgroup i).subtype
  let _ (i) : CommGroup (E i) := IsMulCommutative.instCommGroup
  have hcomm : Pairwise fun i j => ∀ x y : N, x ∈ E i → y ∈ E j → Commute x y := by
    intro i j hij x y hx hy
    exact F.commuting hij x (hEC i hx) y (hEC j hy)
  let f : (∀ i, E i) →* N := noncommPiCoprod hcomm
  have hfi : Function.Injective f :=
    injective_noncommPiCoprod_of_iSupIndep (F.independent.mono hEC)
  have hfU : ∀ z, ((f z : N) : G) ∈ normalizer (U : Set G) := by
    intro z
    have hz : f z ∈ ⨆ i, E i := by
      rw [← noncommPiCoprod_range (hcomm := hcomm)]
      exact ⟨z, rfl⟩
    have hle : (⨆ i, E i) ≤ (normalizer (U : Set G)).comap N.subtype := by
      apply iSup_le
      intro i x hx
      exact F.local_containment i (mem_map_of_mem N.subtype (hEC i hx))
    exact hle hz
  let fU : (∀ i, E i) →* normalizer (U : Set G) :=
    (N.subtype.comp f).codRestrict (normalizer (U : Set G)) hfU
  have hfUi : Function.Injective fU := by
    intro x y he
    apply hfi
    apply Subtype.ext
    exact congrArg (fun z : normalizer (U : Set G) => (z : G)) he
  have hpow : ∀ z : (∀ i, E i), z ^ p = 1 := by
    intro z
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (E i)) (z i)
  have hc : Nat.card (∀ i, E i) = p ^ D.size := by
    simp only [Nat.card_pi, hEcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hrank : D.size ≤ primeRank p (normalizer (U : Set G)) :=
    primeRank_ge_of_elementary_embedding hpow hc fU hfUi
  have hUp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 V).of_injective
    (inclusion hU.1) (inclusion_injective hU.1)
  exact hrank.trans (isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin
    (normalizer (U : Set G)) ⟨U, hU.2.1, hUp, rfl⟩ p hp hodd)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
