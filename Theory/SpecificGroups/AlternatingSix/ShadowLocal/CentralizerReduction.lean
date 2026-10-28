module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ElementaryAbelian
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.PGroupCore
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Centralizers of a normal A₆ with a disjoint crossing kernel

Let J have three-rank at most two, with normal K ≅ A₆ and Sylow two-subgroup S.
Suppose C_J(K) has characteristic two and the conjugation action identifies
S/C_S(K) with a Sylow subgroup of Aut(A₆). An automorphism of S carrying
C_S(K) to a disjoint subgroup embeds O₂(C_J(K)) in a normal subgroup of that
actual Sylow subgroup. Its automorphism group has only the primes two and
three. The intrinsic core action gives the same restriction for C_J(K).
The disjoint commuting K factor forces its three-rank to vanish, so C_J(K)
is a two-group and lies in S.

This proves the centralizer step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined 1 March 2004 manuscript, Lemma 2.5.22(2), p.567.
It uses the rank of J, not that of a potentially proper subgroup KS, and
avoids the false unrestricted normal-subgroup dichotomy in the printed proof.
The crossing embedding also transports the rank-one classification used in
2.5.27. Its rank-one and Frattini hypotheses remain explicit.
-/

public section

open Subgroup
open Theory.GroupTheory
namespace AlternatingSix.ShadowLocal

variable {J : Type*} [Group J] [Finite J]

/-- An A₆ factor exhausts the available three-rank; its centralizer has order prime to three. -/
theorem centralizer_three_prime_to (K : Subgroup J) (e : K ≃* A6)
    (hrank : primeRank 3 J ≤ 2) : ¬ 3 ∣ Nat.card (centralizer (K : Set J)) := by
  let C := centralizer (K : Set J)
  have hd : Disjoint K C := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    have haz : (⟨a, ha.1⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (ha.2 k k.property)
    have hez := (Subgroup.centerCongr e ⟨⟨a, ha.1⟩, haz⟩).property
    change e ⟨a, ha.1⟩ ∈ center A6 at hez
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    exact congrArg Subtype.val (e.injective (hez.trans e.map_one.symm))
  have hc : K ≤ centralizer (C : Set J) := by
    intro k hk c hc
    exact (hc k hk).symm
  have hp := K.primeRank_sup_eq_add_of_disjoint_commuting C hd hc 3
  have hle := (Theory.GroupTheory.primeRank_le_of_injective 3 (K ⊔ C).subtype
    (K ⊔ C).subtype_injective).trans hrank
  rw [hp] at hle
  obtain ⟨E, hE, hcard⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv e
  let := hE
  have htwo : 2 ≤ primeRank 3 K :=
    IsElementaryAbelian.primeRank_ge_of_card E hcard
  have hzero : primeRank 3 C = 0 := by omega
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hzero

/-- The crossing automorphism embeds every normal subgroup of the kernel into a normal subgroup of the actual Sylow image. -/
theorem exists_normal_subgroup_equiv_of_crossing
    {S : Type*} [Group S] (P : Sylow 2 AutA6)
    (f : S →* P) (hf : Function.Surjective f)
    (a : MulAut S) (hd : Disjoint f.ker (f.ker.map a.toMonoidHom))
    (Q : Subgroup S) [Q.Normal] (hQ : Q ≤ f.ker) :
    ∃ W : Subgroup P, W.Normal ∧ Nonempty (Q ≃* W) := by
  let R := Q.map a.toMonoidHom
  let W := R.map f
  let : R.Normal := (inferInstance : Q.Normal).map _ a.surjective
  let : W.Normal := (inferInstance : R.Normal).map _ hf
  have hdis : Disjoint f.ker R := hd.mono_right (map_mono hQ)
  have hi : Function.Injective (f.subgroupMap R) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
      Subgroup.subgroupOf_eq_bot]
    exact hdis
  let e : Q ≃* W := (a.subgroupMap Q).trans
    (MulEquiv.ofBijective (f.subgroupMap R) ⟨hi, f.subgroupMap_surjective R⟩)
  exact ⟨W, inferInstance, ⟨e⟩⟩

/-- Transport the proved automorphism-prime restriction through the crossing embedding. -/
theorem normal_subgroup_aut_primes_of_crossing
    {S : Type*} [Group S] (P : Sylow 2 AutA6)
    (f : S →* P) (hf : Function.Surjective f)
    (a : MulAut S) (hd : Disjoint f.ker (f.ker.map a.toMonoidHom))
    (Q : Subgroup S) [Q.Normal] (hQ : Q ≤ f.ker)
    {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card (MulAut Q)) : p = 2 ∨ p = 3 := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_normal_subgroup_equiv_of_crossing P f hf a hd Q hQ
  let := hW
  apply SylowGeometry.normal_subgroup_automorphism_primes P W hp
  rwa [← Nat.card_congr (MulAut.congr e).toEquiv]

/-- Classify a rank-one crossing kernel with nontrivial Frattini subgroup. These are the two explicit incoming conclusions of source 2.5.24 and 2.5.26. -/
theorem rank_one_kernel_classification_of_crossing
    {S : Type*} [Group S] [Finite S] (P : Sylow 2 AutA6)
    (f : S →* P) (hf : Function.Surjective f)
    (a : MulAut S) (hd : Disjoint f.ker (f.ker.map a.toMonoidHom))
    (hrank : primeRank 2 f.ker = 1) (hphi : frattini f.ker ≠ ⊥) :
    Nonempty (f.ker ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (f.ker ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (f.ker ≃* QuaternionGroup 2) := by
  obtain ⟨W, _, ⟨e⟩⟩ := exists_normal_subgroup_equiv_of_crossing P f hf a hd f.ker le_rfl
  have hr : primeRank 2 W = 1 := (primeRank_congr 2 e).symm.trans hrank
  have hWphi : frattini W ≠ ⊥ := by
    intro h
    apply hphi
    have he := e.mapSubgroup.map_radical
    change (frattini f.ker).map e.toMonoidHom = frattini W at he
    exact ((frattini f.ker).map_eq_bot_iff_of_injective e.injective).mp (he.trans h)
  rcases SylowGeometry.rank_one_subgroup_classification P W hr hWphi with h | h | h
  · obtain ⟨v⟩ := h
    exact Or.inl ⟨e.trans v⟩
  · obtain ⟨v⟩ := h
    exact Or.inr (Or.inl ⟨e.trans v⟩)
  · obtain ⟨v⟩ := h
    exact Or.inr (Or.inr ⟨e.trans v⟩)

/-- The intrinsic core and its faithful crossed image force the A₆ centralizer to be a two-group. -/
theorem centralizer_isTwoGroup (K : Subgroup J) [K.Normal] (e : K ≃* A6)
    (S : Sylow 2 J) (hrank : primeRank 3 J ≤ 2)
    (hchar : centralizer (pCore 2 (centralizer (K : Set J)) :
      Set (centralizer (K : Set J))) ≤ pCore 2 (centralizer (K : Set J)))
    (P : Sylow 2 AutA6) (f : S →* P) (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (K : Set J)).subgroupOf S)
    (a : MulAut S) (hd : Disjoint f.ker (f.ker.map a.toMonoidHom)) :
    IsPGroup 2 (centralizer (K : Set J)) := by
  let C := centralizer (K : Set J)
  let Q := (pCore 2 C).map C.subtype
  let : Q.Normal := inferInstanceAs ((pCore 2 C).map C.subtype).Normal
  have hQS : Q ≤ (S : Subgroup J) :=
    (pCore_isPGroup.map C.subtype).le_sylow_of_normal S
  let QS := Q.subgroupOf (S : Subgroup J)
  have hQD : QS ≤ f.ker := by
    rw [hker]
    intro q hq
    exact (map_le_range _ _).trans_eq C.range_subtype hq
  let eQ : pCore 2 C ≃* QS :=
    ((pCore 2 C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (subgroupOfEquivOfLe hQS).symm
  have hAut {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card (MulAut (pCore 2 C))) :
      p = 2 ∨ p = 3 := by
    apply normal_subgroup_aut_primes_of_crossing P f hf a hd QS hQD hp
    rwa [← Nat.card_congr (MulAut.congr eQ).toEquiv]
  let c : C →* MulAut (pCore 2 C) := MulAut.conjNormal
  have hcle : c.ker ≤ pCore 2 C := by
    intro g hg
    apply hchar
    rw [mem_centralizer_iff]
    intro q hq
    have hh := congrArg (fun b : MulAut (pCore 2 C) => (b ⟨q, hq⟩ : C))
      (MonoidHom.mem_ker.mp hg)
    change g * q * g⁻¹ = q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcp : IsPGroup 2 c.ker := pCore_isPGroup.to_le hcle
  have hprimes {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card C) : p = 2 ∨ p = 3 := by
    have hcount := c.ker.card_mul_index
    rw [Subgroup.index_ker] at hcount
    rw [← hcount] at hdiv
    rcases hp.dvd_mul.mp hdiv with hk | hi
    · obtain ⟨n, hn⟩ := hcp.exists_card_eq
      rw [hn] at hk
      exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp
        (hp.dvd_of_dvd_pow hk)).symm
    · exact hAut hp (hi.trans c.range.card_subgroup_dvd_card)
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  rcases hprimes hprime hdiv with h2 | h3
  · simpa [h2] using Nat.prime_two
  · exact False.elim (centralizer_three_prime_to K e hrank (h3 ▸ hdiv))

/-- Apply the centralizer theorem to the actual conjugation action, constructing its Sylow image and verifying its kernel. -/
theorem centralizer_isTwoGroup_of_conjugation
    (K : Subgroup J) [K.Normal] (e : K ≃* A6)
    (S : Sylow 2 J) (hrank : primeRank 3 J ≤ 2)
    (hchar : centralizer (pCore 2 (centralizer (K : Set J)) :
      Set (centralizer (K : Set J))) ≤ pCore 2 (centralizer (K : Set J)))
    (hsurj : Function.Surjective (conjugationAction K e))
    (a : MulAut S)
    (hd : Disjoint ((centralizer (K : Set J)).subgroupOf S)
      (((centralizer (K : Set J)).subgroupOf S).map a.toMonoidHom)) :
    IsPGroup 2 (centralizer (K : Set J)) := by
  let P := conjugationSylow K e hsurj S
  let f : S →* P := (conjugationAction K e).subgroupMap (S : Subgroup J)
  have hf : Function.Surjective f := (conjugationAction K e).subgroupMap_surjective _
  have hker : f.ker = (centralizer (K : Set J)).subgroupOf S := by
    change ((conjugationAction K e).subgroupMap (S : Subgroup J)).ker = _
    rw [Subgroup.ker_subgroupMap, conjugationAction_ker]
  exact centralizer_isTwoGroup K e S hrank hchar P f hf hker a (hker ▸ hd)

/-- A centralizer supplement collapses into S. No later Frattini or involution-fusion conclusions enter this proof. -/
theorem generated_eq_top_of_centralizer_supplement
    (K : Subgroup J) [K.Normal] (e : K ≃* A6)
    (S : Sylow 2 J) (hrank : primeRank 3 J ≤ 2)
    (hchar : centralizer (pCore 2 (centralizer (K : Set J)) :
      Set (centralizer (K : Set J))) ≤ pCore 2 (centralizer (K : Set J)))
    (hsurj : Function.Surjective (conjugationAction K e))
    (a : MulAut S)
    (hd : Disjoint ((centralizer (K : Set J)).subgroupOf S)
      (((centralizer (K : Set J)).subgroupOf S).map a.toMonoidHom))
    (hgen : K ⊔ (S : Subgroup J) ⊔ centralizer (K : Set J) = ⊤) :
    K ⊔ (S : Subgroup J) = ⊤ := by
  have hC := centralizer_isTwoGroup_of_conjugation K e S hrank hchar hsurj a hd
  have hCS := hC.le_sylow_of_normal S
  rwa [sup_eq_left.mpr (hCS.trans le_sup_right)] at hgen

/-- An inner involution in the automorphism image has Sylow centralizer; pull this back through a kernel contained in S. -/
theorem centralizer_eq_sylow_of_inner_image
    (f : J →* AutA6) (hf : Function.Surjective f) (S : Sylow 2 J)
    (hker : f.ker ≤ (S : Subgroup J)) (z : J)
    (hz : (S : Subgroup J) ≤ centralizer ({z} : Set J))
    (ho : orderOf (f z) = 2) (hi : f z ∈ inner) :
    centralizer ({z} : Set J) = (S : Subgroup J) := by
  let P := S.mapSurjective hf
  obtain ⟨Q, hQ⟩ := inner_involution_centralizer_sylow (f z) ho hi
  have hPQ : (P : Subgroup AutA6) ≤ Q := by
    rintro b ⟨s, hs, rfl⟩
    rw [hQ, mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hz hs))
  have heq : (Q : Subgroup AutA6) = P := P.is_maximal' Q.isPGroup' hPQ
  apply le_antisymm _ hz
  intro j hj
  have hjP : f j ∈ (P : Subgroup AutA6) := by
    rw [← heq, hQ, mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hj)
  have hpre : (P : Subgroup AutA6).comap f = S := by
    change ((S : Subgroup J).map f).comap f = _
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  exact hpre ▸ hjP

end AlternatingSix.ShadowLocal
