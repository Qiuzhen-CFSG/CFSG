module
public import Theory.Quasithin
public import Mathlib.Order.Preorder.Finite
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Prime rank and the quasithin invariant

For a finite group, prime rank is monotone under embeddings and invariant under
isomorphism. Every 2-local is contained in a maximal 2-local, so bounding `e G`
is equivalent to bounding all odd-prime ranks of all 2-locals. Thus `IsQuasithin G`
is precisely strong quasithinness of its 2-locals. Empty families are handled by
the bottom-valued natural-number supremum.

The subgroup argument maps abelian prime subgroups injectively. For `e`, it
places each subgroup normalizer inside an ambient normalizer. The quotient
argument uses Schur–Zassenhaus in the inverse image of an abelian prime subgroup;
it requires the kernel order to be coprime to the prime. No unrestricted
quotient or section monotonicity of prime rank is asserted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §0.1 and the opening of §A.2; the normal 2-subgroup
quotient bounds support the reductions in §A.3. The subgroup and complement
arguments also appear in this repository in
`FeitThompson/BGsection8/theorem_8_1.lean` and
`FeitThompson/BGsection10/theorem_10_2_a.lean`. They are given here at the reusable
Theory layer, using the existing definitions of `primeRank` and `e` directly.
-/

@[expose] public section
open scoped IsMulCommutative

variable {G H : Type*} [Group G] [Group H]

/-- A finite group has at most its cardinality many generators. -/
theorem Group.rank_le_nat_card [Finite G] : Group.rank G ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  simpa using (Group.rank_le (G := G) (S := Finset.univ) (by simp))

/-- The natural-number supremum defining prime rank is bounded for a finite group. -/
theorem primeRank_bddAbove (p : ℕ) (G : Type*) [Group G] [Finite G] :
    BddAbove {n : ℕ | ∃ A : Subgroup G, IsPGroup p A ∧ IsMulCommutative A ∧
      ∃ hA : Group.FG A, n ≤ @Group.rank A inferInstance hA} := by
  refine ⟨Nat.card G, ?_⟩
  rintro n ⟨A, _, _, hA, hn⟩
  exact hn.trans (Group.rank_le_nat_card.trans (Subgroup.card_le_card_group A))

/-- Specification of an upper bound on prime rank. -/
theorem primeRank_le_iff [Finite G] (p r : ℕ) :
    primeRank p G ≤ r ↔ ∀ A : Subgroup G, IsPGroup p A → IsMulCommutative A →
      Group.rank A ≤ r := by
  constructor
  · intro h A hp hc
    exact (le_csSup (primeRank_bddAbove p G) ⟨A, hp, hc, inferInstance, le_rfl⟩).trans h
  · intro h
    apply csSup_le
    · exact ⟨0, ⊥, IsPGroup.of_bot, inferInstance, inferInstance, Nat.zero_le _⟩
    · rintro n ⟨A, hp, hc, hA, hn⟩
      exact hn.trans (h A hp hc)

/-- Prime rank is bounded by group order. -/
theorem primeRank_le_nat_card [Finite G] (p : ℕ) : primeRank p G ≤ Nat.card G :=
  (primeRank_le_iff p _).2 fun A _ _ ↦
    Group.rank_le_nat_card.trans (Subgroup.card_le_card_group A)

/-- Injective homomorphisms cannot increase prime rank. -/
theorem primeRank_le_of_injective [Finite G] [Finite H] (p : ℕ)
    (f : G →* H) (hf : Function.Injective f) : primeRank p G ≤ primeRank p H := by
  apply (primeRank_le_iff p _).2
  intro A hp hc
  let := hc
  have he := Group.rank_congr (Subgroup.equivMapOfInjective A f hf)
  rw [he]
  exact le_csSup (primeRank_bddAbove p H)
    ⟨A.map f, hp.map f, inferInstance, inferInstance, le_rfl⟩

/-- Prime rank is invariant under group isomorphism. -/
theorem primeRank_congr [Finite G] [Finite H] (p : ℕ) (f : G ≃* H) :
    primeRank p G = primeRank p H :=
  le_antisymm (primeRank_le_of_injective p f.toMonoidHom f.injective)
    (primeRank_le_of_injective p f.symm.toMonoidHom f.symm.injective)

/-- Prime rank of a subgroup is bounded by ambient prime rank. -/
theorem primeRank_subgroup_le [Finite G] (p : ℕ) (A : Subgroup G) :
    primeRank p A ≤ primeRank p G :=
  primeRank_le_of_injective p A.subtype A.subtype_injective

/-- Prime rank is monotone on the subgroup lattice. -/
theorem primeRank_mono [Finite G] (p : ℕ) {A B : Subgroup G} (h : A ≤ B) :
    primeRank p A ≤ primeRank p B :=
  primeRank_le_of_injective p (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

/-- Every 2-local in a finite group is contained in a maximal 2-local. -/
theorem IsTwoLocal.exists_le_maximal [Finite G] {L : Subgroup G} (hL : IsTwoLocal L) :
    ∃ M : Subgroup G, L ≤ M ∧ M ∈ calM G :=
  Finite.exists_le_maximal hL

/-- Boundedness needed for the natural-number supremum defining `e`. -/
theorem e_bddAbove (G : Type*) [Group G] [Finite G] :
    BddAbove {n : ℕ | ∃ M : Subgroup G, M ∈ calM G ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ n ≤ primeRank p M} := by
  refine ⟨Nat.card G, ?_⟩
  rintro n ⟨M, _, p, _, _, hn⟩
  exact hn.trans ((primeRank_le_nat_card p).trans (Subgroup.card_le_card_group M))

/-- An upper bound on `e` can be checked on the maximal 2-locals.
The empty supremum is zero. -/
theorem e_le_iff_maximalTwoLocal [Finite G] (r : ℕ) :
    e G ≤ r ↔ ∀ M : Subgroup G, M ∈ calM G →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ r := by
  constructor
  · intro h M hM p hp ho
    exact (le_csSup (e_bddAbove G) ⟨M, hM, p, hp, ho, le_rfl⟩).trans h
  · intro h
    apply csSup_le'
    rintro n ⟨M, hM, p, hp, ho, hn⟩
    exact hn.trans (h M hM p hp ho)

/-- Maximal 2-local overgroups allow testing `e` on all 2-locals. -/
theorem e_le_iff_twoLocal [Finite G] (r : ℕ) :
    e G ≤ r ↔ ∀ L : Subgroup G, IsTwoLocal L →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ r := by
  rw [e_le_iff_maximalTwoLocal]
  constructor
  · intro h L hL p hp ho
    obtain ⟨M, hLM, hM⟩ := hL.exists_le_maximal
    exact (primeRank_mono p hLM).trans (h M hM p hp ho)
  · intro h M hM
    exact h M hM.1

/-- Source (QT) is equivalent to (SQT) for every 2-local subgroup. -/
theorem isQuasithin_iff_twoLocal [Finite G] :
    IsQuasithin G ↔ ∀ L : Subgroup G, IsTwoLocal L →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 2 :=
  e_le_iff_twoLocal 2

/-- If no 2-local exists, the invariant is the supremum of the empty set, hence zero. -/
theorem e_eq_zero_of_no_twoLocal [Finite G] (h : ∀ L : Subgroup G, ¬ IsTwoLocal L) :
    e G = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (e_le_iff_twoLocal 0).2 fun L hL ↦ (h L hL).elim

/-- A 2-local transports along a group isomorphism. -/
theorem IsTwoLocal.map_equiv {L : Subgroup G} (hL : IsTwoLocal L) (f : G ≃* H) :
    IsTwoLocal (L.map f.toMonoidHom) := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hL
  refine ⟨Q.map f.toMonoidHom, ?_, hp.map f.toMonoidHom, ?_⟩
  · intro h
    apply hQ
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    simpa using h
  · exact Subgroup.map_equiv_normalizer_eq Q f

private theorem e_le_of_equiv [Finite G] [Finite H] (j : G ≃* H) : e G ≤ e H := by
  apply (e_le_iff_twoLocal _).2
  intro L hL p hp ho
  rw [primeRank_congr p (Subgroup.equivMapOfInjective L j.toMonoidHom j.injective)]
  exact (e_le_iff_twoLocal (G := H) _).1 le_rfl _ (hL.map_equiv j) p hp ho

/-- The invariant is unchanged by group isomorphisms. -/
theorem e_congr [Finite G] [Finite H] (f : G ≃* H) : e G = e H :=
  le_antisymm (e_le_of_equiv f) (e_le_of_equiv f.symm)

/-- Quasithinness is invariant under group isomorphism. -/
theorem isQuasithin_congr [Finite G] [Finite H] (f : G ≃* H) :
    IsQuasithin G ↔ IsQuasithin H := by
  unfold IsQuasithin
  rw [e_congr f]

/-- Strong quasithinness, stated without a campaign-specific predicate, descends to subgroups. -/
theorem odd_primeRank_le_two_subgroup [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2) (L : Subgroup G) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 2 :=
  fun p hp ho ↦ (primeRank_subgroup_le p L).trans (h p hp ho)

/-- Strong quasithinness implies quasithinness. -/
theorem isQuasithin_of_odd_primeRank_le_two [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2) : IsQuasithin G :=
  isQuasithin_iff_twoLocal.mpr fun L _ ↦ odd_primeRank_le_two_subgroup h L

/-- Prime rank does not increase on quotienting by a normal subgroup of order
coprime to the prime. Schur–Zassenhaus lifts every abelian prime subgroup. -/
theorem primeRank_quotient_le_of_coprime [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hc : Nat.Coprime p (Nat.card N)) :
    primeRank p (G ⧸ N) ≤ primeRank p G := by
  apply (primeRank_le_iff p _).2
  intro A hAp hAc
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let L : Subgroup G := A.comap q
  let K : Subgroup L := N.subgroupOf L
  have hNL : N ≤ L := by
    intro x hx
    change q x ∈ A
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [hxq]
    exact A.one_mem
  let f : L →* A :=
    { toFun := fun x ↦ ⟨q x, x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y ↦ Subtype.ext (map_mul q (x : G) (y : G)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y.val
    exact ⟨⟨x, by change q x ∈ A; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hk : f.ker = K := by
    ext x
    change (⟨q x, x.property⟩ : A) = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.val
  let j : L ⧸ K ≃* A := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hKcard : Nat.card K = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hKcop : Nat.Coprime (Nat.card K) K.index := by
    rw [hKcard, Subgroup.index_eq_card, Nat.card_congr j.toEquiv]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
    rw [hn]
    exact hc.symm.pow_right n
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hKcop
  let k : A ≃* C := j.symm.trans hC.symm.QuotientMulEquiv
  let B : Subgroup G := C.map L.subtype
  let b : A ≃* B := k.trans (Subgroup.equivMapOfInjective C L.subtype L.subtype_injective)
  have hBp : IsPGroup p B := hAp.of_equiv b
  have hBc : IsMulCommutative B := by
    let := hAc
    refine ⟨⟨fun x y ↦ b.symm.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  rw [Group.rank_congr b]
  exact le_csSup (primeRank_bddAbove p G) ⟨B, hBp, hBc, inferInstance, le_rfl⟩

/-- The corresponding section bound: take a subgroup, then a coprime normal quotient. -/
theorem primeRank_section_le_of_coprime [Finite G] (p : ℕ) [Fact p.Prime]
    (L : Subgroup G) (N : Subgroup L) [N.Normal] (hc : Nat.Coprime p (Nat.card N)) :
    primeRank p (L ⧸ N) ≤ primeRank p G :=
  (primeRank_quotient_le_of_coprime p N hc).trans (primeRank_subgroup_le p L)

/-- The ambient normalizer of an image supplies a 2-local overgroup, even though
images of 2-locals under subgroup inclusions need not themselves be 2-local. -/
theorem e_subgroup_le [Finite G] (U : Subgroup G) : e U ≤ e G := by
  apply (e_le_iff_twoLocal _).2
  rintro L ⟨Q, hQ, hpQ, rfl⟩ p hp ho
  let R : Subgroup G := Q.map U.subtype
  have hR : R ≠ ⊥ := by
    intro h
    apply hQ
    apply Subgroup.map_injective (f := U.subtype) U.subtype_injective
    simpa [R] using h
  have hlocal : IsTwoLocal (Subgroup.normalizer (R : Set G)) :=
    ⟨R, hR, hpQ.map U.subtype, rfl⟩
  calc
    primeRank p (Subgroup.normalizer (Q : Set U)) =
        primeRank p ((Subgroup.normalizer (Q : Set U)).map U.subtype) :=
      primeRank_congr p (Subgroup.equivMapOfInjective _ U.subtype U.subtype_injective)
    _ ≤ primeRank p (Subgroup.normalizer (R : Set G)) :=
      primeRank_mono p (Subgroup.le_normalizer_map U.subtype)
    _ ≤ e G := (e_le_iff_twoLocal _).1 le_rfl _ hlocal p hp ho

/-- Quasithinness passes to subgroups. -/
theorem IsQuasithin.subgroup [Finite G] (h : IsQuasithin G) (U : Subgroup G) :
    IsQuasithin U :=
  (e_subgroup_le U).trans h

/-- Strong quasithinness passes to normal quotients whose kernel is coprime to
each odd prime. In particular this covers normal 2-subgroups. -/
theorem odd_primeRank_le_two_quotient [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (N : Subgroup G) [N.Normal]
    (hc : ∀ p : ℕ, p.Prime → Odd p → Nat.Coprime p (Nat.card N)) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p (G ⧸ N) ≤ 2 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_coprime p N (hc p hp ho)).trans (h p hp ho)

/-- Odd-prime rank decreases on taking a quotient by a normal 2-subgroup. -/
theorem primeRank_quotient_le_of_isTwoGroup [Finite G] (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) :
    primeRank p (G ⧸ N) ≤ primeRank p G := by
  apply primeRank_quotient_le_of_coprime
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

/-- Strong quasithinness passes to a section with normal 2-group kernel. -/
theorem odd_primeRank_le_two_section_of_isTwoGroup [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (U : Subgroup G) (N : Subgroup U) [N.Normal] (hN : IsPGroup 2 N) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p (U ⧸ N) ≤ 2 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho N hN).trans
    ((primeRank_subgroup_le p U).trans (h p hp ho))

/-- Group rank is bounded by the cardinality. -/
theorem groupRank_le_nat_card [Finite G] : groupRank G ≤ Nat.card G := by
  apply csSup_le'
  rintro n ⟨p, _, hn⟩
  exact hn.trans (primeRank_le_nat_card p)

/-- Each prime rank is bounded by the group rank. -/
theorem primeRank_le_groupRank [Finite G] (p : ℕ) (hp : p.Prime) :
    primeRank p G ≤ groupRank G := by
  unfold groupRank
  refine le_csSup ?_ ⟨p, hp, le_rfl⟩
  refine ⟨Nat.card G, ?_⟩
  rintro n ⟨q, _, hn⟩
  exact hn.trans (primeRank_le_nat_card q)

/-- Group rank cannot increase under an injective homomorphism. -/
theorem groupRank_le_of_injective [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) : groupRank G ≤ groupRank H := by
  apply csSup_le'
  rintro n ⟨p, hp, hn⟩
  exact hn.trans ((primeRank_le_of_injective p f hf).trans (primeRank_le_groupRank p hp))

/-- Group rank is invariant under group isomorphism. -/
theorem groupRank_congr [Finite G] [Finite H] (f : G ≃* H) :
    groupRank G = groupRank H :=
  le_antisymm (groupRank_le_of_injective f.toMonoidHom f.injective)
    (groupRank_le_of_injective f.symm.toMonoidHom f.symm.injective)

/-- The set of maximal 2-locals is empty exactly when there are no 2-locals. -/
theorem calM_eq_empty_iff [Finite G] :
    calM G = ∅ ↔ ∀ L : Subgroup G, ¬ IsTwoLocal L := by
  constructor
  · intro h L hL
    obtain ⟨M, _, hM⟩ := hL.exists_le_maximal
    simp [h] at hM
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun M hM ↦ h M hM.1

/-- Explicit evaluation of the empty supremum in the definition of `e`. -/
theorem e_eq_zero_of_calM_eq_empty [Finite G] (h : calM G = ∅) : e G = 0 := by
  simp [e, h]

/-- Surjective homomorphisms with kernel coprime to the prime do not increase prime rank. -/
theorem primeRank_le_of_surjective_of_coprime [Finite G] [Finite H]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : Nat.Coprime p (Nat.card f.ker)) : primeRank p H ≤ primeRank p G := by
  rw [← primeRank_congr p (QuotientGroup.quotientKerEquivOfSurjective f hf)]
  exact primeRank_quotient_le_of_coprime p f.ker hc
