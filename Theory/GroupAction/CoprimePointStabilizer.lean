module
public import Theory.GroupTheory.Hall.OddSylowComplement
public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.Nilpotent

/-!
# Odd complements fixing a point

If a normal Sylow two-subgroup has the same point orbit as its finite
solvable overgroup, an odd complement can be chosen in the point stabilizer.
Choose a complement to the stabilizer's Sylow and use the orbit condition
to factor every group element. Hall conjugacy then moves any prescribed
complement into that stabilizer by an element of the original Sylow.

The ambient version applies to a normalized product Q K. Its conjugator
lies in Q, and its conclusion uses literal conjugation in the original
group. The ambient group itself need not be finite.

Source application: DGS, Groups and Graphs (1985), 12.3(a), p.179, the
choices of an edge complement and its middle-core conjugate. The graph
application is CommutingThreeProfile.ComplementSelection.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupAction
variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

/-- Choose the complement inside the actual point stabilizer. -/
theorem exists_complement_fixing_point (T : Sylow 2 G) [(T : Subgroup G).Normal]
    (hsolv : Group.IsSolvable G) (x : X)
    (horbit : ∀ g : G, ∃ t ∈ (T : Subgroup G), t • x = g • x) :
    ∃ K : Subgroup G, K ≤ MulAction.stabilizer G x ∧
      Odd (Nat.card K) ∧ (T : Subgroup G).IsComplement' K := by
  let D := MulAction.stabilizer G x
  let R : Sylow 2 D := default
  let := hsolv
  have hR : (R : Subgroup D).map D.subtype ≤ (T : Subgroup G) := by
    have he := T.is_maximal' ((R.isPGroup'.map D.subtype).to_sup_of_normal_right
      T.isPGroup') le_sup_right
    exact le_sup_left.trans he.le
  obtain ⟨C, hodd, hC⟩ := exists_odd_complement_sylow_two
    (inferInstance : Group.IsSolvable D) R
  let K := C.map D.subtype
  have hKodd : Odd (Nat.card K) := by
    rw [← Nat.card_congr (C.equivMapOfInjective D.subtype D.subtype_injective).toEquiv]
    exact hodd
  have hdis : Disjoint (T : Subgroup G) K := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (Nat.coprime_two_left.mpr hKodd).pow_left n
  refine ⟨K, map_subtype_le _, hKodd, mul_injective_of_disjoint hdis, ?_⟩
  intro g
  obtain ⟨t, ht, htx⟩ := horbit g
  have hd : t⁻¹ * g ∈ D := by
    change (t⁻¹ * g) • x = x
    rw [mul_smul, ← htx, inv_smul_smul]
  obtain ⟨⟨r, c⟩, hrc⟩ := hC.2 ⟨t⁻¹ * g, hd⟩
  refine ⟨(⟨t * (r.val : G), T.mul_mem ht (hR (mem_map_of_mem _ r.property))⟩,
    ⟨c.val, mem_map_of_mem _ c.property⟩), ?_⟩
  have he := congrArg (fun d : D => (d : G)) hrc
  change (r.val : G) * (c.val : G) = t⁻¹ * g at he
  change (t * (r.val : G)) * (c.val : G) = g
  rw [mul_assoc, he, mul_inv_cancel_left]

/-- Move a prescribed complement by an element of the normal Sylow. -/
theorem exists_sylow_conjugate_fixing_point (T : Sylow 2 G)
    [(T : Subgroup G).Normal] (hsolv : Group.IsSolvable G) (x : X)
    (horbit : ∀ g : G, ∃ t ∈ (T : Subgroup G), t • x = g • x)
    (K : Subgroup G) (hK : (T : Subgroup G).IsComplement' K) :
    ∃ t ∈ (T : Subgroup G), K.map (MulAut.conj t).toMonoidHom ≤
      MulAction.stabilizer G x := by
  obtain ⟨C, hCx, _, hC⟩ := exists_complement_fixing_point T hsolv x horbit
  have hall (A : Subgroup G) (hA : (T : Subgroup G).IsComplement' A) :
      IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} A := by
    refine ⟨?_, ?_⟩
    · intro p hp he
      have hp2 : p.val = 2 := he
      rw [← hA.symm.index_eq_card, hp2] at hp
      exact T.not_dvd_index hp
    · intro p hp hp2
      rw [hA.index_eq_card] at hp
      obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
      rw [hn] at hp
      exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv (hall K hK) (hall C hC)
  obtain ⟨⟨t, k⟩, htk⟩ := hK.2 g
  refine ⟨t, t.property, ?_⟩
  rintro a ⟨b, hb, rfl⟩
  have hmem : (g * ((k : G)⁻¹ * b * (k : G)) * g⁻¹) ∈ C := by
    rw [hg]
    exact mem_map_of_mem _ (K.mul_mem (K.mul_mem (K.inv_mem k.property) hb) k.property)
  apply hCx
  convert hmem using 1
  rw [← htk]
  change (t : G) * b * (t : G)⁻¹ = _
  group

omit [Finite G] in
/-- The conjugator stays in the specified two-group in the original ambient group. -/
theorem exists_two_group_conjugate_fixing_point
    (Q K : Subgroup G) [Finite (Q ⊔ K : Subgroup G)]
    (hQ : IsPGroup 2 Q) (hodd : Odd (Nat.card K)) (hsolv : Group.IsSolvable K)
    (hn : K ≤ normalizer (Q : Set G)) (x : X)
    (horbit : ∀ k ∈ K, ∃ q ∈ Q, q • x = k • x) :
    ∃ q ∈ Q, K.map (MulAut.conj q).toMonoidHom ≤ MulAction.stabilizer G x := by
  let J := Q ⊔ K
  let Q' := Q.subgroupOf J
  let K' := K.subgroupOf J
  have hQJ : Q ≤ J := le_sup_left
  have hKJ : K ≤ J := le_sup_right
  let : Finite Q := Finite.of_injective (inclusion hQJ) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKJ) (inclusion_injective _)
  let : Q'.Normal := normal_subgroupOf_of_le_normalizer (sup_le Q.le_normalizer hn)
  have hQ' : IsPGroup 2 Q' := hQ.comap_subtype
  have ho : Odd (Nat.card K') := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKJ).toEquiv]
    exact hodd
  have hd : Disjoint Q' K' := by
    obtain ⟨n, hn⟩ := hQ'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (Nat.coprime_two_left.mpr ho).pow_left n
  have hsup : Q' ⊔ K' = ⊤ := by
    rw [← subgroupOf_sup hQJ hKJ]
    exact subgroupOf_self _
  have hc : Q'.IsComplement' K' := by
    refine ⟨mul_injective_of_disjoint hd, ?_⟩
    intro j
    have hj : j ∈ Q' ⊔ K' := hsup ▸ mem_top j
    obtain ⟨q, hq, k, hk, he⟩ := mem_sup_of_normal_left.mp hj
    exact ⟨(⟨q, hq⟩, ⟨k, hk⟩), he⟩
  let T : Sylow 2 J := hQ'.toSylow (by
    rw [hc.symm.index_eq_card]
    exact Nat.not_even_iff_odd.mpr ho ∘ even_iff_two_dvd.mpr)
  let : (T : Subgroup J).Normal := (inferInstance : Q'.Normal)
  let : Group.IsSolvable K := hsolv
  let := hQ.isNilpotent
  have hJsolv : Group.IsSolvable J := Group.isSolvable_sup_of_normalizes Q K hn
  have hJorbit : ∀ j : J, ∃ t ∈ (T : Subgroup J), t • x = j • x := by
    intro j
    obtain ⟨⟨q, k⟩, hqk⟩ := hc.2 j
    obtain ⟨a, ha, hax⟩ := horbit (k.val : G) k.property
    refine ⟨⟨(q.val : G) * a, hQJ (Q.mul_mem q.property ha)⟩,
      Q.mul_mem q.property ha, ?_⟩
    change ((q.val : G) * a) • x = (j : G) • x
    have he := congrArg (fun j : J => (j : G)) hqk
    change (q.val : G) * (k.val : G) = (j : G) at he
    rw [← he, mul_smul, mul_smul, hax]
  obtain ⟨q, hq, hfix⟩ := exists_sylow_conjugate_fixing_point T hJsolv x hJorbit K' hc
  refine ⟨q, hq, ?_⟩
  rintro a ⟨k, hk, rfl⟩
  exact hfix (mem_map_of_mem (MulAut.conj q).toMonoidHom
    (show (⟨k, hKJ hk⟩ : J) ∈ K' from hk))

end Theory.GroupAction
