module

public import Theory.GroupTheory.PGroup.SymplecticType
public import Theory.GroupTheory.PGroup.NormalFour
public import Theory.GroupTheory.Fitting.PCoreAutomorphisms
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.SemidihedralAut

/-!
# Excluding a Hall factor as a solvable group's two-core

Let a finite solvable group have trivial odd core, an elementary subgroup of
order at least eight, and an elementary four in its two-core, but no normal
elementary four. Then its two-core cannot be a pure binary Hall factor.
The underlying exclusion only needs a nonnormal four in the two-core
and the hypothesis that the ambient group is not a two-group; this also
applies to a nonnormal quotient image of a normal Sylow four.

Cyclic and generalized quaternion groups have no elementary four. In the
order-four dihedral case the given four is the whole core and hence normal.
Every larger dihedral two-group, and every semidihedral group, has a two-group
of automorphisms. Fitting self-centralization then forces the ambient group
to be a two-group, where an elementary eight forces a normal four.
The self-centralizing-core hypothesis is thus supplied by solvability and
trivial odd core and need not be assumed separately.

Sources: GLS2, Chapter C, Sections 10.1–10.11; the elementary dihedral and
semidihedral automorphism calculations and the normal-four theorem.
-/

open Subgroup

private theorem cyclic_of_elementary_quaternion_embedding
    {D : Type*} [Group D] [IsElementaryAbelian 2 D]
    {m : ℕ} (hm : 0 < m) (f : D →* QuaternionGroup m)
    (hf : Function.Injective f) : IsCyclic D := by
  let : NeZero m := ⟨by omega⟩
  have hmem (x : D) : f x ∈ zpowers (QuaternionGroup.a 1 : QuaternionGroup m) := by
    have hx : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 D) x
    have hd : orderOf (f x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
    cases he : f x with
    | a i =>
      have h := pow_mem (mem_zpowers (QuaternionGroup.a 1 : QuaternionGroup m)) i.val
      simpa only [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] using h
    | xa i =>
      rw [he, QuaternionGroup.orderOf_xa] at hd
      norm_num at hd
  exact isCyclic_of_injective (f.codRestrict _ hmem) (fun x y h =>
    hf (congrArg Subtype.val h))

/-- A nonnormal four in the two-core of a solvable odd-core-free group
excludes a pure Hall factor, provided the ambient group is not a two-group. -/
public theorem not_isBinaryHallFactor_pCore_of_not_isPGroup
    {K : Type*} [Group K] [Finite K]
    (hsolv : Group.IsSolvable K) (hodd : pPrimeCore 2 K = ⊥)
    (hnot : ¬ IsPGroup 2 K)
    (D : Subgroup K) [IsElementaryAbelian 2 D]
    (hD : D ≤ pCore 2 K) (hDcard : Nat.card D = 4) (hDn : ¬ D.Normal) :
    ¬ IsBinaryHallFactor (pCore 2 K) := by
  have hnotcyc : ¬ IsCyclic D :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hDcard
  have hnotaut : ¬ IsPGroup 2 (MulAut (pCore 2 K)) := fun haut =>
    hnot (isPGroup_of_pPrimeCore_eq_bot_of_mulAut_pCore hsolv hodd haut)
  intro hHall
  rcases hHall with hcyc | ⟨n, -, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ | ⟨n, hn, hc, a, b, ha, hb, hr, hg⟩
  · let : IsCyclic (pCore 2 K) := hcyc
    exact hnotcyc (isCyclic_of_injective (inclusion hD) (inclusion_injective hD))
  · exact hnotcyc (cyclic_of_elementary_quaternion_embedding (by positivity)
      (e.toMonoidHom.comp (inclusion hD)) (e.injective.comp (inclusion_injective hD)))
  · have hc : Nat.card (pCore 2 K) = 2 * m :=
      (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    by_cases hm : 2 < m
    · exact hnotaut ((DihedralGroup.isPGroup_mulAut_of_two_lt hm
        (pCore_isPGroup.of_equiv e)).of_equiv (MulAut.congr e.symm))
    · have hle := card_le_of_le hD
      have hm2 : m = 2 := by omega
      have heq : D = pCore 2 K := eq_of_le_of_card_ge hD (by omega)
      exact hDn (heq ▸ inferInstance)
  · exact hnotaut (Semidihedral.isPGroup_mulAut hn hc a b ha hb hr hg)

/-- A two-core containing a four-group cannot be a binary Hall factor when the
ambient solvable odd-core-free group has elementary rank at least three and
has no normal four-group. -/
public theorem not_isBinaryHallFactor_pCore_of_elementary_rank_three
    {K : Type*} [Group K] [Finite K]
    (hsolv : Group.IsSolvable K) (hodd : pPrimeCore 2 K = ⊥)
    (E : Subgroup K) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (D : Subgroup K) [IsElementaryAbelian 2 D]
    (hD : D ≤ pCore 2 K) (hDcard : Nat.card D = 4)
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    ¬ IsBinaryHallFactor (pCore 2 K) := by
  apply not_isBinaryHallFactor_pCore_of_not_isPGroup hsolv hodd ?_ D hD hDcard
    (fun hDn => hno D hDn inferInstance hDcard)
  intro hK
  obtain ⟨U, hUn, hUe, hUc⟩ := hK.exists_normal_four_of_elementary_rank_three E hE
  exact hno U hUn hUe hUc
