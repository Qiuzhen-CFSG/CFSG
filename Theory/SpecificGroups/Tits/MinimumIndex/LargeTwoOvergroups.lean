module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.Seeds
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups

/-!
# Parabolic placement of subgroups with large two-part

Sylow's first theorem extracts an order-64 subgroup of L. Sylow conjugacy
moves it into the marked subgroup, where the certified finite seed catalogue is
applied. Both conjugations act on the whole L, preserving its cardinality
and index; a final conjugation placing the overgroup is composed in the
correct order.

The final `large_two_subgroup_placement` supplies both certified inputs to
the preserved conditional reduction: exhaustive order-64 seed coverage and
placement of the literal seed overgroups. It proves the exact `hlargeTwo`
input of `MinimumIndex.lean`, with no remaining certificate premises.

Source: the actual Parrott (1972), §5, p.683 Sylow generators and the primary
ATLAS Tits subgroup entry, https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/.
No maximal-subgroup catalogue is assumed.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups
open Subgroup ExceptionalParabolics
open scoped Pointwise

private theorem map_conj_conj (L : Subgroup Atlas1600Group) (g h : Atlas1600Group) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      L.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

/-- Every two-subgroup can be moved into the marked Sylow subgroup. -/
public theorem two_subgroup_conjugate_le_sylow
    (Q : Subgroup Atlas1600Group) (hQ : IsPGroup 2 Q) :
    ∃ g : Atlas1600Group,
      Q.map (MulAut.conj g).toMonoidHom ≤ atlas1600SylowTwoSubgroup := by
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group P atlas1600SylowTwo
  refine ⟨g, ?_⟩
  rw [← atlas1600SylowTwo_coe, ← hg]
  exact Subgroup.map_mono hP

/-- The entire two-group branch already lies in a conjugate of the first parabolic. -/
public theorem two_subgroup_conjugate_le_first
    (L : Subgroup Atlas1600Group) (hL : IsPGroup 2 L) :
    ∃ g : Atlas1600Group, L.map (MulAut.conj g).toMonoidHom ≤ first := by
  obtain ⟨g, hg⟩ := two_subgroup_conjugate_le_sylow L hL
  exact ⟨g, hg.trans sylow_le_first⟩

/-- An order-64 subgroup of L can be moved into the marked Sylow subgroup,
while remaining a subgroup of the same conjugate of L. -/
public theorem exists_order64_in_conjugate
    (L : Subgroup Atlas1600Group) (h64 : 64 ∣ Nat.card L) :
    ∃ (g : Atlas1600Group) (Q : Subgroup Atlas1600Group),
      Nat.card Q = 64 ∧ Q ≤ atlas1600SylowTwoSubgroup ∧
      Q ≤ L.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := L) 2 (n := 6) h64
  let R' := R.map L.subtype
  have hc : Nat.card R' = 64 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hR
  obtain ⟨g, hg⟩ := two_subgroup_conjugate_le_sylow R'
    (IsPGroup.of_card (n := 6) hc)
  refine ⟨g, R'.map (MulAut.conj g).toMonoidHom, ?_, hg, ?_⟩
  · rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  · exact Subgroup.map_mono (Subgroup.map_subtype_le R)

/-- A certified list inside the marked Sylow subgroup suffices to move an
order-64 subgroup of an arbitrary L onto a listed seed. The same conjugator
is applied to the whole L. -/
public theorem exists_seed_in_conjugate
    (hcover : ∀ Q : Subgroup Atlas1600Group,
      Q ≤ atlas1600SylowTwoSubgroup → Nat.card Q = 64 →
      ∃ (i : Fin 122) (s : atlas1600SylowTwoSubgroup),
        Q.map (MulAut.conj s.val).toMonoidHom = seed i)
    (L : Subgroup Atlas1600Group) (h64 : 64 ∣ Nat.card L) :
    ∃ (g : Atlas1600Group) (i : Fin 122),
      seed i ≤ L.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, Q, hQ, hQS, hQL⟩ := exists_order64_in_conjugate L h64
  obtain ⟨i, s, hs⟩ := hcover Q hQS hQ
  refine ⟨s.val * g, i, ?_⟩
  have hm := Subgroup.map_mono (f := (MulAut.conj s.val).toMonoidHom) hQL
  rwa [hs, map_conj_conj] at hm

/-- Finite seed coverage and their actual overgroup placements imply precisely
the large-two-part input of `MinimumIndex.lean`. The final theorem below
discharges both certificate premises. -/
public theorem placement_of_seed_certificates
    (hcover : ∀ Q : Subgroup Atlas1600Group,
      Q ≤ atlas1600SylowTwoSubgroup → Nat.card Q = 64 →
      ∃ (i : Fin 122) (s : atlas1600SylowTwoSubgroup),
        Q.map (MulAut.conj s.val).toMonoidHom = seed i)
    (hovergroups : ∀ (i : Fin 122) (K : Subgroup Atlas1600Group),
      seed i ≤ K → K ≠ ⊤ → 2 ∣ K.index →
      ¬ 25 ∣ Nat.card K → ¬ 13 ∣ Nat.card K →
      ∃ g : Atlas1600Group,
        K.map (MulAut.conj g).toMonoidHom ≤ first ∨
        K.map (MulAut.conj g).toMonoidHom ≤ second)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (heven : 2 ∣ L.index)
    (h64 : 64 ∣ Nat.card L) (h25 : ¬ 25 ∣ Nat.card L) (h13 : ¬ 13 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ first ∨
      L.map (MulAut.conj g).toMonoidHom ≤ second := by
  obtain ⟨g, i, hseed⟩ := exists_seed_in_conjugate hcover L h64
  let K := L.map (MulAut.conj g).toMonoidHom
  have hi : K.index = L.index := Subgroup.index_map_of_bijective
    (MulAut.conj g).bijective L
  have hc : Nat.card K = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hK : K ≠ ⊤ := by
    intro ht
    apply hL
    apply Subgroup.index_eq_one.mp
    rw [← hi, ht, Subgroup.index_top]
  obtain ⟨h, hh⟩ := hovergroups i K hseed hK (hi.symm ▸ heven)
    (hc.symm ▸ h25) (hc.symm ▸ h13)
  refine ⟨h * g, ?_⟩
  simpa only [K, map_conj_conj] using hh

/-- Every proper even-index subgroup with order divisible by 64, but by
neither 25 nor 13, is conjugate into one of the two marked parabolics.
This discharges the exact `hlargeTwo` premise of the minimum-index reduction. -/
public theorem large_two_subgroup_placement
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (heven : 2 ∣ L.index)
    (h64 : 64 ∣ Nat.card L) (h25 : ¬ 25 ∣ Nat.card L) (h13 : ¬ 13 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ first ∨
      L.map (MulAut.conj g).toMonoidHom ≤ second :=
  placement_of_seed_certificates order64_seed_coverage seed_overgroup_placement
    L hL heven h64 h25 h13

end Tits.MinimumIndex.LargeTwoOvergroups
