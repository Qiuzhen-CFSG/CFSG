module

public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow


/-!
# Prime-field PSL₂ two-ranks

For a prime p > 3, coefficient automorphisms are trivial. The proved
semilinear coverage therefore identifies Aut(PSL₂(p)) with PGL₂(p).
Both have dihedral Sylow two-subgroups; a Klein four in a PSL₂ Sylow
subgroup gives equality for its two-rank and the automorphism upper bound
is two. This includes the primes five and seven.

Source: Aschbacher–Smith, 16.1.5 and 16.3.9, printed pp.1171–1172, 1180.
The projective automorphism action and Sylow identifications are the
actual matrix equivalences proved in the imported Gorenstein–Walter modules.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
open GorensteinWalter

/-- The full automorphism group of prime-field PSL₂ has two-rank at most two. -/
theorem primeField_automorphism_two_rank {p : ℕ} [Fact p.Prime] (hlarge : 3 < p) :
    primeRank 2 (MulAut PSL(2, ZMod p)) ≤ 2 := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  let : Finite (PGL2 (ZMod p)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let e : PGL2 (ZMod p) ≃* MulAut PSL(2, ZMod p) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 (ZMod p) hK hc)
      ⟨pgl2InnerAutPSL2_injective (ZMod p) hK hc, primeField_pgl_coverage hp hlarge⟩
  rw [← primeRank_equiv 2 e]
  let P : Sylow 2 (PGL2 (ZMod p)) := Classical.choice inferInstance
  obtain ⟨n, _, ⟨eP⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model (ZMod p) hK P
  rw [P.primeRank_eq, primeRank_equiv 2 eP]
  exact dihedral_rank_le_two n

/-- The two-rank of prime-field PSL₂ is exactly two. -/
theorem primeField_two_rank {p : ℕ} [Fact p.Prime] (hlarge : 3 < p) :
    primeRank 2 PSL(2, ZMod p) = 2 := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  let P : Sylow 2 PSL(2, ZMod p) := Classical.choice inferInstance
  obtain ⟨n, hn, ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod p) hK P
  apply le_antisymm
  · rw [P.primeRank_eq, primeRank_equiv 2 eP]
    exact dihedral_rank_le_two n
  · obtain ⟨V, _, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (P : Subgroup PSL(2, ZMod p)) hn eP
    let : IsElementaryAbelian 2 V := {
      toIsMulCommutative := by
        let : IsKleinFour V := hV
        exact IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV.exponent_two] }
    exact IsElementaryAbelian.primeRank_ge_of_card V hV.card_four

end Theory.PSL2
