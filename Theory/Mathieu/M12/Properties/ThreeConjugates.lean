module

public import Theory.Mathieu.M12.Properties.ThreeConjugates.Fusion

/-!
# Three inner conjugates generate the inner automorphisms of M₁₂

Every involution of the concrete degree-24 automorphism carrier is conjugate
into its proved Sylow two-subgroup. The exhaustive coordinate check reduces it
to three representatives, each with two inner conjugators whose triple contains
both inner generators. Normality preserves the inner-conjugator requirement
under ambient conjugacy, and the marked automorphism equivalence transports the
literal subgroup containment to the Witt-design M₁₂.

This proves the concrete generation input to the source degree-at-most-24
reduction for Aschbacher–Smith Chapter K, printed pp.451 and 457. It uses no
representation classification or identification of outer fixed subgroups.
Generator provenance is ATLAS M12d2G1-p24B0, retained in `Extension.Seeds`;
all finite word and fusion identities are checked by Lean's kernel.
-/

public section
namespace Sporadic.Mathieu.M12ThreeConjugates
open M12ExceptionalExtension Subgroup

/-- Every involution of the actual automorphism carrier has the required
triple, with both conjugators in its literal inner subgroup. -/
theorem carrier_generates (t : Carrier) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Generates t := by
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P
    (SecondCoordinates.commonSylow innerModel)
  have hmem : MulAut.conj g t ∈ overlap := by
    have he := (P.equivSMul g ⟨t, hP (mem_zpowers t)⟩).property
    change MulAut.conj g t ∈ (g • P : Sylow 2 Carrier) at he
    rw [hg] at he
    exact he
  have hn : MulAut.conj g t ≠ 1 := by
    intro h
    apply ht
    exact (MulAut.conj g).injective (h.trans (map_one _).symm)
  have hsq : (MulAut.conj g t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  exact generates_of_isConj (sylow_generates ⟨_, hmem⟩ hn hsq)
    (isConj_iff.mpr ⟨g, rfl⟩).symm

end Sporadic.Mathieu.M12ThreeConjugates

namespace Sporadic.Mathieu

/-- Every nonidentity involutory automorphism of M₁₂ and two conjugates by
inner automorphisms generate a subgroup containing all inner automorphisms. -/
theorem m12_threeConjugateAutomorphisms :
    Theory.GroupTheory.ThreeConjugateAutomorphisms M12 :=
  M12ThreeConjugates.automorphisms_of_carrier M12ThreeConjugates.carrier_generates

end Sporadic.Mathieu
