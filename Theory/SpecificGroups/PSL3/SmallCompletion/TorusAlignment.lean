module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Aligning a torus image inside the actual projective Borel

The projective Borel is solvable: its two-core is unipotent and its quotient
is the two-parameter torus modulo the full cubic scalar kernel. The native
torus is a Hall complement. Hall conjugacy therefore moves its image under
any Borel automorphism back to the original torus by one Borel element.

This supplies the common correction for all three maps of a native amalgam
automorphism, as required in the marked F.4.8–9 comparison (Aschbacher–Smith,
`refs/quasithin.pdf`, pp.278–279). No endpoint extension is assumed here.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.SmallCompletion
variable (F : Type*) [Field F] [Finite F]

/-- The actual split projective torus inside the whole Borel. -/
abbrev borelTorus : Subgroup (borel F) := (torus F).subgroupOf (borel F)

theorem borel_solvable {n : ℕ} (hF : Nat.card F = 2^n) :
    Group.IsSolvable (borel F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent (pCore 2 (borel F)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable ((borel F) ⧸ pCore 2 (borel F)) :=
    Group.isSolvable_of_surjective (f := (BorelQuotient.quotientTorusEquiv F hF).symm.toMonoidHom)
      (BorelQuotient.quotientTorusEquiv F hF).symm.surjective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (borel F))).mpr
    ⟨inferInstance,inferInstance⟩

theorem borelTorus_card_coprime_index {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.Coprime (Nat.card (borelTorus F)) (borelTorus F).index := by
  rw [(BorelQuotient.borel_complement F hF).index_eq_card,
    Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv,
    card_unipotent,hF,←pow_mul]
  have ho : Odd (Nat.card (torus F)) := by
    apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
    rw [Nat.card_prod]
    exact (BorelQuotient.units_odd F hF).mul (BorelQuotient.units_odd F hF)
  exact ho.coprime_two_right.pow_right _

/-- One common Borel conjugation aligns the image of the native torus under
any automorphism of the whole Borel. -/
theorem exists_borel_torus_alignment {n : ℕ} (hF : Nat.card F = 2^n)
    (a : MulAut (borel F)) : ∃ b : borel F,
      ((borelTorus F).map a.toMonoidHom).map (MulAut.conj b).toMonoidHom =
        borelTorus F := by
  let π : Set Nat.Primes := {p | p.val ∣ Nat.card (borelTorus F)}
  have hcop := borelTorus_card_coprime_index F hF
  have hHall : IsHallSubgroup π (borelTorus F) := by
    refine ⟨fun _ hp => hp, ?_⟩
    intro p hp hi
    exact p.property.not_dvd_one ((Nat.dvd_gcd hi hp).trans (by rw [hcop.gcd_eq_one]))
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (borel_solvable F hF) (hHall.map_mulAut a) hHall
  exact ⟨b,hb.symm⟩
end Matrix.PSL3.SmallCompletion
