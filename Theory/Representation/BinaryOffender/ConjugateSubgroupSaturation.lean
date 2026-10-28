module
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Saturation of a fixed-quotient bound by a moved submodule

The fixed space of conjugate generators is their fixed-space intersection.
Summing their common codimensions bounds the global fixed quotient. If an
invariant submodule already fills that bound, the dimension formula forces
it to supplement the global fixed space.

This is the dimension argument used in MS93 (3.3), printed p.867, to obtain
the decomposition of X from four root conjugates and its known natural layer.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The fixed quotient is bounded by a family of conjugate subgroup fixed quotients. -/
theorem fixedCodim_le_card_mul_of_subgroup_conjugates
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (L A : Subgroup G) (g : ι → G)
    (hgen : L ≤ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom) :
    fixedCodim ρ L ≤ Fintype.card ι * fixedCodim ρ A := by
  let X (i : ι) := A.map (MulAut.conj (g i)).toMonoidHom
  have hle := ρ.invariants_comp_subtype_antitone hgen
  have hdim : Module.finrank (ZMod 2) (fixedSpace ρ (⨆ i, X i)) ≤
      Module.finrank (ZMod 2) (fixedSpace ρ L) := Submodule.finrank_mono hle
  have hdL := fixedCodim_add_finrank ρ L
  have hdX := fixedCodim_add_finrank ρ (⨆ i, X i)
  have hcod : fixedCodim ρ L ≤ fixedCodim ρ (⨆ i, X i) := by omega
  have hi := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (X i))
  have he : fixedSpace ρ (⨆ i, X i) = ⨅ i, fixedSpace ρ (X i) :=
    ρ.invariants_comp_iSup X
  rw [←he] at hi
  change fixedCodim ρ (⨆ i, X i) ≤ ∑ i, fixedCodim ρ (X i) at hi
  exact hcod.trans (by
    simpa only [X, fixedCodim_map_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id] using hi)

/-- A moved submodule filling the conjugate-generator bound spans the entire
module together with its fixed space. -/
theorem subrepresentation_sup_fixed_of_conjugate_budget
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (U : Subrepresentation ρ)
    (L A : Subgroup G) (g : ι → G)
    (hgen : L ≤ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom)
    (hbudget : Fintype.card ι * fixedCodim ρ A ≤ fixedCodim U.toRepresentation L) :
    U.toSubmodule ⊔ fixedSpace ρ L = ⊤ := by
  apply (fixedCodim_subrepresentation_eq_iff ρ U L).mp
  exact le_antisymm (fixedCodim_subrepresentation_le ρ U L)
    ((fixedCodim_le_card_mul_of_subgroup_conjugates ρ L A g hgen).trans hbudget)

end Representation.BinaryOffender
