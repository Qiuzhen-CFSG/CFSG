module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Duality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedSubgroup

/-!
# The quotient module and fixed subgroup in J.2.2(3)

This boundary proves the full third clause from LocalSetup and the earlier
containment Q ≤ K. It retains the literal H-equivariant commutator dual,
the inherited K/Q ≃ A₅ marking, the actual natural SL₂(4) section Q/HC,
and the exact ambient preimage of the fixed subgroup C_{Q/U}(K).

F.9.7 constructs the dual section. Trace-determinant self-duality identifies
its restricted K-action with the natural module. The order-four section
HC/U has trivial A₅ action; conversely any fixed class in Q/U maps to zero
in the natural Q/HC module. Thus HC/U is exactly the fixed subgroup.
No classification of six-dimensional indecomposable modules is needed.
The premise Q ≤ K is the conclusion of J.2.2(1), whose assembly belongs
to the parent ParabolicStructure boundary.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443).
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

/-- J.2.2(3), using only the earlier Q ≤ K containment. The fixed-subgroup
clause is the exact ambient preimage specification for HC/U=C_{Q/U}(K).
Both quotient markings and the natural module use the original Ru2 map. -/
theorem lemma_J_2_2_three (d : LocalSetup G)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    let _ : (d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K).Normal :=
      d.toTypeRuSetup.Q_normal_in_K
    Nonempty ((d.toTypeRuSetup.K ⧸ d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K) ≃*
      alternatingGroup (Fin 5)) ∧
    (∀ q : G, q ∈ d.toTypeRuSetup.HC ↔ q ∈ d.toTypeRuSetup.Q ∧
      ∀ k ∈ d.toTypeRuSetup.K, ⁅k, q⁆ ∈ d.toTypeRuSetup.U) ∧
    Nonempty (BinaryConjugationSection d.toTypeRuSetup.K d.toTypeRuSetup.Q d.toTypeRuSetup.HC
      (SL2FourNatural.naturalRepresentation.comp d.toTypeRuSetup.naturalQuotientMap)) := by
  let _ : (d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K).Normal :=
    d.toTypeRuSetup.Q_normal_in_K
  exact ⟨⟨d.toTypeRuSetup.alternatingQuotientEquiv⟩,
    d.mem_HC_iff_commutator_mem_U hQK, ⟨d.naturalQuotientSection hQK⟩⟩

end CFSG.Quasithin.ChapterJ
