module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonabelianCoreSource
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceQuotient

/-!
# The original A₆ component supplies its full involution centralizer

The complete A₆ branch of source 2.5.21 constructs H/O₂(H) ≃ Aut(A₆).
The existing compatible-action argument then proves H = C_G(t) for the
original central core involution, without an additional quotient witness.

Source: Aschbacher--Smith, 2.5.21–22, printed pp.565–567.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow
open ComponentRefinement Section05.ComponentSelection
variable {G:Type*} [Group G] [Finite G] {H K M:Subgroup G} {S:Sylow 2 H} {z:G}

/-- Original source 2.5.22(2) for an actual A₆ component, with the 2.5.21
quotient and its compatible conjugation action discharged internally. -/
theorem centralizer_eq_of_original_component
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (eK:K≃*alternatingGroup (Fin 6)) :
    H=centralizer ({t}:Set G) := by
  obtain ⟨eQ⟩ := MathieuSourceSetup.alternating_six_full_core_quotient
    c hG hempty hgen hb hstar eK
  exact centralizer_eq_of_original_quotient c hG hempty hgen hb hstar t ht htC htZ eK eQ
end CFSG.Quasithin.Chapter2.A6Shadow
