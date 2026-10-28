module

public import CFSG.Quasithin.MainConverse.MathieuSections.Reduction
public import CFSG.Quasithin.ClassificationModels.Families

/-!+# Quotient inputs for the sporadic proper-K calculation

For each concrete sporadic carrier, the remaining input is the identification
of nonsolvable simple quotients `U / N`, where `U` is a proper subgroup and
`N` is normal in `U`. The quotient is in the carrier's own universe. The first
isomorphism theorem transports this input to arbitrary simple targets, and
the existing section reductions flatten nested subgroups, transport along
actual model equivalences, and identify solvable simple targets as prime
cyclic groups. Finiteness then discharges the guards on the inclusion in K.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, condition K and Theorem 0.1.2(5), printed p.4,
repeated on p.482. The input classifications are not proved here. In
particular these conditional assembly results do not establish proper K
for any sporadic carrier. J₂ and HS retain the ATLAS permutation carriers
from `ClassificationModels.Families`; no lattice-model comparison is assumed.
-/

namespace CFSG.Quasithin.MainConverse.SporadicSections

open CFSG.KnownSimple ClassificationModels

universe u v

/-- Classifying actual quotients in the concrete carrier's universe also
classifies surjective images in any universe. Normality is inside `U`. -/
public theorem constructed_of_quotient_classification
    {H : Type v} {S : Type u} [Group H] [Group S] [IsSimpleGroup S]
    (hquotients : ∀ (U : Subgroup H), U ≠ ⊤ →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (hS : ¬ Group.IsSolvable S) (U : Subgroup H) (hU : U ≠ ⊤)
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsSimpleGroup (U ⧸ f.ker) := e.isSimpleGroup
  have hns : ¬ Group.IsSolvable (U ⧸ f.ker) := by
    intro hsolv
    let := hsolv
    exact hS (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  exact (hquotients U hU f.ker hns).of_mulEquiv e.symm

/-- Conditional assembly for a finite concrete model. Solvable targets and
subgroups nested inside proper subgroups need no additional input. -/
public theorem properK_of_quotient_classification
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite H]
    {K : GroupClass.{u}}
    (hK : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (e : G ≃* H)
    (hquotients : ∀ (U : Subgroup H), U ≠ ⊤ →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N)) :
    HasProperKSubgroups K G := by
  let : Finite G := Finite.of_injective e e.injective
  apply MathieuSections.properK_of_constructed_sections hK
  apply MathieuSections.properK_of_nonsolvable_simple_sections_of_equiv e
  intro S _ _ hS U hU f hf
  exact constructed_of_quotient_classification hquotients hS U hU f hf

/-- The named carrier supplies finiteness directly from its construction.
Its proper-quotient classification is still a required, explicit premise. -/
public theorem sporadic_properK_of_quotient_classification
    {G : Type u} [Group G] {K : GroupClass.{u}}
    (hK : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (name : SporadicName) (e : G ≃* name.Carrier)
    (hquotients : ∀ (U : Subgroup name.Carrier), U ≠ ⊤ →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N)) :
    HasProperKSubgroups K G := by
  let : Finite name.Carrier := by
    cases name <;> dsimp [SporadicName.Carrier] <;> infer_instance
  exact properK_of_quotient_classification hK e hquotients

end CFSG.Quasithin.MainConverse.SporadicSections
