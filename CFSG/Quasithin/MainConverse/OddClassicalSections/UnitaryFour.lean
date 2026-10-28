module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# PSU₄(3): model transport and geometric section assembly

Source: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4
and 482 of `refs/quasithin.pdf`. The model predicate allows any nondegenerate
Hermitian form over any field of order nine, with conjugation x ↦ x³.

The actual model equivalence is proved in `UnitaryFourThree.Model`. To handle
a subgroup of a proper subgroup, flatten it inside the ambient group and
transport it to that model. The first isomorphism theorem identifies each
simple image with a quotient whose kernel is normal inside its numerator.
Solvable simple images are prime cyclic. The nonsolvable case splits according
to whether the full SU preimage preserves a nonzero proper subspace.

The reducible and irreducible quotient classifications remain explicit
premises. These assembly lemmas do not assert the source proper-K theorem;
this module retains that final assembly until both branches are proved.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- The arbitrary form in `IsPSU` is identified with the concrete field-nine model. -/
public theorem psu_three_model_equiv {G : Type*} [Group G] {n : ℕ}
    (hG : ClassicalGroup.IsPSU G n 3) : Nonempty (G ≃* Carrier n) := by
  obtain ⟨F, hF, hfin, J, hcard, hc, ⟨e⟩⟩ := hG
  obtain ⟨a⟩ := exists_model_equiv J (by simpa using hcard) hc
  exact ⟨e.trans a⟩

/-- A proper nested subgroup remains proper after flattening and model transport. -/
private theorem proper_image {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U) :
    (V.map U.subtype).map e.toMonoidHom ≠ ⊤ := by
  intro h
  have hv : V.map U.subtype = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  exact hU (top_unique (hv ▸ Subgroup.map_subtype_le V))

/-- Conditional assembly from the two exhaustive geometric branches.
Normality in each branch is inside the numerator subgroup. Neither branch
classification is asserted by this reduction. -/
public theorem psu4_three_simpleSection_of_geometric_branches
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hG : ClassicalGroup.IsPSU G 4 3)
    (hreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (hirreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → ¬ IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (f : V →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  by_cases hs : Group.IsSolvable S
  · let := hs
    exact .cyclic (primeCyclic_of_solvable_simple S)
  obtain ⟨e⟩ := psu_three_model_equiv hG
  let W := (V.map U.subtype).map e.toMonoidHom
  let a := (Subgroup.equivMapOfInjective V U.subtype U.subtype_injective).trans
    (Subgroup.equivMapOfInjective (V.map U.subtype) e.toMonoidHom e.injective)
  let g : W →* S := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  let q : (W ⧸ g.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective g hg
  let : IsSimpleGroup (W ⧸ g.ker) := q.isSimpleGroup
  have hnsolv : ¬ Group.IsSolvable (W ⧸ g.ker) := by
    intro h
    let := h
    exact hs (Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective)
  have hW : W ≠ ⊤ := proper_image e U hU V
  apply IsConstructedCarrier.of_mulEquiv (e := q.symm)
  by_cases hred : IsReducible W
  · exact hreducible W hW hred g.ker hnsolv
  · exact hirreducible W hW hred g.ker hnsolv

/-- Quotient version of the conditional assembly, with the normal subgroup
inside the actual subgroup being quotiented. -/
public theorem psu4_three_simpleQuotient_of_geometric_branches
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSU G 4 3)
    (hreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (hirreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → ¬ IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U) (N : Subgroup V)
    [N.Normal] [IsSimpleGroup (V ⧸ N)] : IsConstructedCarrier (V ⧸ N) :=
  psu4_three_simpleSection_of_geometric_branches hG hreducible hirreducible U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The proper-K conclusion remains conditional until both geometric
section classifications are proved. -/
public theorem psu4_three_properK_of_geometric_branches
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSU G 4 3)
    (hreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N))
    (hirreducible : ∀ (U : Subgroup (Carrier 4)), U ≠ ⊤ → ¬ IsReducible U →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)],
        ¬ Group.IsSolvable (U ⧸ N) → IsConstructedCarrier (U ⧸ N)) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU S _ hS V f hf
  let := hS
  exact psu4_three_simpleSection_of_geometric_branches hG hreducible hirreducible
    U hU V f hf

end CFSG.Quasithin.MainConverse
