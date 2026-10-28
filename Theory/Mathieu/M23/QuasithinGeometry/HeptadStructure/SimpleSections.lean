module

public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension

/-!
# Nonsolvable simple sections of the M23 heptad stabilizer

The concrete heptad stabilizer has elementary abelian kernel of order 16
and actual quotient A7. A nonsolvable simple section therefore descends
to A7. Conversely, any section of A7 lifts through the surjective quotient
map. The proof uses the constructed quotient equivalence and the proved
commutativity of the kernel, not the order or name of the stabilizer.

Sources: ATLAS, the M23 maximal-subgroup table on printed p. 71;
Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1 and its M23
specialization. The concrete split extension is proved in `SplitExtension`.
The result reduces this stabilizer's section calculation to A7; it does
not assert that all proper subgroups of M23 lie in this stabilizer.
-/

namespace Sporadic.Mathieu.M23Geometry

/-- The concrete heptad stabilizer and A7 have exactly the same nonsolvable
simple sections, represented by surjections from actual subgroups. -/
public theorem nonsolvable_simple_section_heptad_iff_alternating
    {S : Type*} [Group S] [IsSimpleGroup S] (hS : ¬ Group.IsSolvable S) :
    (∃ U : Subgroup heptadStabilizer, ∃ f : U →* S, Function.Surjective f) ↔
      ∃ U : Subgroup (alternatingGroup (Fin 7)), ∃ f : U →* S, Function.Surjective f := by
  constructor
  · rintro ⟨U, f, hf⟩
    let : Group.IsSolvable heptadKernel := Group.isSolvable_of_comm heptadKernel_mul_comm
    obtain ⟨W, g, hg⟩ := Subgroup.simple_section_quotient_of_solvable_kernel
      hS heptadKernel U f hf
    let e := Subgroup.equivMapOfInjective W heptadQuotientAlternatingEquiv.toMonoidHom
      heptadQuotientAlternatingEquiv.injective
    exact ⟨W.map heptadQuotientAlternatingEquiv.toMonoidHom,
      g.comp e.symm.toMonoidHom, hg.comp e.symm.surjective⟩
  · rintro ⟨U, f, hf⟩
    have hq : Function.Surjective heptadAlternatingAction :=
      fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩
    exact ⟨U.comap heptadAlternatingAction,
      f.comp (heptadAlternatingAction.subgroupComap U),
      hf.comp (heptadAlternatingAction.subgroupComap_surjective_of_surjective U hq)⟩

end Sporadic.Mathieu.M23Geometry
