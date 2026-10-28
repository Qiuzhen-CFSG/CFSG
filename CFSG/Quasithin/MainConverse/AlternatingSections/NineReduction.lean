module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Nonprimitive
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Projective

/-!
# Reduction of the A₉ proper-K clause

Source: Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed pp.4 and
482. The target concerns every simple section of every proper subgroup of
an actual copy of A₉. The degree-eight section theorem is left explicit,
with target groups in the universe of the original group.

The nonprimitive cases are proved by restriction and the block action in
`Nonprimitive`. The projective cases use the actual PSL₂(8) matrix carrier
and a normal-subgroup/quotient argument in `Projective`.

The theorems below still assume the primitive structural alternative:
a proper primitive subgroup is solvable, or has a normal PSL₂(8) with
solvable quotient. They are conditional assembly lemmas, not the completed
A₉ proper-K theorem. Exhaustive primitive coverage and construction of its
actual normal subgroups and model equivalences remain to be proved.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open CFSG.KnownSimple BenderSuzuki.MatrixGroups

universe u

/-- The section assembly after the primitive structural alternative is supplied. -/
public theorem simple_section_of_primitive_structure
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    (hprimitive : ∀ H : Subgroup (alternatingGroup (Fin 9)), H ≠ ⊤ →
      MulAction.IsPreprimitive H (Fin 9) →
      Group.IsSolvable H ∨ ∃ (N : Subgroup H) (_ : N.Normal),
        Nonempty (N ≃* PSL2MatrixGroup (GaloisField 2 3)) ∧ Group.IsSolvable (H ⧸ N))
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  by_cases hp : MulAction.IsPreprimitive H (Fin 9)
  · rcases hprimitive H hH hp with hs | ⟨N, hn, ⟨e⟩, hq⟩
    · let := hs
      let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
      exact .cyclic (primeCyclic_of_solvable_simple S)
    · let := hn
      let := hq
      exact normal_pslTwoEight_simple_section_constructed N e U f hf
  · exact simple_section_of_not_preprimitive h8 hp U f hf

/-- Transport the conditional proper-section calculation to any actual copy of A₉.
The primitive premise is still an obligation, in addition to the degree-eight premise. -/
public theorem properK_of_primitive_structure
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    (hprimitive : ∀ H : Subgroup (alternatingGroup (Fin 9)), H ≠ ⊤ →
      MulAction.IsPreprimitive H (Fin 9) →
      Group.IsSolvable H ∨ ∃ (N : Subgroup H) (_ : N.Normal),
        Nonempty (N ≃* PSL2MatrixGroup (GaloisField 2 3)) ∧ Group.IsSolvable (H ⧸ N))
    {G : Type u} [Group G] [Finite G] (e : G ≃* alternatingGroup (Fin 9)) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro H hH S _ hS U f hf
  let := hS
  have hproper : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    have h := congrArg (Subgroup.comap e.toMonoidHom) ht
    simpa only [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.comap_top] using h
  let eH := Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
  let eU := Subgroup.equivMapOfInjective U eH.toMonoidHom eH.injective
  exact simple_section_of_primitive_structure h8 hprimitive (H.map e.toMonoidHom) hproper
    (U.map eH.toMonoidHom) (f.comp eU.symm.toMonoidHom) (hf.comp eU.symm.surjective)

end CFSG.Quasithin.MainConverse.NineReduction
