module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.FanoCoreStructure
public import Theory.Representation.PSL3Two.FanoQuotients
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual

/-!
# The Fano permutation modules in H.5–H.9

This source assembly re-exports the proved binary irreducible catalogue and
point/line core structure. It identifies the actual cosets of the marked Sylow
two-subgroup with the twenty-one flags and lifts that identification to an
intertwining equivalence, giving the four-summand decomposition on the source's
coset carrier, with the literal basis-vector formula.

These are H.5.1, H.5.3(1–2,5), H.6.1 and the marked form of H.6.2(1), from
Aschbacher–Smith, combined manuscript of 1 March 2004, printed pp.385–388.
The quotient reduction for H.6.5 is also provided with its two excluded
simple quotients explicit; the cyclic-generator hypotheses must still
establish those exclusions and the five final module alternatives.
The remaining local calculations and the natural-plus-dual results of H.9
are separate source obligations; no statement here assumes the false printed
H.6.4 kernel-containment lemma.
-/

@[expose] public section

open Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition

namespace CFSG.Quasithin.ChapterH.Section05To09
/-- The cosets of `flagSylow`, whose underlying subgroup is the marked flag stabilizer. -/
abbrev FlagCosets := Group ⧸ MulAction.stabilizer Group markedFlag
noncomputable instance : Fintype FlagCosets := Fintype.ofFinite _
noncomputable local instance : DecidableEq FlagCosets := Classical.decEq _

noncomputable def cosetRepresentation : Representation (ZMod 2) Group
    (BinaryPermutation.Full FlagCosets) :=
  (BinaryPermutation.representation FlagCosets).comp (MulAction.toPermHom Group FlagCosets)

noncomputable def cosetFlagEquiv : cosetRepresentation.Equiv flagRepresentation :=
  .mk (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) cosetEquiv.symm) (by
    intro g
    apply LinearMap.ext
    intro a
    funext f
    change a (g⁻¹ • cosetEquiv.symm f) = a (cosetEquiv.symm (g⁻¹ • f))
    congr 1
    apply cosetEquiv.injective
    rw [cosetEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

noncomputable def cosetDecomposition : cosetRepresentation.Equiv targetRepresentation :=
  cosetFlagEquiv.trans flagDecomposition

@[simp] theorem cosetFlagEquiv_basis (q : FlagCosets) :
    cosetFlagEquiv (Pi.single q 1) = Pi.single (cosetEquiv q) 1 := by
  classical
  ext f
  change (Pi.single q 1 : FlagCosets → ZMod 2) (cosetEquiv.symm f) =
    (Pi.single (cosetEquiv q) 1 : Flag → ZMod 2) f
  by_cases h : f = cosetEquiv q
  · subst f
    simp
  · have hq : cosetEquiv.symm f ≠ q := fun he => h (cosetEquiv.symm_apply_eq.mp he)
    simp only [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne h]

/-- The four components of the image of a basis coset in the H.6.2 decomposition. -/
theorem cosetDecomposition_basis (q : FlagCosets) :
    cosetDecomposition (Pi.single q 1) =
      (1, (pointSpike (cosetEquiv q).val.1,
        (lineSpike (cosetEquiv q).val.2, flagRankOne (cosetEquiv q)))) := by
  change flagDecomposition (cosetFlagEquiv (Pi.single q 1)) = _
  rw [cosetFlagEquiv_basis, flagDecomposition_basis]

/-- The corrected H.6.5 reduction on the source's literal coset module.
The two quotient exclusions remain explicit until deduced from its cyclic seed. -/
theorem coset_quotient_of_no_trivial_or_dual
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) Group M)
    (q : cosetRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (htriv : ∀ f : ρ.IntertwiningMap FanoQuotients.trivialRepresentation,
      ¬ Function.Surjective f)
    (hdual : ∀ f : ρ.IntertwiningMap W.dual, ¬ Function.Surjective f) :
    ∃ f : (U₂.prod S).IntertwiningMap ρ, Function.Surjective f :=
  FanoQuotients.quotient_of_flags ρ (q.comp cosetFlagEquiv.symm.toIntertwiningMap)
    (hq.comp cosetFlagEquiv.symm.toLinearEquiv.surjective) htriv hdual
end CFSG.Quasithin.ChapterH.Section05To09
