module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives
public import Theory.Representation.G2BinarySylowFixedSpace

/-!
# Excluding the binary G₂ natural section in the mixed FF branch

The explicit cubic fixer on the natural module of G₂(2)′ transports through
`restrictMarked`, using the commuting subgroup square of the full G₂(2)
action. Cubic lifting across the central kernel of `[V,L] → [V,L]/C_[V,L](L)`
and odd Sylow-coset averaging across `V/[V,L]` then give an outside-Sylow
fixer on the original module. Both extensions may be nonsplit, and the
marked offender subgroup need not be the whole ambient actor.

For the literal offender action, the seed centralizer excludes this fixer.
Thus the binary G₂ constructor of `ExceptionalSection` is impossible there.
Source-row extraction and the independent triple-six calculation remain with
their existing owners; this module proves the entire binary G₂ exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
15.4.18, printed p.1163; B.4.2(4), p.86; B.5.1, p.99.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Representation.BinarySylowFixedSpace
open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives

namespace ExceptionalFixedSpace.BinaryG2
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- The marked binary G₂ natural section supplies a cubic outside every
ambient Sylow, retaining the actual central section and both extensions. -/
theorem enlargement (s : MovedSection ρ L)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let a : ActionEquiv (s.action.comp L.subtype) (g2DerivedNatural (ZMod 2)) :=
    NativeSections.restrictMarked e
  let T : Sylow 2 L := Classical.choice inferInstance
  apply NativeSections.movedSection_enlargement s T _ S
  exact sylow_fixedSpace_enlargement_equivariant _ _ (T : Subgroup L)
    a.groupEquiv a.linearEquiv a.intertwines
    (Atlas.G2.Natural.BinarySylowFixedSpace.derived_sylow_enlargement
      (T.mapSurjective a.groupEquiv.surjective))

/-- Application to the exact section stored in the source-correct B.5.1
conclusion. No equality of the offender actor and the ambient group is used. -/
theorem source_enlargement (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (e : MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action) L
      (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v :=
  enlargement c.sectionData e S

end ExceptionalFixedSpace.BinaryG2

variable {H : Type*} [Group H] [Finite H]
  (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- The actual seed centralizer excludes a marked binary G₂ section of the
literal offender action, with no additional fixed-space premise. -/
theorem offenderAction_not_binaryG2
    (L : Subgroup (offenderGroup P Z hC)) (s : MovedSection (offenderAction P Z hC) L)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨S, hS⟩ := exists_offenderSylow P Z hC
  obtain ⟨d, hd, _, hf⟩ := ExceptionalFixedSpace.BinaryG2.enlargement s e S
  exact offenderAction_no_fixedSpace_enlargement P Z hC (S : Subgroup _) hS d hd hf

/-- Eliminate the binary G₂ constructor, retaining precisely the independent
triple-six alternative and its faithful source action. -/
theorem offenderAction_tripleSix_of_exceptionalSection
    (L : Subgroup (offenderGroup P Z hC)) (s : MovedSection (offenderAction P Z hC) L)
    (h : ExceptionalSection s) :
    Function.Injective s.action ∧ Nonempty (FFAlternatives.ProjectiveLine.TripleSixAction s.action L) := by
  cases h with
  | binaryG2 _ e => exact (offenderAction_not_binaryG2 P Z hC L s e).elim
  | tripleSix hf e => exact ⟨hf, ⟨e⟩⟩

/-- The exhaustive comparison's literal source section has only the triple-six
exception left once the source module alternatives have been extracted. -/
theorem comparedBranch_tripleSix_of_models
    (b : QuasisimpleComparison.ComparedBranch (quotientAction P Z hC))
    (h : SectionAlternatives b.source.sectionData) :
    Function.Injective b.source.sectionData.action ∧
      Nonempty (FFAlternatives.ProjectiveLine.TripleSixAction b.source.sectionData.action
        (generalizedFitting (offenderGroup P Z hC))) :=
  offenderAction_tripleSix_of_exceptionalSection P Z hC _ b.source.sectionData
    (comparedBranch_exceptionalSection_of_models P Z hC b h)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
