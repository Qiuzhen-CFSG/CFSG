module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Multiplicity
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Homogeneous

/-!
# Recognizing the quotient of an abelian binary MS core

The reduction constructs the literal conjugation action from elementary-core
and intrinsic-kernel centrality hypotheses. It proves faithfulness, full
commutator generation, and the fixed-space identification, then transports
natural module coordinates to `AbelianCore.NaturalQuotient`.
The offender inequality bounds the multiplicity by two, and faithfulness
excludes zero copies. This sharp bound does not assume semisimplicity of D.

Two existence results remain: the whole-core elementary FF-action from the
MS hypotheses, and homogeneous natural recognition for arbitrary binary
SL₃(2) FF-modules. Thus `Input.exists_abelianCore_naturalQuotient` is not yet
asserted. Final assembly of that theorem belongs to this module.

Source: Aschbacher–Smith C.1.34(1),(2),(5), printed pp.136–137 of the combined
manuscript of 1 March 2004; the source invokes the binary MS93/DGS85 argument.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition

open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} [IsElementaryAbelian 2 (commutatorCore L)]

/-- Homogeneous coordinates for the whole-core FF-action automatically have
the required sharp multiplicity and transfer to the literal group quotient.
Existence of the two inputs remains a separate local and module-theoretic task. -/
theorem CoreFFAction.naturalQuotient_cases (a : CoreFFAction h) {m : ℕ}
    (q : ModuleQuotient a.representation m) :
    (m = 1 ∨ m = 2) ∧ Nonempty (AbelianCore.NaturalQuotient h m) :=
  ⟨q.multiplicity_cases a.faithful a.offending, ⟨a.toNaturalQuotient q⟩⟩

omit [IsElementaryAbelian 2 (commutatorCore L)] in
include h in
/-- An abelian binary MS core has a natural quotient of multiplicity one or two.
The whole-core action and its offender are constructed from the genuine MS
hypotheses, then the binary homogeneous-module theorem supplies the quotient
coordinates. -/
theorem Input.exists_abelianCore_naturalQuotient
    (hc : IsMulCommutative (commutatorCore L)) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (AbelianCore.NaturalQuotient h m) := by
  obtain ⟨he, ha⟩ := h.exists_abelianCore_coreFFAction hc
  let _ : IsElementaryAbelian 2 (commutatorCore L) := he
  obtain ⟨a⟩ := ha
  obtain ⟨m, hm⟩ := exists_moduleQuotient a.representation a.faithful
    a.full_commutator a.offending
  obtain ⟨q⟩ := hm
  exact ⟨m, a.naturalQuotient_cases q⟩

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
