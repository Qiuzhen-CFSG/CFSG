module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.FlagGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.Sylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel

/-!
# Marking the actual original symmetric-eight flag quotient

The original linear-four component selects its literal maximal invariant
quotient and natural module. Simultaneous inner conjugation of its group
and module markings sends the original Sylow to the binary-tree Sylow.
The resulting surjective projection retains exactly the selected module
kernel. The original seed is a singular plane and its flag is the standard
singular point, whose full stabilizer preimage is retained literally.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open AlternatingSevenSource BinaryPermutation
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open BinaryNaturalDual.VectorStabilizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original degree-four row supplies the marked proper natural quotient,
its exact kernel and full flag stabilizer, with no module or marking premise. -/
theorem local_four_exists_marked_flag_quotient_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
        (N : Subrepresentation a.representation)
        (b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8)),
        let q := QuotientGroup.mk' (pCore 2 I)
        let π := b.toMonoidHom.comp q
        ∃ p : Representation.IntertwiningMap (a.representation.comp q)
            ((naturalRepresentation (Fin 8)).comp π),
          BinaryOffender.quadraticRatio a.representation ≤ 2 ∧ IsCoatom N ∧
          IsIrreducible N.quotientRepresentation ∧
          Function.Injective N.quotientRepresentation ∧
          BinaryOffender.quadraticRatio N.quotientRepresentation ≤ 2 ∧
          p.toLinearMap.ker = N.toSubmodule ∧ Function.Surjective p ∧
          ((T : Subgroup G).subgroupOf I).map π = treeGroup ∧
          (let s := localQuotientSection a
           let E := (s.imageSpace V).map p.toLinearMap
           let D := (s.imageSpace (F.Vi 2)).map p.toLinearMap
           Module.finrank (ZMod 2) E = 2 ∧
             D = Submodule.span (ZMod 2) {standardPoint} ∧
             (∀ x ∈ E, TerminalOrthogonal.Eight.form x = 0) ∧
             representationStabilizer ((naturalRepresentation (Fin 8)).comp π) standardPoint =
               fourStabilizer.comap π) := by
  obtain ⟨hU,hr⟩ := local_four_exists_natural_quotient_at d h hab structural previous
    faithful earlier source47 I hI C hC e
  let := hU
  obtain ⟨a,N,b,ha,hN,hirr,hfaith,hq,_hcomp,hnat⟩ := hr
  obtain ⟨E,hE⟩ := hnat
  let m : Representation.Equiv N.quotientRepresentation
      ((naturalRepresentation (Fin 8)).comp b.toMonoidHom) :=
    .mk E (by
      intro g
      apply LinearMap.ext
      intro x
      exact hE g x)
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (f := q)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨b',hP,⟨m'⟩⟩ := NaturalMarking.exists_sylow_marking 2 P treeSylow
    (naturalRepresentation (Fin 8)) N.quotientRepresentation b m.symm
  let π := b'.toMonoidHom.comp q
  have hT : ((T : Subgroup G).subgroupOf I).map π = treeGroup := by
    rw [show π = b'.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact hP
  let p : Representation.IntertwiningMap (a.representation.comp q)
      ((naturalRepresentation (Fin 8)).comp π) := {
    toLinearMap := m'.symm.toLinearMap.comp N.toSubmodule.mkQ
    isIntertwining' := by
      intro i
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (m'.symm.isIntertwining' (q i)) (N.toSubmodule.mkQ x) }
  have hker : p.toLinearMap.ker = N.toSubmodule := by
    change (m'.symm.toLinearMap.comp N.toSubmodule.mkQ).ker = _
    rw [LinearMap.ker_comp_of_ker_eq_bot _ m'.symm.toLinearEquiv.ker,Submodule.ker_mkQ]
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    rw [hker]
    intro he
    exact hN.ne_top (Subrepresentation.toSubmodule_injective he)
  have hsurj : Function.Surjective p :=
    m'.symm.surjective.comp N.toSubmodule.mkQ_surjective
  exact ⟨hU,a,N,b',p,ha,hN,hirr,hfaith,hq,hker,hsurj,hT,
    local_natural_flag_geometry_at h hI π hT (localQuotientSection a) p hp⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
