module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic

/-!
# Excluding the natural quotient at the original alternating-seven component

The faithful seven-letter marking has range A₇ or S₇. In either case its
actual quotient Sylow and module coordinates can be marked simultaneously.
The original component supplies point-core movement, so the source seed
word contradiction excludes the natural six-dimensional alternative with
no additional partition, word, Sylow, or movement hypotheses.
Source: Aschbacher–Smith 14.7.50, printed pp.1064–1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original proper local quotient cannot be the natural seven-letter module. -/
theorem local_natural_quotient_impossible_at
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
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7)) (hj : Function.Injective j)
    (hcases : j.range = alternatingGroup (Fin 7) ∨ j.range = ⊤)
    (hnatural : IsNatural N.quotientRepresentation j) : False := by
  have hm := local_alternating_seven_plane_moved_at d h hab structural previous faithful
    earlier source47 I hI C hC e
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (f := q)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨m⟩ := hnatural
  rcases hcases with ha | hs
  · let jA := j.codRestrict (alternatingGroup (Fin 7)) (fun x => ha ▸ (show j x ∈ j.range from ⟨x,rfl⟩))
    have hjA : Function.Bijective jA := by
      constructor
      · intro x y he
        exact hj (congrArg Subtype.val he)
      · intro z
        have hz : z.val ∈ j.range := ha.symm ▸ z.property
        obtain ⟨x,hx⟩ := hz
        exact ⟨x,Subtype.ext hx⟩
    let b : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective jA hjA
    have mb : Representation.Equiv ((alternatingCoreRepresentation (Fin 7)).comp b.toMonoidHom)
        N.quotientRepresentation := m
    obtain ⟨b',hP,⟨m'⟩⟩ := NaturalMarking.alternating_sylow_marking P N.quotientRepresentation b mb
    let π := b'.toMonoidHom.comp q
    have hT : ((T : Subgroup G).subgroupOf I).map π = SevenSourceCubics.Alternating.two := by
      rw [show π = b'.toMonoidHom.comp q from rfl,←Subgroup.map_map]
      exact hP
    let p : Representation.IntertwiningMap (a.representation.comp q)
        ((alternatingCoreRepresentation (Fin 7)).comp π) := {
      toLinearMap := m'.symm.toLinearMap.comp N.toSubmodule.mkQ
      isIntertwining' := by
        intro i
        apply LinearMap.ext
        intro z
        exact LinearMap.congr_fun (m'.symm.isIntertwining' (q i)) (N.toSubmodule.mkQ z) }
    have hp : p.toLinearMap.ker ≠ ⊤ := by
      intro he
      apply hN
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro z _
      have hz : p z = 0 := by
        change z ∈ p.toLinearMap.ker
        rw [he]
        trivial
      have hz' : N.toSubmodule.mkQ z = 0 := m'.symm.injective (hz.trans (map_zero m'.symm).symm)
      exact (Submodule.Quotient.mk_eq_zero _).mp hz'
    have hk : IsPGroup 2 π.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ b'.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact local_alternating_natural_impossible_at h hab structural previous faithful hm
      I hI π (b'.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT
      (localQuotientSection a) p hp
  · let b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 7) :=
      MulEquiv.ofBijective j ⟨hj,MonoidHom.range_eq_top.mp hs⟩
    obtain ⟨b',hP,⟨m'⟩⟩ := NaturalMarking.symmetric_sylow_marking P N.quotientRepresentation b m
    let π := b'.toMonoidHom.comp q
    have hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo := by
      rw [show π = b'.toMonoidHom.comp q from rfl,←Subgroup.map_map]
      exact hP
    let p : Representation.IntertwiningMap (a.representation.comp q)
        ((coreRepresentation (Fin 7)).comp π) := {
      toLinearMap := m'.symm.toLinearMap.comp N.toSubmodule.mkQ
      isIntertwining' := by
        intro i
        apply LinearMap.ext
        intro z
        exact LinearMap.congr_fun (m'.symm.isIntertwining' (q i)) (N.toSubmodule.mkQ z) }
    have hp : p.toLinearMap.ker ≠ ⊤ := by
      intro he
      apply hN
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro z _
      have hz : p z = 0 := by
        change z ∈ p.toLinearMap.ker
        rw [he]
        trivial
      have hz' : N.toSubmodule.mkQ z = 0 := m'.symm.injective (hz.trans (map_zero m'.symm).symm)
      exact (Submodule.Quotient.mk_eq_zero _).mp hz'
    have hk : IsPGroup 2 π.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ b'.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact local_symmetric_natural_impossible_at h hab structural previous faithful hm
      I hI π (b'.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT
      (localQuotientSection a) p hp
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
