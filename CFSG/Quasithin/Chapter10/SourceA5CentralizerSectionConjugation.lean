module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedOpposite
public import Theory.GroupTheory.SubgroupSectionConjugation

/-!
# Transporting the original factor-centralizer section

The offender preimage is normal in the original local join. Thus a
section of the literal quotient image of its centralizer of L transports
to the centralizer of any prescribed conjugate of L. The original
quotient, offender subgroup, and conjugator are retained. The zero-center
consumer supplies the distinct original Sylow-conjugate pair.

Source: Aschbacher–Smith 10.2.1, pp.742–743. The first section is provided
by the exact natural-kernel extension calculation.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A section of the original quotient on the actual factor centralizer. -/
@[expose] def OriginalCentralizerImageSection (A : Subgroup (localJoin T L)) : Prop :=
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let P := Y.comap q ⊓ centralizer (A : Set H)
  ∃ σ : P.map q →* P, (q.comp P.subtype).comp σ = (P.map q).subtype

/-- Transport the actual first section using the supplied original conjugator. -/
theorem source_centralizer_image_section_conjugate
    (A : Subgroup (localJoin T L)) (t : localJoin T L)
    (hs : OriginalCentralizerImageSection D A) :
    OriginalCentralizerImageSection D (A.map (MulAut.conj t).toMonoidHom) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨σ,hσ⟩ := hs
  exact exists_centralizer_image_section_conjugate q (Y.comap q) A t σ hσ

/-- One exact kernel splitting supplies sections for both actual members
of the original zero-center Sylow-conjugate pair. -/
theorem source_a5_zero_centralizer_pair_sections_of_first
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hs : OriginalCentralizerImageSection D (L.subgroupOf (localJoin T L))) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      L.subgroupOf (localJoin T L) ≠
        (L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom ∧
      SourceOriginalPairedOpposite D t ∧
      OriginalCentralizerImageSection D (L.subgroupOf (localJoin T L)) ∧
      OriginalCentralizerImageSection D
        ((L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨t,ht,hne,hop⟩ := source_a5_zero_centralizer_paired_opposite D e hn hout hz
  exact ⟨t,ht,hne,hop,hs,source_centralizer_image_section_conjugate D _ t hs⟩

end CFSG.Quasithin.Chapter10
