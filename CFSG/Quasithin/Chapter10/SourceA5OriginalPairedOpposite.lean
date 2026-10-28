module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPair
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualOpposite

/-!
# The original conjugate pair occupies opposite alternating axes

The prescribed conjugator is retained while the paired residual
permutation and the nonabelian alternating images exclude the same-axis
case. The zero-center consumer supplies the original commuting pair and
its Sylow conjugator without assuming any quotient-axis identification.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

@[expose] def SourceOriginalPairedOpposite (t : localJoin T L) : Prop :=
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let B := A.map (MulAut.conj t).toMonoidHom
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ _c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      Y.comap q ≤ normalizer (A : Set H) ∧
      ((A.map q = (factorResidual q Y d.first).map q ∧
        B.map q = (factorResidual q Y d.second).map q) ∨
       (A.map q = (factorResidual q Y d.second).map q ∧
        B.map q = (factorResidual q Y d.first).map q))

/-- The chosen original conjugator retains its opposite-axis identification. -/
theorem source_a5_original_paired_opposite
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (t : localJoin T L)
    (hc : ⁅L.subgroupOf (localJoin T L),
      (L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom⁆ = ⊥) :
    SourceOriginalPairedOpposite D t := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  obtain ⟨d,c,hex,hnorm,haxes⟩ := source_a5_original_paired_axes D e hn hout
  exact ⟨d,c,hnorm,paired_symmetric_commuting_conjugate_opposite U hU q hq hk d c
    (L.subgroupOf H) t hc haxes⟩

/-- The original zero-center pair supplies the commuting conjugator and
opposite marked axes together, with no additional premise. -/
theorem source_a5_zero_centralizer_paired_opposite
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      (L.subgroupOf (localJoin T L) ≠
        (L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom) ∧
      SourceOriginalPairedOpposite D t := by
  obtain ⟨t,ht,hne,hc,_,_,_,_,_⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  exact ⟨t,ht,hne,source_a5_original_paired_opposite D e hn hout t hc⟩

end CFSG.Quasithin.Chapter10
