module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition.Geometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme

/-!
# Quotient and residual of the even three-pair stabilizer

Adjoin the fixed seventh letter to the existing six-letter syntheme model.
Its even subgroup has order 24 and quotient S₃ by its two-core. The literal
two-residual is the paired A₄, of order 12. Conjugating the same markings
transports all three conclusions to every partition of type 2,2,2,1.
The finite checks concern only the 48-element syntheme model.

Source: Aschbacher--Smith 15.1.22(1), printed pp.1098--1099;
I.5.7 for the six-letter syntheme quotient.
-/

public section
open Subgroup Equiv Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals
namespace CFSG.Quasithin.Chapter15.Section01.SevenPartition

theorem even_stabilizer_card (p : Partition 7 4 ![2,2,2,1]) :
    Nat.card (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup Perm7) = 24 := by
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hA : (alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom = alternatingGroup (Fin 7) :=
    Normal.map_conj_eq _ c
  have he : alternatingGroup (Fin 7) ⊓ p.stabilizer =
      (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)).map
        (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective,hA,hc]
  rw [he,card_map_of_injective (MulAut.conj c).injective,←pairedFour_normalizer_eq]
  exact alternating_normalizer_pairedFour_card

theorem even_stabilizer_residual_card (p : Partition 7 4 ![2,2,2,1]) :
    Nat.card (pResidual 2 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup Perm7)) = 12 := by
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hh := congrArg (fun H : Subgroup Perm7 => Nat.card H)
    (conjugate_partition_twoResidual p.stabilizer c hc)
  rw [card_map_of_injective (alternatingGroup (Fin 7) ⊓ p.stabilizer).subtype_injective,
    card_map_of_injective (MulAut.conj c).injective,pairedFour_card] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section01.SevenPartition

namespace CFSG.Quasithin.Chapter15.Section01.SevenPartition
open Theory.SpecificGroups.SymmetricSix
open SynthemeCalculation
private def modelSeven : Model →* Perm7 :=
  (Perm.extendDomainHom (finSuccAboveEquiv (6 : Fin 7))).comp modelHom
private theorem modelSeven_injective : Function.Injective modelSeven :=
  (Perm.extendDomainHom_injective _).comp modelHom_injective
private theorem modelSeven_pair (a : Model) :
    modelSeven a ∈ centralizer ({pairing} : Set Perm7) := by
  rw [mem_centralizer_singleton_iff]
  revert a
  decide +kernel
private theorem modelSeven_even (a : evenModel) :
    modelSeven a ∈ alternatingGroup (Fin 7) := by
  have hh : ∀ a : Model, a ∈ evenModel → (modelSeven a).sign = 1 := by decide +kernel
  exact hh a a.property
private def evenModelSeven : evenModel →*
    (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) : Subgroup Perm7) :=
  (modelSeven.comp evenModel.subtype).codRestrict _ (fun a => ⟨modelSeven_even a,modelSeven_pair a⟩)
private theorem evenModelSeven_bijective : Function.Bijective evenModelSeven := by
  apply Function.Injective.bijective_of_nat_card_le
  · intro a b he
    exact Subtype.ext (modelSeven_injective (congrArg Subtype.val he))
  · rw [evenModel_card,←pairedFour_normalizer_eq,alternating_normalizer_pairedFour_card]

/-- The even partition stabilizer has its literal S₃ two-core quotient. -/
theorem even_stabilizer_quotient (p : Partition 7 4 ![2,2,2,1]) :
    Nonempty (((alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup Perm7) ⧸
      pCore 2 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup Perm7)) ≃* Perm (Fin 3)) := by
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hA : (alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom = alternatingGroup (Fin 7) :=
    Normal.map_conj_eq _ c
  have he : (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)).map
      (MulAut.conj c).toMonoidHom = alternatingGroup (Fin 7) ⊓ p.stabilizer := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective,hA,hc]
  let t := ((MulAut.conj c).subgroupMap
    (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7))).trans (MulEquiv.subgroupCongr he)
  let u := (t.symm.trans (MulEquiv.ofBijective evenModelSeven evenModelSeven_bijective).symm).trans evenModelEquiv
  exact ⟨(QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans a6SynthemeCoreQuotientEquiv⟩
end CFSG.Quasithin.Chapter15.Section01.SevenPartition