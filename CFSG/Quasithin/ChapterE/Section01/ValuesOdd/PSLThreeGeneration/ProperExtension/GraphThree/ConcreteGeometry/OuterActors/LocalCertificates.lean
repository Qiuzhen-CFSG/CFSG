module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Certificates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.LocalCertificates.Words

/-!
# Intersection and generation for the selected graph centralizer

The standard Sylow has coordinates `Fin 16 × Bool`. Commutation with its
coordinate `(13,true)` cuts out exactly sixteen coordinates, giving the
order of its intersection with the literal graph-involution centralizer.
The extra matrix of `Words` commutes with that marker. Its checked generating
words give the whole inner subgroup, and the graph element already lies in
the Sylow. The inner/graph normal form therefore proves generation of the
literal graph extension.

This discharges the local certificate used by the outer-actor placement
assembly. The separate actor-placement certificate is not a premise here.

Source: Aschbacher–Smith E.1.2, E.1.5, E.1.14(7), printed pp.209–210, 214;
Asc82a Lemma 4.11.
-/

public section
open Subgroup Matrix.PSL3Three Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
open OuterActors
set_option maxRecDepth 10000

private theorem selected_mem_iff (i : Index) :
    element i ∈ localSubgroup (localConjugator true) ↔
      multiply i (13,true) = multiply (13,true) i := by
  rw [localSubgroup_marker, mem_centralizer_singleton_iff]
  exact element_commute_iff i (13,true)

private noncomputable def intersectionEquiv :
    {i : Index // multiply i (13,true) = multiply (13,true) i} ≃
      standardSubgroup.subgroupOf (localSubgroup (localConjugator true)) :=
  Equiv.ofBijective
    (fun i => ⟨⟨element i.val, (selected_mem_iff i.val).mpr i.property⟩,
      element_mem_standardSubgroup i.val⟩)
    ⟨by
      intro i j h
      exact Subtype.ext (element_injective (congrArg (fun x => x.val.val) h)), by
      rintro ⟨⟨x,hK⟩,hS⟩
      change ∃ i, element i = x at hS
      obtain ⟨i,hi⟩ := hS
      refine ⟨⟨i, (selected_mem_iff i).mp (hi.symm ▸ hK)⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hi)⟩

private theorem selected_intersection_card :
    Nat.card (standardSubgroup.subgroupOf (localSubgroup (localConjugator true))) = 16 := by
  rw [← Nat.card_congr intersectionEquiv, Nat.card_eq_fintype_card]
  decide +kernel

private theorem extra_mem_local :
    inner LocalCertificates.extra ∈ localSubgroup (localConjugator true) := by
  rw [localSubgroup_marker, mem_centralizer_singleton_iff]
  have hm : LocalCertificates.extra * twoElement 13 =
      twoElement 13 * graphSL (ZMod 3) LocalCertificates.extra := by
    apply Subtype.ext
    decide +kernel
  change pair LocalCertificates.extra false * pair (twoElement 13) true =
    pair (twoElement 13) true * pair LocalCertificates.extra false
  rw [pair_mul, pair_mul]
  change pair (LocalCertificates.extra * twoElement 13) true =
    pair (twoElement 13 * graphSL (ZMod 3) LocalCertificates.extra) true
  rw [hm]

private theorem selected_generation :
    standardSubgroup ⊔ localSubgroup (localConjugator true) = ⊤ := by
  let H := standardSubgroup ⊔ localSubgroup (localConjugator true)
  have hi (i : Fin 16) : inner (twoElement i) ∈ H := by
    apply mem_sup_left
    simpa only [element, pair, Bool.false_eq_true, ↓reduceIte, mul_one] using
      element_mem_standardSubgroup (i,false)
  have hSL : H.comap inner = ⊤ := by
    apply LocalCertificates.eq_top_of_twoElement_extra_mem
    · exact hi 1
    · exact hi 8
    · exact mem_sup_right extra_mem_local
  have hzero : twoElement 0 = 1 := Subtype.ext (by decide +kernel)
  have hg : graphElement ∈ H := by
    apply mem_sup_left
    simpa only [element, pair, ↓reduceIte, hzero, map_one,
      one_mul] using element_mem_standardSubgroup (0,true)
  apply top_unique
  intro x _
  obtain ⟨⟨a,b⟩,rfl⟩ := pair_surjective x
  apply H.mul_mem
  · have ha : a ∈ H.comap inner := by rw [hSL]; trivial
    exact ha
  · cases b
    · exact H.one_mem
    · exact hg

/-- The exact intersection and generation certificate for the selected graph
centralizer, with no actor-placement or classification premises. -/
theorem standardLocalCertificates : StandardLocalCertificates :=
  ⟨selected_intersection_card, selected_generation⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
