module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Certificates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates.Classification
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates.Local
/-!
# The outer-actor certificate in the explicit PSL₃(3) graph Sylow

Every outer elementary actor of rank at least two is one of thirteen
four-groups or two eight-groups. Explicit inner conjugators fuse each whole
actor to one of three rows. Their coordinate centralizers establish both
containment clauses, and a nonidentity cubic commutator proves escape from
the intrinsic local two-core of order eight.

This discharges the actor premise of
`centralizerPlacement_outer_of_standard_certificates`. The independent
intersection-order and generation certificate belongs to the local calculation.

Source: Aschbacher–Smith E.1.2/E.1.5/E.1.14(7), printed pp.209–210, 214;
Asc82a Lemma 4.11. All coordinates and conjugators are checked in the literal
graph extension; the original actor, including rank-three actors, is retained.
-/

public section

open Subgroup Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
open OuterActors OuterActors.ActorCertificates

private theorem fused_actor_mem (A : Subgroup G) (hAS : A ≤ standardSubgroup)
    (n : Fin 15) (hn : ∀ i, element i ∈ A ↔ i ∈ actor n) (x : G) :
    x ∈ A.map (MulAut.conj (inner (conjugatorMatrix n))).toMonoidHom ↔
      ∃ i ∈ actor (target n), element i = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := hAS ha
    refine ⟨fuse n i, ?_, (conjugate_element n i ((hn i).mp ha)).symm⟩
    rw [← fuse_image]
    exact Finset.mem_image.mpr ⟨i, (hn i).mp ha, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rw [← fuse_image] at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨element j, (hn j).mpr hj, conjugate_element n j hj⟩

/-- Every whole outer elementary actor of rank at least two can be placed in
the selected literal graph centralizer, with the required Sylow centralizer
containment and nontrivial image modulo its intrinsic two-core. -/
theorem standardOuterActorCertificates : StandardOuterActorCertificates := by
  intro A hA hAS hr hout
  obtain ⟨n, hn⟩ := actor_complete A hA hAS hr hout
  let B := A.map (MulAut.conj (inner (conjugatorMatrix n))).toMonoidHom
  have hB (x : G) : x ∈ B ↔ ∃ i ∈ actor (target n), element i = x :=
    fused_actor_mem A hAS n hn x
  have hBK : B ≤ K := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hB x).mp hx
    rw [K, localSubgroup_marker]
    exact mem_centralizer_singleton_iff.mpr
      ((element_commute_iff i (13,true)).mpr (target_local n i hi))
  refine ⟨inner (conjugatorMatrix n), ?_, hBK, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := (hB x).mp hx
    exact element_mem_standardSubgroup i
  · rintro x ⟨hxS, hxC⟩
    obtain ⟨i, rfl⟩ := hxS
    rw [localSubgroup_marker]
    apply mem_centralizer_singleton_iff.mpr
    apply (element_commute_iff i (13,true)).mpr
    apply target_centralizer n i
    intro j hj
    apply (element_commute_iff i j).mp
    exact (mem_centralizer_iff.mp hxC (element j) ((hB _).mpr ⟨j, hj, rfl⟩)).symm
  · intro hcore
    have haB : element (escapeIndex n) ∈ B :=
      (hB _).mpr ⟨escapeIndex n, escape_mem n, rfl⟩
    exact escape_not_mem_core n (hBK haB) (hcore haB)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
