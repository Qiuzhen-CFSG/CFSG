module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Partition
public import Theory.Representation.BinarySevenCode.PermutationAction

/-!
# Three-pair partitions over seven-letter two-subgroups

The full three-pair stabilizer has order 48, hence contains a Sylow
of S₇. Sylow conjugacy places every two-subgroup in a relabeled partition.
Its even subgroup contains the paired A₄, which fixes no weight-two word:
the two explicit generators force constant coordinates on the six-letter
orbit. The calculation checks only binary words and specified permutations.

Source: Aschbacher--Smith 15.1.22(1), printed pp.1098--1099.
-/

public section
open Subgroup Equiv
open scoped Pointwise
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals BinarySevenCode
namespace CFSG.Quasithin.Chapter15.Section01.SevenPartition

private def relabel (p : Partition 7 4 ![2,2,2,1]) (c : Perm7) :
    Partition 7 4 ![2,2,2,1] where
  part i := c • p.part i
  card i := (Finset.card_smul_finset c _).trans (p.card i)
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,hax⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨b,hb,hbx⟩ := Finset.mem_smul_finset.mp hy
    have hab : a = b := c.injective (hax.trans hbx.symm)
    exact Finset.disjoint_left.mp (p.disjoint hij) ha (hab.symm ▸ hb)
  cover x := by
    obtain ⟨i,hi⟩ := p.cover (c.symm x)
    exact ⟨i,Finset.mem_smul_finset.mpr ⟨c.symm x,hi,c.apply_symm_apply x⟩⟩

private theorem relabel_stabilizer (p : Partition 7 4 ![2,2,2,1]) (c : Perm7) :
    (relabel p c).stabilizer = p.stabilizer.map (MulAut.conj c).toMonoidHom := by
  have he : Set.range (relabel p c).part = c • Set.range p.part := by
    ext s
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨p.part i,⟨i,rfl⟩,rfl⟩
    · rintro ⟨s,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  change MulAction.stabilizer Perm7 (Set.range (relabel p c).part) = _
  rw [he,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

/-- The full stabilizer has order 48. -/
theorem stabilizer_card (p : Partition 7 4 ![2,2,2,1]) :
    Nat.card p.stabilizer = 48 := by
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  rw [hc,card_map_of_injective (MulAut.conj c).injective,centralizer_pairing_card]

/-- Every seven-letter two-subgroup preserves a partition of type 2,2,2,1. -/
theorem exists_partition (R : Subgroup Perm7) (hR : IsPGroup 2 R) :
    ∃ p : Partition 7 4 ![2,2,2,1], R ≤ p.stabilizer := by
  classical
  let p : Partition 7 4 ![2,2,2,1] := {
    part := ![{0,1},{2,3},{4,5},{6}]
    card := by decide +kernel
    disjoint := by change ∀ i j, i ≠ j → _; decide +kernel
    cover := by decide +kernel }
  let Q : Sylow 2 p.stabilizer := Classical.choice inferInstance
  let Q0 : Subgroup Perm7 := (Q : Subgroup p.stabilizer).map p.stabilizer.subtype
  have hcard : Nat.card Q0 = 16 := by
    rw [card_map_of_injective p.stabilizer.subtype_injective,Q.card_eq_multiplicity,
      stabilizer_card]
    decide +kernel
  let Q1 : Sylow 2 Perm7 := Sylow.ofCard Q0 (by
    rw [hcard,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide +kernel)
  obtain ⟨R1,hRR⟩ := hR.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq Perm7 Q1 R1
  refine ⟨relabel p c,hRR.trans ?_⟩
  rw [relabel_stabilizer,←hc]
  exact map_mono (map_subtype_le _)

private theorem paired_generators_no_weight_two (w : EvenWord)
    (h3 : evenRepresentation pairedThree w = w)
    (h2 : evenRepresentation fourFlip w = w) : weight w.val ≠ 2 := by
  have hh : ∀ v : Word,
      (∀ i, v (pairedThree.symm i) = v i) →
      (∀ i, v (fourFlip.symm i) = v i) → weight v ≠ 2 := by decide +kernel
  exact hh w.val (fun i => congrArg (fun x : EvenWord => x.val i) h3)
    (fun i => congrArg (fun x : EvenWord => x.val i) h2)

/-- The even partition stabilizer moves every weight-two word. -/
theorem partition_moves_weight_two (p : Partition 7 4 ![2,2,2,1])
    (w : EvenWord) (hw : weight w.val = 2) :
    ∃ g ∈ alternatingGroup (Fin 7) ⊓ p.stabilizer, evenRepresentation g w ≠ w := by
  by_contra! hn
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  let v := evenRepresentation c⁻¹ w
  have hfix (g : Perm7) (hg : g ∈ pairedFour) : evenRepresentation g v = v := by
    have hh := hn (c * g * c⁻¹) ⟨by
      exact (mem_normalizer_iff.mp ((alternatingGroup (Fin 7)).normalizer_eq_top ▸
        mem_top c) _).mp (models_le_alternating.2.2 hg),by
      rw [hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom
        (pairedFour_le_centralizer_pairing hg)⟩
    have ht := congrArg (evenRepresentation c⁻¹) hh
    change evenRepresentation g (evenRepresentation c⁻¹ w) = _
    simpa only [←Module.End.mul_apply,←map_mul,←mul_assoc,inv_mul_cancel,one_mul] using ht
  have hne := paired_generators_no_weight_two v
    (hfix pairedThree (subset_closure (by simp)))
    (hfix fourFlip (subset_closure (by simp)))
  exact hne ((weight_evenRepresentation c⁻¹ w).trans hw)

end CFSG.Quasithin.Chapter15.Section01.SevenPartition
