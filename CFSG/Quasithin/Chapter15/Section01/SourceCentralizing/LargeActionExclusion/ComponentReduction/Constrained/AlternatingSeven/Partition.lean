module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.Representation.BinaryPermutation.PairedPartition

/-!
# Relabeling the actual three-pair partition

Two partitions with the same ordered sizes are related by a permutation:
identify their disjoint sums part by part. For sizes 2,2,2,1 the standard
partition is the orbit partition of the triple transposition. The source
partition stabilizer is consequently a conjugate of its centralizer.
This supplies the coordinate transport required by the A₇ block argument.

Source: Aschbacher--Smith 15.1.25(5), printed p.1102.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private def partitionSumEquiv {n k : ℕ} {sizes : Fin k → ℕ}
    (p : Partition n k sizes) : (Σ i, p.part i) ≃ Fin n :=
  Equiv.ofBijective (fun x => x.2.val) ⟨by
    rintro ⟨i,x,hx⟩ ⟨j,y,hy⟩ he
    dsimp at he
    subst y
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (p.disjoint hne)) hx hy
    subst j
    rfl,
    fun x => by obtain ⟨i,hi⟩ := p.cover x; exact ⟨⟨i,x,hi⟩,rfl⟩⟩

/-- Partitions with the same list of part sizes admit a simultaneous labeling. -/
theorem Partition.exists_perm_parts {n k : ℕ} {sizes : Fin k → ℕ}
    (p q : Partition n k sizes) :
    ∃ c : Equiv.Perm (Fin n), ∀ i, c • p.part i = q.part i := by
  let E : (Σ i, p.part i) ≃ (Σ i, q.part i) :=
    Equiv.sigmaCongrRight (fun i => Finset.equivOfCardEq ((p.card i).trans (q.card i).symm))
  let c := (partitionSumEquiv p).symm.trans (E.trans (partitionSumEquiv q))
  refine ⟨c,?_⟩
  intro i
  have hc (x : p.part i) : c x =
      (Finset.equivOfCardEq ((p.card i).trans (q.card i).symm) x).val := by
    change c (partitionSumEquiv p ⟨i,x⟩) = _
    simp only [c,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hx
    change c y ∈ q.part i
    rw [hc ⟨y,hy⟩]
    exact (Finset.equivOfCardEq ((p.card i).trans (q.card i).symm) ⟨y,hy⟩).property
  · intro hx
    let y := (Finset.equivOfCardEq ((p.card i).trans (q.card i).symm)).symm ⟨x,hx⟩
    apply Finset.mem_smul_finset.mpr
    refine ⟨y,y.property,?_⟩
    change c y = x
    rw [hc y]
    exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

open AlternatingSeven.ThreeResidualLocals
private def pairedPartition : Partition 7 4 ![2,2,2,1] where
  part := ![{0,1},{2,3},{4,5},{6}]
  card := by decide +kernel
  disjoint := by change ∀ i j, i ≠ j → _; decide +kernel
  cover := by decide +kernel

private theorem stabilizer_coe_parts {n k : ℕ} {sizes : Fin k → ℕ}
    (p : Partition n k sizes) : p.stabilizer =
      MulAction.stabilizer (Equiv.Perm (Fin n))
        (Set.range (fun i => (p.part i : Set (Fin n)))) := by
  ext g
  change g • Set.range p.part = Set.range p.part ↔
    g • Set.range (fun i => (p.part i : Set (Fin n))) = _
  have hi : Function.Injective (fun s : Set (Finset (Fin n)) =>
      (fun t : Finset (Fin n) => (t : Set (Fin n))) '' s) :=
    Set.image_injective.mpr Finset.coe_injective
  have he (s : Set (Finset (Fin n))) :
      (fun t : Finset (Fin n) => (t : Set (Fin n))) '' (g • s) =
      g • ((fun t : Finset (Fin n) => (t : Set (Fin n))) '' s) := by
    ext t
    constructor
    · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨(v : Set (Fin n)),⟨v,hv,rfl⟩,(Finset.coe_smul_finset g v).symm⟩
    · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨g • v,⟨v,hv,rfl⟩,Finset.coe_smul_finset g v⟩
  rw [← hi.eq_iff]
  rw [he,← Set.range_comp]
  rfl

private theorem pairedPartition_stabilizer :
    pairedPartition.stabilizer = centralizer ({pairing} : Set Perm7) := by
  rw [stabilizer_coe_parts,centralizer_eq_pairPartitionStabilizer pairing pairing_sq]
  congr 1
  ext s
  change (∃ i : Fin 4, (pairedPartition.part i : Set (Fin 7)) = s) ↔
    ∃ x : Fin 7, ({x,pairing x} : Set (Fin 7)) = s
  have h1 : ∀ i : Fin 4, ∃ x : Fin 7,
      pairedPartition.part i = {x,pairing x} := by decide +kernel
  have h2 : ∀ x : Fin 7, ∃ i : Fin 4,
      ({x,pairing x} : Finset (Fin 7)) = pairedPartition.part i := by decide +kernel
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨x,hx⟩ := h1 i
    exact ⟨x,by rw [hx]; simp only [Finset.coe_pair]⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨i,hi⟩ := h2 x
    exact ⟨i,by rw [←hi]; simp only [Finset.coe_pair]⟩

/-- Every source partition is a conjugate of the literal standard pairing. -/
theorem Partition.three_pairs_stabilizer (p : Partition 7 4 ![2,2,2,1]) :
    ∃ c : Perm7, p.stabilizer =
      (centralizer ({pairing} : Set Perm7)).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c,hc⟩ := pairedPartition.exists_perm_parts p
  refine ⟨c,?_⟩
  rw [← pairedPartition_stabilizer]
  have he : Set.range p.part = c • Set.range pairedPartition.part := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨pairedPartition.part i,⟨i,rfl⟩,hc i⟩
    · rintro ⟨w,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(hc i).symm⟩
  change MulAction.stabilizer Perm7 (Set.range p.part) = _
  rw [he,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
