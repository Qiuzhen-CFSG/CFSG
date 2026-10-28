module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.PairOrder
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Elementary-pair incidence from double-coset obstructions

An overgroup of order 2304 cannot contain an element with nonidentity 2304th
power. A double-coset cover through a subgroup P therefore confines the
overgroup to the union of two candidate subgroups, provided every other
representative has such a witness in its join with P. A subgroup contained
in a union of two subgroups lies in one of them.

When P has order 256, the proved ambient order makes P Sylow. Sylow conjugacy
moves an arbitrary elementary pair product to an overgroup of P; the existing
pair-order theorem and the preceding argument finish the conditional reduction.
No double-coset coverage, candidate membership, or power witness is assumed
without an explicit hypothesis. The concrete certificates remain separate.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528
of refs/quasithin.pdf, citing Aschbacher, Overgroups of Sylow subgroups in
sporadic groups (1986). The counting and union arguments here are elementary.
-/

open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Theory.GroupTheory.SubgroupEnumeration
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup

private theorem le_one_of_two_of_mem_union {G : Type*} [Group G]
    (K B C : Subgroup G) (h : ∀ x ∈ K, x ∈ B ∨ x ∈ C) : K ≤ B ∨ K ≤ C := by
  classical
  by_cases hB : K ≤ B
  · exact Or.inl hB
  · right
    obtain ⟨b, hbK, hbB⟩ := SetLike.not_le_iff_exists.mp hB
    have hbC := (h b hbK).resolve_left hbB
    intro x hxK
    by_contra hxC
    have hxB := (h x hxK).resolve_right hxC
    rcases h (b * x) (K.mul_mem hbK hxK) with hbxB | hbxC
    · exact hbB ((B.mul_mem_cancel_right hxB).mp hbxB)
    · exact hxC ((C.mul_mem_cancel_left hbC).mp hbxC)

/-- A subgroup whose order is n cannot contain an element whose nth power is nontrivial. -/
private theorem pow_eq_one_of_card {G : Type*} [Group G] (K : Subgroup G)
    {n : ℕ} (hK : Nat.card K = n) {x : G} (hx : x ∈ K) : x ^ n = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : K)))
  change x ^ Nat.card K = 1 at h
  rwa [hK] at h

/-- Double cosets inside either candidate, or with an incompatible power witness,
cover every order-2304 overgroup of the distinguished subgroup. -/
public theorem involutionMatrixOvergroup_le_of_doubleCosetObstructions {ι : Type*}
    (P : Subgroup LowerBound.quotientSubgroup)
    (rep : ι → LowerBound.quotientSubgroup)
    (hPB : P ≤ involutionMatrixLineStabilizer)
    (hPC : P ≤ involutionMatrixSecondSubgroup)
    (hcover : DoubleCosetCover P rep)
    (hrep : ∀ j, rep j ∈ involutionMatrixLineStabilizer ∨
      rep j ∈ involutionMatrixSecondSubgroup ∨
      ∃ x ∈ P ⊔ Subgroup.zpowers (rep j), x ^ 2304 ≠ 1)
    (K : Subgroup LowerBound.quotientSubgroup) (hPK : P ≤ K)
    (hK : Nat.card K = 2304) :
    K ≤ involutionMatrixLineStabilizer ∨ K ≤ involutionMatrixSecondSubgroup := by
  apply le_one_of_two_of_mem_union
  intro x hx
  obtain ⟨j, a, b, ha, hb, hxab⟩ := hcover x
  have hrK : rep j ∈ K := by
    rw [hxab] at hx
    exact (K.mul_mem_cancel_left (hPK ha)).mp
      ((K.mul_mem_cancel_right (hPK hb)).mp hx)
  rcases hrep j with hrB | hrC | ⟨y, hy, hyne⟩
  · left
    rw [hxab]
    exact involutionMatrixLineStabilizer.mul_mem
      (involutionMatrixLineStabilizer.mul_mem (hPB ha) hrB) (hPB hb)
  · right
    rw [hxab]
    exact involutionMatrixSecondSubgroup.mul_mem
      (involutionMatrixSecondSubgroup.mul_mem (hPC ha) hrC) (hPC hb)
  · exact (hyne (pow_eq_one_of_card K hK
      ((sup_le hPK (Subgroup.zpowers_le.mpr hrK)) hy))).elim

/-- Sylow conjugacy transports a certified two-candidate double-coset calculation
to every elementary pair in the actual matrix quotient. -/
public theorem elementaryMatrixIncidence_of_doubleCosetObstructions {ι : Type*}
    (P : Subgroup LowerBound.quotientSubgroup)
    (rep : ι → LowerBound.quotientSubgroup)
    (hP : Nat.card P = 256)
    (hPB : P ≤ involutionMatrixLineStabilizer)
    (hPC : P ≤ involutionMatrixSecondSubgroup)
    (hcover : DoubleCosetCover P rep)
    (hrep : ∀ j, rep j ∈ involutionMatrixLineStabilizer ∨
      rep j ∈ involutionMatrixSecondSubgroup ∨
      ∃ x ∈ P ⊔ Subgroup.zpowers (rep j), x ^ 2304 ≠ 1) :
    ElementaryMatrixIncidence := by
  classical
  have hfac : Nat.factorization 2661120 2 = 8 := by decide +kernel
  let T : Sylow 2 LowerBound.quotientSubgroup := Sylow.ofCard P (by
    rw [involutionMatrixQuotient_card, hfac, hP]
    rfl)
  intro S R hE hR hp
  let K : Subgroup LowerBound.quotientSubgroup := R ⊔ S.toSubgroup
  have hK : Nat.card K = 2304 := involutionMatrixPair_card S R hE hR hp
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq LowerBound.quotientSubgroup S T
  let L := K.map (MulAut.conj u).toMonoidHom
  have hPL : P ≤ L := by
    have h := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom)
      (show S.toSubgroup ≤ K from le_sup_right)
    have hu' : S.toSubgroup.map (MulAut.conj u).toMonoidHom = P :=
      congrArg Sylow.toSubgroup hu
    rwa [hu'] at h
  have hL : Nat.card L = 2304 :=
    (Nat.card_congr (K.equivMapOfInjective _ (MulAut.conj u).injective).toEquiv).symm.trans hK
  have hLC := involutionMatrixOvergroup_le_of_doubleCosetObstructions P rep hPB hPC
    hcover hrep L hPL hL
  have hm : ∃ i : Bool, L ≤ involutionMatrixCandidate i := by
    rcases hLC with hB | hC
    · exact ⟨false, hB⟩
    · exact ⟨true, hC⟩
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, u⁻¹, ?_⟩
  intro x hx
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj u) x,
    hi (Subgroup.mem_map_of_mem _ hx), ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
