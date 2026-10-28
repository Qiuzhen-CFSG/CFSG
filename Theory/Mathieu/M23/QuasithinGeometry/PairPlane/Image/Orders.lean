module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Stabilizers
public import Theory.Mathieu.M23.Properties.Transitivity
public import Theory.Mathieu.M23.Properties.Order

/-!
# Orders of the setwise and pointwise pair stabilizers in M23

Two-transitivity gives all 253 unordered pairs in the orbit and realizes both
permutations of the deleted pair. Orbit--stabilizer gives orders 40320 and
20160, respectively. These are the orders used in the field-plane image
comparison (Aschbacher, *Sporadic Groups*, §18).
-/

set_option maxRecDepth 10000

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage
open scoped Pointwise

private theorem twoPretransitive : MulAction.IsMultiplyPretransitive M23 (Fin 23) 2 := by
  let := m23_isFourPretransitive
  exact MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4) (by simp)

/-- Every pair is an M23 translate of the distinguished pair. -/
theorem exists_smul_pair_eq (P : Finset (Fin 23)) (hP : P.card = 2) :
    ∃ g : M23, g • x.val = P := by
  classical
  let e : Fin 2 ≃ x.val := (Fintype.equivFinOfCardEq (by simp [x.property])).symm
  let f : Fin 2 ≃ P := (Fintype.equivFinOfCardEq (by simp [hP])).symm
  let a : Fin 2 ↪ Fin 23 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin 2 ↪ Fin 23 := f.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp twoPretransitive) a b
  have happ (i : Fin 2) : g • (e i).val = (f i).val :=
    congrArg (fun v : Fin 2 ↪ Fin 23 => v i) hg
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.mp hz
    obtain ⟨i, hi⟩ := e.surjective ⟨w, hw⟩
    have hi' : (e i).val = w := congrArg Subtype.val hi
    rw [← hi', happ]
    exact (f i).property
  · rw [Finset.card_smul_finset, hP, x.property]

/-- All 253 pairs occur in the orbit. -/
theorem orbit_pair : MulAction.orbit M23 x.val =
    ↑((Finset.univ : Finset (Fin 23)).powersetCard 2) := by
  ext P
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, Finset.mem_powersetCard]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Finset.subset_univ _, (Finset.card_smul_finset _ _).trans x.property⟩
  · rintro ⟨_, hP⟩
    exact exists_smul_pair_eq P hP

theorem pairStabilizer_index : pairStabilizer.index = 253 := by
  rw [MulAction.index_stabilizer, orbit_pair, Set.ncard_coe_finset,
    Finset.card_powersetCard]
  decide +kernel

/-- The setwise stabilizer has the order of PSL(3,4) extended by Frobenius. -/
theorem pairStabilizer_card : Nat.card pairStabilizer = 40320 := by
  have h := Subgroup.card_mul_index pairStabilizer
  rw [pairStabilizer_index, m23_order] at h
  omega

/-- The deleted-pair action realizes its full symmetric group. -/
theorem pairSetAction_surjective : Function.Surjective (setAction x.val) := by
  classical
  let e : Fin 2 ≃ x.val := (Fintype.equivFinOfCardEq (by simp [x.property])).symm
  intro σ
  let a : Fin 2 ↪ Fin 23 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin 2 ↪ Fin 23 := (e.trans σ).toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp twoPretransitive) a b
  have happ (i : Fin 2) : g • (e i).val = (σ (e i)).val :=
    congrArg (fun v : Fin 2 ↪ Fin 23 => v i) hg
  have hact (z : x.val) : g • z.val = (σ z).val := by
    obtain ⟨i, rfl⟩ := e.surjective z
    exact happ i
  have hfix : g ∈ pairStabilizer := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro z hz
    rw [hact ⟨z, hz⟩]
    exact (σ ⟨z, hz⟩).property
  refine ⟨⟨g, hfix⟩, ?_⟩
  apply Equiv.ext
  intro z
  exact Subtype.ext (hact z)

theorem pointwisePairStabilizer_index : pointwisePairStabilizer.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr pairSetAction_surjective,
    Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [x.property]

/-- The pointwise stabilizer has the order of PSL(3,4). -/
theorem pointwisePairStabilizer_card : Nat.card pointwisePairStabilizer = 20160 := by
  have h := Subgroup.card_mul_index pointwisePairStabilizer
  rw [pointwisePairStabilizer_index, pairStabilizer_card] at h
  omega

end Sporadic.Mathieu.M23Geometry.PairPlaneImage
