module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.AlgebraicGroup.RootData.Realization
/-!
# Generation by the torus and signed simple D4 roots

The Chevalley reflection words transport both signs of a root group. Induction
on the standard root system therefore places every root group in any subgroup
containing the signed simple roots. The supplied opposite big cell then gives
generation together with the actual torus. No concrete D4 model is used.

Source: GLS3 Chapter 1, §§1.11–1.12, and Steinberg, *Representations of
Algebraic Groups* (1963), §§2 and 4.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
@[expose] public noncomputable section
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]
/-- The root indexed by a numbered vertex of the fixed D4 base. -/
def simpleRoot (S : D4Geometry K) (i : Fin 4) : S.roots.Root :=
  S.rootEquiv.symm (typeDSimpleRootIndex 2 i)

/-- The numbered simple roots belong to the unchanged positive system. -/
theorem simpleRoot_positive (S : D4Geometry K) (i : Fin 4) :
    simpleRoot S i ∈ S.roots.positive := by
  have hs : simpleRoot S i ∈ S.roots.simple := by
    apply (S.based.2.2.2.1 _).mpr
    simpa only [simpleRoot, Equiv.apply_symm_apply, ← typeDRootPairing_baseEquiv_val] using
      (typeDRootPairing_baseEquiv 2 i).property
  exact ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 _).mp hs).1

private theorem equiv_neg (S : D4Geometry K) (α : S.roots.Root) :
    (typeDRootPairing 2).root (S.rootEquiv (S.roots.neg α)) =
      -(typeDRootPairing 2).root (S.rootEquiv α) := by
  rw [S.based.2.2.1, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]

private theorem reflect_neg (S : D4Geometry K) (α β : S.roots.Root) :
    S.roots.reflect β (S.roots.neg α) = S.roots.neg (S.roots.reflect β α) := by
  apply S.rootEquiv.injective
  apply (typeDRootPairing 2).root.injective
  rw [S.based.2.1, RootPairing.root_reflectionPerm, equiv_neg,
    map_neg, equiv_neg, S.based.2.1, RootPairing.root_reflectionPerm]

private theorem simple_n_mem (S : D4Geometry K) (H : Subgroup K.Point)
    (i : Fin 4)
    (hpos : ∀ t, S.chevalley.x (simpleRoot S i) t ∈ H)
    (hneg : ∀ t, S.chevalley.x (S.roots.neg (simpleRoot S i)) t ∈ H) :
    S.chevalley.n (simpleRoot S i) 1 ∈ H := by
  rw [S.chevalley_spec.2.1]
  exact H.mul_mem (H.mul_mem (hpos _) (hneg _)) (hpos _)

private theorem reflect_mem [CharP k 2] (S : D4Geometry K) (H : Subgroup K.Point)
    (α β : S.roots.Root) (hn : S.chevalley.n β 1 ∈ H)
    (hx : ∀ t, S.chevalley.x α t ∈ H) :
    ∀ t, S.chevalley.x (S.roots.reflect β α) t ∈ H := by
  obtain ⟨sgn, hs, hxconj, _⟩ := S.chevalley_spec.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs1 : (sgn α β : k) = 1 := by
    rcases hs α β with h | h
    · rw [h, Units.val_one]
    · rw [h, Units.val_neg, Units.val_one, CharTwo.neg_eq]
  intro t
  have he := hxconj α β t
  rw [hs1, one_mul] at he
  rw [← he]
  exact H.mul_mem (H.mul_mem (H.inv_mem hn) (hx t)) hn

/-- The actual torus and signed simple root groups generate the point group. -/
theorem subgroup_eq_top_of_torus_and_simple_roots [IsAlgClosed k] [CharP k 2] (S : D4Geometry K)
    (H : Subgroup K.Point) (hT : S.torus.toSubgroup ≤ H)
    (hp : ∀ i t, S.chevalley.x (simpleRoot S i) t ∈ H)
    (hn : ∀ i t, S.chevalley.x (S.roots.neg (simpleRoot S i)) t ∈ H) : H = ⊤ := by
  have hbase (j : TypeDRootIndex 4) (hj : j ∈ (typeDRootPairing_base 2).support) :
      ∃ i, S.rootEquiv.symm j = simpleRoot S i := by
    obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
    refine ⟨i, ?_⟩
    have hi' := congrArg Subtype.val hi
    simpa only [typeDRootPairing_baseEquiv_val, simpleRoot] using
      congrArg S.rootEquiv.symm hi'.symm
  have hall (j : TypeDRootIndex 4) :
      (∀ t, S.chevalley.x (S.rootEquiv.symm j) t ∈ H) ∧
      (∀ t, S.chevalley.x (S.roots.neg (S.rootEquiv.symm j)) t ∈ H) := by
    apply (typeDRootPairing_base 2).induction_reflect j
    · intro j hj
      have he : S.rootEquiv.symm ((typeDRootPairing 2).reflectionPerm j j) =
          S.roots.neg (S.rootEquiv.symm j) := by
        apply S.rootEquiv.injective
        simp only [Equiv.apply_symm_apply, S.based.2.2.1]
      rw [he, S.realized.neg_neg]
      exact ⟨hj.2, hj.1⟩
    · intro j hj
      obtain ⟨i, hi⟩ := hbase j hj
      rw [hi]
      exact ⟨hp i, hn i⟩
    · intro j b hj hb
      obtain ⟨i, hi⟩ := hbase b hb
      have he : S.rootEquiv.symm ((typeDRootPairing 2).reflectionPerm b j) =
          S.roots.reflect (simpleRoot S i) (S.rootEquiv.symm j) := by
        apply S.rootEquiv.injective
        rw [Equiv.apply_symm_apply, S.based.2.1, ← hi]
        simp only [Equiv.apply_symm_apply]
      rw [he, ← reflect_neg]
      exact ⟨reflect_mem S H _ _ (simple_n_mem S H i (hp i) (hn i)) hj.1,
        reflect_mem S H _ _ (simple_n_mem S H i (hp i) (hn i)) hj.2⟩
  let : PreirreducibleSpace K.Point :=
    ⟨(connectedAlgebraicGroup_irreducible K S.simple.1).2⟩
  apply top_unique
  rw [← S.bigCell.generated_eq_top_of_dense S.simple.1]
  apply sup_le _ hT
  apply (RootSubgroupGenerated_le_iff _ _ _).mpr
  intro α _ x hx
  have hx' : x ∈ Set.range (S.chevalley.x α) := by
    rw [(S.chevalley_spec.1 α).2]
    exact hx
  obtain ⟨t, rfl⟩ := hx'
  simpa only [Equiv.symm_apply_apply] using (hall (S.rootEquiv α)).1 t
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
