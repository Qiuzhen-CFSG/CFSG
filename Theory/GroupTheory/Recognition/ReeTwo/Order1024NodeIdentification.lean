module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024NodeCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel

/-!
# Identification of the twenty-seven order-sixteen tail-quotient nodes

Every checked node has preimage equal to the canonical core or a conjugate
of one of the fifteen residual or three exceptional representatives. This
statement needs neither centricity nor exhaustiveness of the node list.

The word certificates identify the quotient images. All candidates contain
the tail, which is normal and is precisely the projection kernel, so taking
preimages recovers equality in the Sylow group. The root convention is
`rootOne = inr (generator 4)⁻¹`, whose quotient coordinate code is 48.

Source: the root generators in `Order1024ResidualRepresentatives` and
`Order1024Representatives`, and the Shinoda coordinate formulas (1975),
(2.3), pp. 81–82, implemented in `SylowTailQuotient`.
-/

namespace ReeTwo.SylowModel
open TailQuotient
namespace Order1024NodeIdentification

private def rootGenerator (j : Fin 18) : Fin 4 → SylowModel :=
  (![![root 3, root 2, root 0, rootOne ^ 2],
    ![root 3, root 2, root 1, rootOne ^ 2 * root 0],
    ![root 3, root 2, root 0 * root 1, rootOne ^ 2 * root 1],
    ![root 2 * root 3, root 1 * root 3, root 0, rootOne ^ 2],
    ![root 2 * root 3, root 1, root 0, rootOne ^ 2],
    ![root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2 * root 3],
    ![root 2 * root 3, root 1, root 0 * root 3, rootOne ^ 2 * root 3],
    ![root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2],
    ![root 2 * root 3, root 1 * root 3, root 0, rootOne ^ 2 * root 3],
    ![root 3, root 2, root 1, rootOne ^ 2],
    ![root 2 * root 3, root 1 * root 3, rootOne * root 0, rootOne * root 0],
    ![root 2 * root 3, root 1 * root 3, rootOne * root 0 * root 3,
      rootOne * root 0 * root 3],
    ![root 3, root 2, rootOne, rootOne],
    ![root 3, root 2, rootOne * root 0 * root 1, rootOne * root 0 * root 1],
    ![root 2 * root 3, root 1, rootOne * root 0 * root 3, rootOne * root 0 * root 3],
    ![root 2 * root 3, root 1 * root 3, rootOne, rootOne],
    ![root 2 * root 3, root 1 * root 3, rootOne * root 3, rootOne * root 3],
    ![root 2 * root 3, root 1, rootOne, rootOne]] j)

private def candidate (j : Fin 18) : Subgroup SylowModel :=
  tailSubgroup ⊔ Subgroup.closure (Set.range (rootGenerator j))

set_option maxRecDepth 100000 in
private theorem candidate_residual (j : Fin 15) :
    candidate (j.castAdd 3) = residualCandidate j := by
  fin_cases j <;>
    simp [candidate, rootGenerator, residualCandidate, Matrix.range_cons,
      Matrix.range_empty] <;>
    congr 2 <;> ext x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

set_option maxRecDepth 100000 in
private theorem candidate_exceptional (j : Fin 3) :
    candidate (j.natAdd 15) = exceptionalCandidate j := by
  fin_cases j <;>
    simp [candidate, rootGenerator, exceptionalCandidate, Matrix.range_cons,
      Matrix.range_empty] <;>
    congr 2 <;> ext x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem projection_rootGenerator : ∀ j k,
    projection (rootGenerator j k) = Order1024NodeCertificates.quotientGenerator j k := by
  intro j k
  apply coordinateCode_injective
  exact (by decide +kernel : ∀ j k,
    coordinateCode (projection (rootGenerator j k)) =
      coordinateCode (Order1024NodeCertificates.quotientGenerator j k)) j k

private theorem candidate_image (j : Fin 18) :
    (candidate j).map projection =
      Subgroup.closure (Set.range (Order1024NodeCertificates.quotientGenerator j)) := by
  have ht : tailSubgroup.map projection = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (le_of_eq ker_projection.symm)
  rw [candidate, Subgroup.map_sup, ht, bot_sup_eq, MonoidHom.map_closure,
    ← Set.range_comp']
  congr 2
  funext k
  exact projection_rootGenerator j k

private theorem tail_le_conjugate (j : Fin 18) (g : SylowModel) :
    tailSubgroup ≤ (candidate j).map (MulAut.conj g).toMonoidHom := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
  · apply (show tailSubgroup ≤ candidate j from le_sup_left)
    simpa only [inv_inv] using tailSubgroup_normal.conj_mem x hx g⁻¹
  · simp [MulAut.conj_apply, mul_assoc]

private theorem node_succ_preimage (i : Fin 26) :
    (Order16Nodes.node i.succ).comap projection =
      (candidate (Order1024NodeCertificates.representative i)).map
        (MulAut.conj (lift (coordinateElement
          (Order1024NodeCertificates.conjugatorCode i)))).toMonoidHom := by
  let j := Order1024NodeCertificates.representative i
  let g := lift (coordinateElement (Order1024NodeCertificates.conjugatorCode i))
  have himage : ((candidate j).map (MulAut.conj g).toMonoidHom).map projection =
      Order16Nodes.node i.succ := by
    rw [map_conjugate, candidate_image, MonoidHom.map_closure, ← Set.range_comp',
      Order1024NodeCertificates.node_eq_closure]
    congr 2
  rw [← himage, comap_map _ (tail_le_conjugate j g)]

/-- The zeroth node is the image of the canonical ten-root core. -/
public theorem node_zero_preimage :
    (Order16Nodes.node 0).comap projection = coreSubgroup := by
  have hzero : ∀ q : TailQuotient.Group, q ∈ Order16Nodes.node 0 ↔ q.right = 1 :=
    by decide +kernel
  ext x
  rw [Subgroup.mem_comap, hzero]
  change x.right = 1 ↔ x ∈ (SemidirectProduct.inl : Core →* SylowModel).range
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

/-- Every checked quotient-node preimage is one of the nineteen proposed
representatives up to conjugation. No centricity hypothesis is required. -/
public theorem node_preimage_identification (i : Fin 27) :
    (Order16Nodes.node i).comap projection = coreSubgroup ∨
      (∃ (j : Fin 15) (g : SylowModel),
        (Order16Nodes.node i).comap projection =
          (residualCandidate j).map (MulAut.conj g).toMonoidHom) ∨
      ∃ (j : Fin 3) (g : SylowModel),
        (Order16Nodes.node i).comap projection =
          (exceptionalCandidate j).map (MulAut.conj g).toMonoidHom := by
  refine Fin.cases (Or.inl node_zero_preimage) (fun k => ?_) i
  right
  have h := node_succ_preimage k
  let g := lift (coordinateElement (Order1024NodeCertificates.conjugatorCode k))
  generalize Order1024NodeCertificates.representative k = j at h
  revert h
  refine Fin.addCases (m := 15) (n := 3)
    (motive := fun j => (Order16Nodes.node k.succ).comap projection =
      (candidate j).map (MulAut.conj g).toMonoidHom → _)
    (fun r h => ?_) (fun e h => ?_) j
  · exact Or.inl ⟨r, g, by simpa only [candidate_residual] using h⟩
  · exact Or.inr ⟨e, g, by simpa only [candidate_exceptional] using h⟩

end Order1024NodeIdentification
end ReeTwo.SylowModel
