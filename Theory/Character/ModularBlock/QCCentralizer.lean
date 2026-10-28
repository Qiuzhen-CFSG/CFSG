module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# A subgroup and its centralizer inside the normalizer

For a subgroup Q of G, the join Q C_G(Q) is normal in N_G(Q), and both
factors are normal in the join. If Q is given inside H and its ambient
centralizer lies in H, the internal and ambient joins agree under the
subtype map, yielding a canonical group equivalence.

The centralizer normalizes Q, while the normalizer of Q normalizes its
centralizer. The join and subgroup restriction formulas prove the normal
tower. The canonical maps and equivalences expose their ambient values for
later group-algebra embeddings. No finite-group hypothesis is needed.

Ported from the group-theoretic infrastructure of revision c3503435,
public/lean-eval/glauberman_zStar,
Submission/ZStar/NormalizerBrauerPair.lean. It is generic subgroup algebra
used in the normalizer layer of the Brauer-pair argument.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerPair
open Subgroup
open scoped Pointwise
universe u
/-- The subgroup denoted `Q C_G(Q)` in the block-theory literature. -/
@[expose] def qcCentralizer
    {G : Type u} [Group G] (Q : Subgroup G) : Subgroup G :=
  Q ⊔ Subgroup.centralizer (Q : Set G)

/-- Under the admissibility condition `C_G(Q) ≤ H`, the centralizer of
`Q` computed inside `H` maps onto its ambient centralizer. -/
theorem centralizer_map_subtype_eq_of_ambientCentralizer_le
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    (Subgroup.centralizer (Q : Set H)).map H.subtype =
      Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨xH, hxH, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro qG hqG
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hqG
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hxH q hq)
  · intro x hx
    let xH : H := ⟨x, hC hx⟩
    have hxH : xH ∈ Subgroup.centralizer (Q : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hqG : (q : G) ∈ Q.map H.subtype :=
        Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hx (q : G) hqG
    exact Subgroup.mem_map.mpr ⟨xH, hxH, rfl⟩

/-- Consequently the internal subgroup `Q C_H(Q)` maps exactly onto the
ambient subgroup `Q C_G(Q)`. -/
theorem qcCentralizer_map_subtype_eq_of_ambientCentralizer_le
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    (qcCentralizer Q).map H.subtype =
      qcCentralizer (Q.map H.subtype : Subgroup G) := by
  rw [qcCentralizer, qcCentralizer, Subgroup.map_sup,
    centralizer_map_subtype_eq_of_ambientCentralizer_le H Q hC]

/-- The canonical equivalence `Q C_H(Q) ≃ Q C_G(Q)` available for an
admissible subgroup. -/
@[expose] noncomputable def qcCentralizerMapEquiv
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    qcCentralizer Q ≃* qcCentralizer (Q.map H.subtype : Subgroup G) :=
  (Subgroup.equivMapOfInjective (qcCentralizer Q) H.subtype
      H.subtype_injective).trans
    (MulEquiv.subgroupCongr
      (qcCentralizer_map_subtype_eq_of_ambientCentralizer_le H Q hC))

@[simp] theorem qcCentralizerMapEquiv_apply_coe
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H)
    (x : qcCentralizer Q) :
    ((qcCentralizerMapEquiv H Q hC x :
      qcCentralizer (Q.map H.subtype : Subgroup G)) : G) = (x : G) := rfl

/-- The preceding equivalence carries the canonical copy of `Q` to the
canonical copy of its ambient image. -/
theorem subgroupOf_qcCentralizer_map_qcCentralizerMapEquiv
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    (Q.subgroupOf (qcCentralizer Q)).map
        (qcCentralizerMapEquiv H Q hC).toMonoidHom =
      (Q.map H.subtype).subgroupOf
        (qcCentralizer (Q.map H.subtype : Subgroup G)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    change (p : H) ∈ Q at hp
    change ((qcCentralizerMapEquiv H Q hC p :
      qcCentralizer (Q.map H.subtype : Subgroup G)) : G) ∈
        Q.map H.subtype
    exact Subgroup.mem_map.mpr ⟨(p : H), hp, rfl⟩
  · intro hx
    change (x : G) ∈ Q.map H.subtype at hx
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
    let p : qcCentralizer Q :=
      ⟨q, (le_sup_left : Q ≤
        Q ⊔ Subgroup.centralizer (Q : Set H)) hq⟩
    apply Subgroup.mem_map.mpr
    refine ⟨p, ?_, ?_⟩
    · exact hq
    · apply Subtype.ext
      exact hqx

/-- The canonical inclusion `C_G(Q) → Q C_G(Q)`. -/
@[expose] def centralizerToQcCentralizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.centralizer (Q : Set G) →* qcCentralizer Q :=
  Subgroup.inclusion le_sup_right

theorem centralizerToQcCentralizer_injective
    {G : Type u} [Group G] (Q : Subgroup G) :
    Function.Injective (centralizerToQcCentralizer Q) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : qcCentralizer Q => (z : G)) hxy

/-- `Q C_G(Q)` is contained in `N_G(Q)`. -/
theorem qcCentralizer_le_normalizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    qcCentralizer Q ≤ Subgroup.normalizer Q := by
  exact sup_le Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer (Q : Set G))

/-- The subgroup `Q C_G(Q)` is normal in `N_G(Q)`.  This is the subgroup
tower behind the intermediate block in the First Main/Nagao argument. -/
theorem qcCentralizer_subgroupOf_normalizer_isNormal
    {G : Type u} [Group G] (Q : Subgroup G) :
    (qcCentralizer Q).subgroupOf (Subgroup.normalizer Q) |>.Normal := by
  have hQ : Q ≤ Subgroup.normalizer Q := Subgroup.le_normalizer
  have hC : Subgroup.centralizer (Q : Set G) ≤
      Subgroup.normalizer Q :=
    Subgroup.centralizer_le_normalizer (Q : Set G)
  rw [qcCentralizer, Subgroup.subgroupOf_sup hQ hC]
  infer_instance

/-- The `Q` factor is normal in `Q C_G(Q)`. -/
theorem subgroupOf_qcCentralizer_isNormal
    {G : Type u} [Group G] (Q : Subgroup G) :
    (Q.subgroupOf (qcCentralizer Q)).Normal := by
  rw [qcCentralizer, sup_comm]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (Q : Set G))

/-- The centralizer factor is also normal in `Q C_G(Q)`. -/
theorem centralizer_subgroupOf_qcCentralizer_isNormal
    {G : Type u} [Group G] (Q : Subgroup G) :
    ((Subgroup.centralizer (Q : Set G)).subgroupOf
      (qcCentralizer Q)).Normal := by
  have hQ : Q ≤ Subgroup.normalizer
      (Subgroup.centralizer (Q : Set G)) := by
    let :
        ((Subgroup.centralizer (Q : Set G)).subgroupOf
          (Subgroup.normalizer (Q : Set G))).Normal := inferInstance
    have hNle : Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer
          ((Subgroup.centralizer (Q : Set G)) : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf
        (H := Subgroup.centralizer (Q : Set G))
        (K := Subgroup.normalizer (Q : Set G))
        (Subgroup.centralizer_le_normalizer (Q : Set G))
    exact Subgroup.le_normalizer.trans hNle
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hQ

/-- If `Q` is a subgroup of `H` and `C_G(Q) ≤ H`, then the whole subgroup
`Q C_G(Q)` lies in `H`.  Here `Q` is presented as a subgroup of `H`, as in
the admissible witness produced by `ThirdMainReduction`. -/
theorem qcCentralizer_le_of_ambientCentralizer_le
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    qcCentralizer (Q.map H.subtype : Subgroup G) ≤ H := by
  exact sup_le (Subgroup.map_subtype_le Q) hC

/-- The exact subgroup tower used before applying First Main: an admissible
`Q C_G(Q)` lies simultaneously in `H` and in `N_G(Q)`. -/
theorem qcCentralizer_le_inf_of_ambientCentralizer_le
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    qcCentralizer (Q.map H.subtype : Subgroup G) ≤
      H ⊓ Subgroup.normalizer (Q.map H.subtype : Subgroup G) := by
  exact le_inf
    (qcCentralizer_le_of_ambientCentralizer_le H Q hC)
    (qcCentralizer_le_normalizer (Q.map H.subtype : Subgroup G))

end ModularBlock.NormalizerBrauerPair

