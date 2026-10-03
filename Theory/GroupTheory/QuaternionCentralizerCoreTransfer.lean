module

public import Theory.GroupTheory.CentralProductElementaryTransfer
public import Theory.GroupTheory.PGroup.CentralProductProjection
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.SpecificGroups.QuaternionCentralSquareEmbedding
public import Theory.PGroupCore
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# Quaternion-core transfer in a binary centralizer product

The centralizer projection of an elementary subgroup is a two-group. Joining
it with the quaternion core gives a two-group with no elementary four, hence
a generalized quaternion group. Every square in the projection is central
in this larger group, because it belongs to the overlap of the commuting
factors.

The central-square embedding puts this projection into the quaternion core,
preserving the overlap with the other factor. The multiplication maps then
have the same kernel, so the elementary subgroup transfers without changing
its cardinality. In particular an elementary eight transfers into the product
with the core. The solvability, odd-core, and rank-two assumptions of the
campaign statement are not needed for this transfer step.

This is the quaternion-core case in the binary centralizer argument associated
with the remark following GLS, Number 2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). The projection, quaternion geometry, and
gluing arguments are intrinsic lemmas in `Theory`.
-/

namespace Subgroup

open Subgroup
open scoped IsMulCommutative

/-- The centralizer projection can be placed in a generalized quaternion
two-group containing the two-core, with all its squares central there. -/
public theorem exists_quaternion_centralizer_projection
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] :
    ∃ R T : Subgroup (centralizer (Q : Set H)),
      pCore 2 (centralizer (Q : Set H)) ≤ R ∧ T ≤ R ∧ IsPGroup 2 R ∧
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (R ≃* QuaternionGroup (2 ^ (n - 2)))) ∧
      B ≤ Q ⊔ T.map (centralizer (Q : Set H)).subtype ∧
      ∀ t : T, ∀ ht : (t : centralizer (Q : Set H)) ∈ R,
        (⟨t, ht⟩ : R) ^ 2 ∈ center R := by
  let C := centralizer (Q : Set H)
  have hcomm : ∀ q : Q, ∀ c : C, Commute (q : H) (c : H) := by
    intro q c
    exact mem_centralizer_iff.mp c.property q q.property
  obtain ⟨T, hT, hBT, hpow⟩ :=
    exists_pSubgroup_projection_of_elementary Q C B hQ hcomm
      (hgen.symm ▸ le_top)
  let K := pCore 2 C
  let R : Subgroup C := T ⊔ K
  have hKR : K ≤ R := le_sup_right
  have hTR : T ≤ R := le_sup_left
  have hR : IsPGroup 2 R := hT.to_sup_of_normal_right pCore_isPGroup
  obtain ⟨eK⟩ := hcore
  have hKcard : Nat.card K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hRcard : 8 ≤ Nat.card R := hKcard ▸ card_le_of_le hKR
  let : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hRfour : ∀ F : Subgroup R, IsElementaryAbelian 2 F → Nat.card F ≠ 4 := by
    intro F hF hcard
    let : IsElementaryAbelian 2 F := hF
    have hh := hfour (F.map R.subtype) (IsElementaryAbelian.map R.subtype)
    rw [card_map_of_injective R.subtype_injective, hcard] at hh
    omega
  obtain hcyc | ⟨n, hn, hnmodel⟩ :=
    hR.isCyclic_or_quaternion_of_no_elementary_four hRfour
  · let : IsCyclic R := hcyc
    let f : QuaternionGroup 2 →* R := (inclusion hKR).comp eK.symm.toMonoidHom
    have hf : Function.Injective f := (inclusion_injective hKR).comp eK.symm.injective
    have hnc : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
    exact (hnc (hf (by simp only [map_mul]; exact mul_comm _ _))).elim
  · refine ⟨R, T, hKR, hTR, hR, ⟨n, hn, hnmodel⟩, hBT, ?_⟩
    intro t ht
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (y : C).property _ (hpow t)).symm

/-- An elementary subgroup of a binary centralizer product has an elementary
copy of the same order in the product with the quaternion two-core. -/
public theorem exists_elementary_subgroup_quaternion_core_of_card_eq
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] :
    ∃ D : Subgroup H,
      D ≤ Q ⊔ (pCore 2 (centralizer (Q : Set H))).map
        (centralizer (Q : Set H)).subtype ∧
      IsElementaryAbelian 2 D ∧ Nat.card D = Nat.card B := by
  let C := centralizer (Q : Set H)
  let K := pCore 2 C
  obtain ⟨R, T, hKR, hTR, _, ⟨n, hn, ⟨model⟩⟩, hBT, hsq⟩ :=
    exists_quaternion_centralizer_projection Q B hQ hgen hfour hcore
  let K' := K.subgroupOf R
  let T' := T.subgroupOf R
  let eK : K' ≃* K := subgroupOfEquivOfLe hKR
  let eT : T' ≃* T := subgroupOfEquivOfLe hTR
  have hK' : Nonempty (K' ≃* QuaternionGroup 2) := by
    obtain ⟨kmodel⟩ := hcore
    exact ⟨eK.trans kmodel⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ n - 2 by omega)
    simpa using this
  obtain ⟨g, _, hgc⟩ := QuaternionGroup.exists_embedding_preserving_center
    hm model K' T' hK' (fun t => hsq (eT t) t.val.property)
  let U := T.map C.subtype
  let eU : T ≃* U := T.equivMapOfInjective C.subtype C.subtype_injective
  let f : U →* H := C.subtype.comp (K.subtype.comp
    (eK.toMonoidHom.comp (g.comp (eT.symm.toMonoidHom.comp eU.symm.toMonoidHom))))
  have hf (t : T') : f (eU (eT t)) = ((g t : R) : C) := by
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rfl
  have ht (t : T') : ((eU (eT t) : U) : H) = ((t : R) : C) := rfl
  have hcomm : ∀ q : Q, ∀ c : C, Commute (q : H) (c : H) := by
    intro q c
    exact mem_centralizer_iff.mp c.property q q.property
  have hcentral (q : Q) (r : R) (hr : (q : H) = ((r : C) : H)) :
      r ∈ center R := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change ((y : C) : H) * ((r : C) : H) = ((r : C) : H) * ((y : C) : H)
    rw [← hr]
    exact (hcomm q (y : C)).eq.symm
  refine exists_elementary_subgroup_of_central_product_replacement Q U
    (K.map C.subtype) B ?_ f ?_ ?_ ?_ hBT
  · intro q u
    obtain ⟨t, rfl⟩ := eU.surjective u
    exact hcomm q t
  · rintro x ⟨u, rfl⟩
    exact ⟨_, (eK (g (eT.symm (eU.symm u)))).property, rfl⟩
  · intro q u
    exact hcomm q (eK (g (eT.symm (eU.symm u))))
  · intro q u
    obtain ⟨t, rfl⟩ := (eT.trans eU).surjective u
    change (q : H) = ((eU (eT t) : U) : H) ↔ (q : H) = f (eU (eT t))
    rw [ht, hf]
    constructor
    · intro h
      have hc := hgc t (t : R) (hcentral q t h)
      have heq := hc.mp rfl
      exact h.trans (congrArg (fun r : R => ((r : C) : H)) heq).symm
    · intro h
      have hc := hgc t (g t : R) (hcentral q (g t) h)
      have heq := hc.mpr rfl
      exact h.trans (congrArg (fun r : R => ((r : C) : H)) heq).symm

/-- Quaternion-core transfer for an elementary subgroup of order at least eight. -/
public theorem exists_elementary_eight_quaternion_core
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hfour : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hcore : Nonempty (pCore 2 (centralizer (Q : Set H)) ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 B] (hB : 8 ≤ Nat.card B) :
    ∃ D : Subgroup H,
      D ≤ Q ⊔ (pCore 2 (centralizer (Q : Set H))).map
        (centralizer (Q : Set H)).subtype ∧
      IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
  obtain ⟨D, hD, he, hc⟩ :=
    exists_elementary_subgroup_quaternion_core_of_card_eq Q B hQ hgen hfour hcore
  exact ⟨D, hD, he, hc ▸ hB⟩

end Subgroup
