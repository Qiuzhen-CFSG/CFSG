module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.Centralizer
public import Theory.GroupAction.ElementaryEightInvolutionCentralizer

/-!
# The local action of an outside involution

For an `IntersectionData` witness, an involution in the normalizer of the
elementary eight acts as a nontrivial involution on that eight.  Its fixed
subgroup has order four.  The centralizer of the induced automorphism is a
two-group, and the normalizer action then transfers this fact to the
centralizer inside `G`.

This is the local calculation in Aschbacher's Lemma 2.8(1), used by the
saturated normalizer argument.
-/

open Subgroup

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

variable {G : Type*} [Group G] [Finite G] {z g : G}

omit [Finite G] in
private theorem outside_action_order (d : IntersectionData z g)
    {j : G} (hj : j ∈ normalizer (coreIntersection z g : Set G))
    (hj2 : orderOf j = 2) (hjE : j ∉ coreIntersection z g) :
    orderOf ((coreIntersection z g).normalizerMonoidHom ⟨j, hj⟩) = 2 := by
  let E := coreIntersection z g
  let jN : normalizer (E : Set G) := ⟨j, hj⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have he : jN ^ 2 = 1 := Subtype.ext (hj2 ▸ pow_orderOf_eq_one j)
    rw [he, map_one]
  · intro he
    have hk : jN ∈ E.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker, d.self_centralizing] at hk
    exact hjE hk

/-- The fixed subgroup of an outside involution has order four. -/
public theorem centralizerIntersection_card_four_of_outside_involution
    (d : IntersectionData z g)
    {j : G} (hj : j ∈ normalizer (coreIntersection z g : Set G))
    (hj2 : orderOf j = 2) (hjE : j ∉ coreIntersection z g) :
    Nat.card (centralizerIntersection z g j) = 4 := by
  let E := coreIntersection z g
  let : IsElementaryAbelian 2 E := d.elementary
  let a := E.normalizerMonoidHom ⟨j, hj⟩
  have ha : orderOf a = 2 := outside_action_order d hj hj2 hjE
  let A := zpowers a
  let x : A := ⟨a, mem_zpowers a⟩
  have hx : x ≠ 1 ∧ x ^ 2 = 1 := by
    constructor
    · intro he
      have he' : a = 1 := congrArg Subtype.val he
      simp [he'] at ha
    · exact Subtype.ext (ha ▸ pow_orderOf_eq_one a)
  have hA : Nat.card A = 2 := (Nat.card_zpowers a).trans ha
  have hmove : ∃ e : E, x • e ≠ e := by
    by_contra! hh
    apply hx.1
    apply Subtype.ext
    exact MulEquiv.ext hh
  have hc := fixed_subgroup_card_four_of_nontrivial_involution_on_eight
    x hx hA d.card hmove
  let F := FixedPoints.subgroup A E
  have hfix (e : E) : e ∈ F ↔ (e : G) ∈ Centralizer j := by
    constructor
    · intro he
      have he' := congrArg Subtype.val (he x)
      change j * (e : G) * j⁻¹ = (e : G) at he'
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro he
      have hae : a e = e := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp he).symm
      have hle : A ≤ MulAction.stabilizer (MulAut E) e := zpowers_le.mpr hae
      exact fun b => hle b.property
  let e : F ≃ centralizerIntersection z g j :=
    { toFun := fun v => ⟨⟨v.val.val, (hfix v.val).mp v.property⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, (hfix _).mpr v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).symm.trans hc

/-- The normalizer part centralizing an outside involution is a two-group. -/
public theorem centralizerIntersection_isPGroup_of_outside_involution
    (d : IntersectionData z g)
    {j : G} (hj : j ∈ normalizer (coreIntersection z g : Set G))
    (hj2 : orderOf j = 2) (hjE : j ∉ coreIntersection z g) :
    IsPGroup 2 ((normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j)) := by
  let E := coreIntersection z g
  let M := normalizer (E : Set G)
  let : IsElementaryAbelian 2 E := d.elementary
  let f := E.normalizerMonoidHom
  let jN : M := ⟨j, hj⟩
  let a := f jN
  have ha : orderOf a = 2 := outside_action_order d hj hj2 hjE
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker, d.self_centralizing]
    exact (IsElementaryAbelian.isPGroup 2 E).comap_subtype
  let P := (centralizer ({a} : Set (MulAut E))).comap f
  have hP : IsPGroup 2 P :=
    (isPGroup_centralizer_of_involution_on_elementary_eight d.card a ha).comap_of_ker_isPGroup f hk
  let i : M.subgroupOf (Centralizer j) →* P :=
    { toFun := fun v => ⟨⟨v.val.val, v.property⟩, by
        change f ⟨v.val.val, v.property⟩ ∈ centralizer ({f jN} : Set (MulAut E))
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp v.val.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply hP.of_injective i
  intro v w he
  exact Subtype.ext (Subtype.ext (congrArg (fun v : P => v.val.val) he))

/-- The two local-action facts needed by the saturated normalizer theorem. -/
public theorem centralizerIntersection_local_action
    (d : IntersectionData z g)
    {j : G} (hj : j ∈ normalizer (coreIntersection z g : Set G))
    (hj2 : orderOf j = 2) (hjE : j ∉ coreIntersection z g) :
    Nat.card (centralizerIntersection z g j) = 4 ∧
      IsPGroup 2 ((normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j)) :=
  ⟨centralizerIntersection_card_four_of_outside_involution d hj hj2 hjE,
    centralizerIntersection_isPGroup_of_outside_involution d hj hj2 hjE⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
