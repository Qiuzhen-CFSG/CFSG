module
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.ElementaryAbelian.Injective

/-!
# Bounds on elementary subgroups normal in a Sylow subgroup

Intersect the actor with a normal subgroup, restrict the supplied Sylow,
and multiply its known bound by the normal subgroup's index. The companion
transport lemmas preserve the supplied Sylow and actor under an isomorphism
or a surjection that is injective on the actor.

Source application: Aschbacher–Smith G.11.1(4), G.11.7; standard Sylow
restriction and the subgroup index formula.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormalSylowElementary

theorem card_le_mul_index
    {D : Type*} [Group D] [Finite D] (N : Subgroup D) [N.Normal]
    (b : ℕ)
    (hb : ∀ (Q : Sylow 2 N) (E : Subgroup Q), E.Normal →
      IsElementaryAbelian 2 E → Nat.card E ≤ b)
    (P : Sylow 2 D) (E : Subgroup D) (hEP : E ≤ P)
    (hn : (E.subgroupOf (P : Subgroup D)).Normal)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ b * N.index := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let E₀ := E.subgroupOf N
  have hEQ : E₀ ≤ (Q : Subgroup N) := by
    rw [hQ]
    exact fun x hx => hEP hx
  let f : Q →* P := {
    toFun := fun x => ⟨(x : N), by
      exact show (x : N) ∈ (P : Subgroup D).subgroupOf N from hQ ▸ x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hnormal : (E₀.subgroupOf (Q : Subgroup N)).Normal := by
    change ((E.subgroupOf (P : Subgroup D)).comap f).Normal
    exact hn.comap f
  let : IsElementaryAbelian 2 E₀ :=
    IsElementaryAbelian.comap_of_injective N.subtype N.subtype_injective E
  let : IsElementaryAbelian 2 (E₀.subgroupOf (Q : Subgroup N)) :=
    IsElementaryAbelian.subgroupOf hEQ
  have hsmall : Nat.card E₀ ≤ b := by
    have h := hb Q (E₀.subgroupOf (Q : Subgroup N)) hnormal inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv] at h
  have hindex : N.relIndex E ≤ N.index :=
    Nat.le_of_dvd (show 0 < N.index from Nat.card_pos) (N.relIndex_dvd_index_of_normal E)
  have hcard := (N.subgroupOf E).card_mul_index
  have heq : Nat.card (N.subgroupOf E) = Nat.card E₀ := by
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [heq] at hcard
  change Nat.card E₀ * N.relIndex E = Nat.card E at hcard
  rw [← hcard]
  exact Nat.mul_le_mul hsmall hindex

theorem bound_equiv
    {D C : Type*} [Group D] [Finite D] [Group C] [Finite C]
    (a : D ≃* C) (b : ℕ)
    (hb : ∀ (Q : Sylow 2 C) (E : Subgroup Q), E.Normal →
      IsElementaryAbelian 2 E → Nat.card E ≤ b)
    (P : Sylow 2 D) (E : Subgroup P) (hn : E.Normal)
    (he : IsElementaryAbelian 2 E) : Nat.card E ≤ b := by
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let f : P ≃* Q := (P : Subgroup D).equivMapOfInjective a.toMonoidHom a.injective
  let R := E.map f.toMonoidHom
  let : R.Normal := hn.map f.toMonoidHom f.surjective
  let : IsElementaryAbelian 2 E := he
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map _
  have h := hb Q R inferInstance inferInstance
  rwa [card_map_of_injective f.injective] at h

theorem bound_surjective
    {D C : Type*} [Group D] [Finite D] [Group C] [Finite C]
    (q : D →* C) (hq : Function.Surjective q) (b : ℕ)
    (hb : ∀ (Q : Sylow 2 C) (R : Subgroup Q), R.Normal →
      IsElementaryAbelian 2 R → Nat.card R ≤ b)
    (P : Sylow 2 D) (E : Subgroup D) (hEP : E ≤ P)
    (hn : (E.subgroupOf (P : Subgroup D)).Normal)
    [IsElementaryAbelian 2 E]
    (hi : Function.Injective (q.comp E.subtype)) : Nat.card E ≤ b := by
  let Q := P.mapSurjective hq
  let R := E.map q
  have hRQ : R ≤ (Q : Subgroup C) := map_mono hEP
  have hnR : (R.subgroupOf (Q : Subgroup C)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hRQ).mpr
    rintro _ ⟨x,hx,rfl⟩
    exact le_normalizer_map q (mem_map_of_mem q
      ((normal_subgroupOf_iff_le_normalizer hEP).mp hn hx))
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map q
  have h := hb Q (R.subgroupOf (Q : Subgroup C)) hnR
    (IsElementaryAbelian.subgroupOf hRQ)
  rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv] at h
  have hEq : Nat.card R = Nat.card E := Nat.card_congr
    (MulEquiv.ofBijective (q.subgroupMap E) ⟨by
      intro x y hxy
      exact hi (congrArg Subtype.val hxy), q.subgroupMap_surjective E⟩).symm.toEquiv
  rwa [hEq] at h

end Theory.GroupTheory.NormalSylowElementary
