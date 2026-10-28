module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.Algebra
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction
public import Theory.GroupAction.NormalComplement
public import Theory.GroupTheory.ConjugacyClassSize
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The two Section 17 incidence counts

Count the incidences between the actual conjugacy class of u and ordered
pairs of distinct cosets. Conjugation makes actor fibers uniform; double
transitivity makes point-pair fibers uniform. For fixed pairs, cyclic Sylow
two-subgroups identify the base fiber with the conjugacy class inside the
literal two-point stabilizer. The moved-point count retains its actual
swapping fiber until the odd-complement argument identifies that fiber.

Source: GLS4, Chapter 2, proof of Lemma 17.1, (17E) and (17F).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1

private theorem card_relation {A B : Type*} [Finite A] [Finite B]
    (R : A → B → Prop) (m : ℕ) (hm : ∀ a, Nat.card {b // R a b} = m) :
    Nat.card {p : A × B // R p.1 p.2} = Nat.card A * m := by
  classical
  let _ := Fintype.ofFinite A
  let e : {p : A × B // R p.1 p.2} ≃ Σ a : A, {b // R a b} := {
    toFun := fun p => ⟨p.val.1, p.val.2, p.property⟩
    invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp [hm, Nat.card_eq_fintype_card]

private theorem card_relation_swap {A B : Type*} (R : A → B → Prop) :
    Nat.card {p : A × B // R p.1 p.2} =
      Nat.card {p : B × A // R p.2 p.1} := by
  exact Nat.card_congr {
    toFun := fun p => ⟨(p.val.2, p.val.1), p.property⟩
    invFun := fun p => ⟨(p.val.2, p.val.1), p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem card_not {A : Type*} [Finite A] (p : A → Prop) :
    Nat.card {a // ¬ p a} = Nat.card A - Nat.card {a // p a} := by
  classical
  let _ := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private theorem card_distinct_pairs (X : Type*) [Finite X] :
    Nat.card {p : X × X // p.1 ≠ p.2} = Nat.card X * (Nat.card X - 1) := by
  apply card_relation
  intro a
  rw [card_not]
  congr 1
  exact Nat.card_eq_one_iff_exists.mpr ⟨⟨a, rfl⟩, fun b => Subtype.ext b.property.symm⟩

section Action
variable {G X : Type*} [Group G] [MulAction G X]

private theorem conj_fixed_iff (g v : G) (x : X) :
    (MulAut.conj g v) • (g • x) = g • x ↔ v • x = x := by
  simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, smul_left_cancel_iff]

private theorem fixed_card_conj {u v : G} (hc : IsConj u v) :
    Nat.card {x : X // v • x = x} = Nat.card {x : X // u • x = x} := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  exact (Nat.card_congr ((MulAction.toPerm g).subtypeEquiv
    (fun x => (conj_fixed_iff g u x).symm))).symm

private theorem fixed_pair_actor_card [Finite X] (v : G) :
    Nat.card {p : {p : X × X // p.1 ≠ p.2} //
      v • p.val.1 = p.val.1 ∧ v • p.val.2 = p.val.2} =
    Nat.card {x : X // v • x = x} * (Nat.card {x : X // v • x = x} - 1) := by
  let F := {x : X // v • x = x}
  let e : {p : {p : X × X // p.1 ≠ p.2} //
      v • p.val.1 = p.val.1 ∧ v • p.val.2 = p.val.2} ≃
      {p : F × F // p.1 ≠ p.2} := {
    toFun := fun p => ⟨(⟨p.val.val.1, p.property.1⟩, ⟨p.val.val.2, p.property.2⟩),
      fun he => p.val.property (congrArg Subtype.val he)⟩
    invFun := fun p => ⟨⟨(p.val.1.val, p.val.2.val), fun he => p.property (Subtype.ext he)⟩,
      p.val.1.property, p.val.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_distinct_pairs]

private theorem fixed_pair_class_fiber_card (u g : G) (a b : X) :
    Nat.card {v : {v : G // IsConj u v} //
      v.val • (g • a) = g • a ∧ v.val • (g • b) = g • b} =
    Nat.card {v : {v : G // IsConj u v} //
      v.val • a = a ∧ v.val • b = b} := by
  let e : {v : G // IsConj u v} ≃ {v : G // IsConj u v} :=
    (MulAut.conj g).toEquiv.subtypeEquiv (fun v =>
      ⟨fun hc => hc.trans (isConj_iff.mpr ⟨g, rfl⟩),
       fun hc => hc.trans (isConj_iff.mpr ⟨g, rfl⟩).symm⟩)
  exact (Nat.card_congr (e.subtypeEquiv (fun v =>
    (and_congr (conj_fixed_iff g v.val a) (conj_fixed_iff g v.val b)).symm))).symm

/-- Double counting the fixed ordered pairs in one actual conjugacy class. -/
private theorem fixed_pair_double_count [Finite G] [Finite X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (u : G) {a b : X} (hab : a ≠ b) :
    Nat.card {v : G // IsConj u v} *
      (Nat.card {x : X // u • x = x} * (Nat.card {x : X // u • x = x} - 1)) =
    (Nat.card X * (Nat.card X - 1)) *
      Nat.card {v : {v : G // IsConj u v} // v.val • a = a ∧ v.val • b = b} := by
  let C := {v : G // IsConj u v}
  let P := {p : X × X // p.1 ≠ p.2}
  let R (v : C) (p : P) := v.val • p.val.1 = p.val.1 ∧ v.val • p.val.2 = p.val.2
  have hleft := card_relation R _ (fun v => by
    change Nat.card {p : P // R v p} = _
    rw [show Nat.card {p : P // R v p} = _ from fixed_pair_actor_card v.val,
      fixed_card_conj v.property])
  have hright := card_relation (fun p v => R v p)
    (Nat.card {v : C // R v ⟨(a,b), hab⟩}) (fun p => by
      obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab p.property
      change Nat.card {v : C // v.val • p.val.1 = p.val.1 ∧
        v.val • p.val.2 = p.val.2} = _
      rw [← hga, ← hgb]
      exact fixed_pair_class_fiber_card u g a b)
  rw [card_distinct_pairs] at hright
  exact hleft.symm.trans ((card_relation_swap R).trans hright)

private theorem moved_pair_fiber_card [Finite X] (v : G) :
    Nat.card {p : {p : X × X // p.1 ≠ p.2} // v • p.val.1 = p.val.2} =
      Nat.card X - Nat.card {x : X // v • x = x} := by
  let e : {p : {p : X × X // p.1 ≠ p.2} // v • p.val.1 = p.val.2} ≃
      {x : X // v • x ≠ x} := {
    toFun := fun p => ⟨p.val.val.1, fun he =>
      p.val.property (he.symm.trans p.property)⟩
    invFun := fun x => ⟨⟨(x.val, v • x.val), x.property.symm⟩, rfl⟩
    left_inv := fun p => by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl p.property
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_not]

private theorem moved_pair_class_fiber_card (u g : G) (a b : X) :
    Nat.card {v : {v : G // IsConj u v} // v.val • (g • a) = g • b} =
      Nat.card {v : {v : G // IsConj u v} // v.val • a = b} := by
  let e : {v : G // IsConj u v} ≃ {v : G // IsConj u v} :=
    (MulAut.conj g).toEquiv.subtypeEquiv (fun v =>
      ⟨fun hc => hc.trans (isConj_iff.mpr ⟨g, rfl⟩),
       fun hc => hc.trans (isConj_iff.mpr ⟨g, rfl⟩).symm⟩)
  apply (Nat.card_congr (e.subtypeEquiv ?_)).symm
  intro v
  change v.val • a = b ↔ (MulAut.conj g v.val) • (g • a) = g • b
  simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, smul_left_cancel_iff]

private theorem moved_pair_double_count [Finite G] [Finite X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (u : G) {a b : X} (hab : a ≠ b) :
    Nat.card {v : G // IsConj u v} *
      (Nat.card X - Nat.card {x : X // u • x = x}) =
    (Nat.card X * (Nat.card X - 1)) *
      Nat.card {v : {v : G // IsConj u v} // v.val • a = b} := by
  let C := {v : G // IsConj u v}
  let P := {p : X × X // p.1 ≠ p.2}
  let R (v : C) (p : P) := v.val • p.val.1 = p.val.2
  have hleft := card_relation R _ (fun v => by
    change Nat.card {p : P // R v p} = _
    rw [show Nat.card {p : P // R v p} = _ from moved_pair_fiber_card v.val,
      fixed_card_conj v.property])
  have hright := card_relation (fun p v => R v p)
    (Nat.card {v : C // R v ⟨(a,b), hab⟩}) (fun p => by
      obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab p.property
      change Nat.card {v : C // v.val • p.val.1 = p.val.2} = _
      rw [← hga, ← hgb]
      exact moved_pair_class_fiber_card u g a b)
  rw [card_distinct_pairs] at hright
  exact hleft.symm.trans ((card_relation_swap R).trans hright)

end Action

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem cyclic_sylow_involutions_conjugate
    {D : Type*} [Group D] [Finite D] (hcyc : ∀ S : Sylow 2 D, IsCyclic S)
    {x y : D} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let S : Sylow 2 D := Classical.choice inferInstance
  let : IsCyclic S := hcyc S
  obtain ⟨a, ha⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨b, hb⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy)
  have hao : orderOf a = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    change MulAut.conj g x = (a : D) at hg
    rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq, hx]
  have hbo : orderOf b = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hb
    change MulAut.conj g y = (b : D) at hg
    rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq, hy]
  have hab : a = b := IsCyclic.eq_of_orderOf_eq_two hao hbo
  exact ha.trans (hab ▸ hb.symm)

omit [Finite G] in
private theorem pair_eq_stabilizers (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    residualPairStabilizer M d.t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (d.t • (QuotientGroup.mk 1 : G ⧸ M)) := by
  have he := rightConjugate_stabilizer (QuotientGroup.mk 1 : G ⧸ M) d.t
  rw [(h.involutions d.t d.t_mem).inv_eq_self, MulAction.stabilizer_quotient] at he
  rw [residualPairStabilizer, he, MulAction.stabilizer_quotient]

/-- The base fiber of Ψ is the conjugacy class of u inside the actual D.
Cyclicity is used on Sylow subgroups of D, not on an ambient Sylow subgroup. -/
public theorem fixed_pair_fiber_card (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M)
    (hcyc : ∀ S : Sylow 2 (residualPairStabilizer M d.t), IsCyclic S) :
    Nat.card {v : {v : G // IsConj ((d.u : M) : G) v} //
      v.val • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ∧
      v.val • (d.t • (QuotientGroup.mk 1 : G ⧸ M)) =
        d.t • (QuotientGroup.mk 1 : G ⧸ M)} =
    (centralizer ({((d.u : M) : G)} : Set G)).relIndex
      (residualPairStabilizer M d.t) := by
  let D := residualPairStabilizer M d.t
  let u : D := ⟨((d.u : M) : G), d.u.property⟩
  have hu : orderOf u = 2 := by
    rw [← Subgroup.orderOf_coe u]
    change orderOf ((d.u : M) : G) = 2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, d.u_order]
  have hc (v : D) : IsConj ((d.u : M) : G) (v : G) ↔ IsConj u v := by
    constructor
    · intro hv
      apply cyclic_sylow_involutions_conjugate hcyc hu
      obtain ⟨g, hg⟩ := isConj_iff.mp hv
      change MulAut.conj g ((d.u : M) : G) = (v : G) at hg
      rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq,
        Subgroup.orderOf_coe, Subgroup.orderOf_coe, d.u_order]
    · intro hv
      obtain ⟨g, hg⟩ := isConj_iff.mp hv
      exact isConj_iff.mpr ⟨D.subtype g, congrArg D.subtype hg⟩
  have hmem (v : G) :
      v • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ∧
      v • (d.t • (QuotientGroup.mk 1 : G ⧸ M)) =
        d.t • (QuotientGroup.mk 1 : G ⧸ M) ↔ v ∈ D := by
    rw [show D = _ from pair_eq_stabilizers h d]
    rfl
  let e : {v : {v : G // IsConj ((d.u : M) : G) v} //
      v.val • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ∧
      v.val • (d.t • (QuotientGroup.mk 1 : G ⧸ M)) =
        d.t • (QuotientGroup.mk 1 : G ⧸ M)} ≃ {v : D // IsConj u v} := {
    toFun := fun v => ⟨⟨v.val.val, (hmem _).mp v.property⟩, (hc _).mp v.val.property⟩
    invFun := fun v => ⟨⟨v.val.val, (hc _).mpr v.property⟩, (hmem _).mpr v.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have he : centralizer ({u} : Set D) =
      (centralizer ({((d.u : M) : G)} : Set G)).subgroupOf D := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf]
    exact Subtype.ext_iff
  change Nat.card (ConjClasses.mk u).carrier = _
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer, he]
  rfl

/-- The fixed-pair incidence identity (17F), before substituting the
model-specific fixed-point degree. All fibers are counted, not assumed. -/
public theorem fixed_pair_count (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    let f := Nat.card {gamma : G ⧸ M // ((d.u : M) : G) • gamma = gamma}
    Nat.card {v : G // IsConj ((d.u : M) : G) v} * (f * (f - 1)) =
      (Nat.card (G ⧸ M) * (Nat.card (G ⧸ M) - 1)) *
        (centralizer ({((d.u : M) : G)} : Set G)).relIndex
          (residualPairStabilizer M d.t) := by
  have hc := fixed_pair_double_count ha.two_transitive ((d.u : M) : G)
    (twisted_involution_swaps h d).2.2
  rw [fixed_pair_fiber_card h d
    (hlocal _ (residualPairStabilizer_localClosure_eq_bot h d.t_not_mem)).2] at hc
  exact hc

/-- The moved-point incidence identity for Δ in Lemma 17.1. The right-hand
fiber is literally the set of conjugates carrying α to β. -/
public theorem moved_pair_count (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M) :
    let f := Nat.card {gamma : G ⧸ M // ((d.u : M) : G) • gamma = gamma}
    Nat.card {v : G // IsConj ((d.u : M) : G) v} * (Nat.card (G ⧸ M) - f) =
      (Nat.card (G ⧸ M) * (Nat.card (G ⧸ M) - 1)) *
        Nat.card {v : {v : G // IsConj ((d.u : M) : G) v} //
          v.val • (QuotientGroup.mk 1 : G ⧸ M) =
            d.t • (QuotientGroup.mk 1 : G ⧸ M)} :=
  moved_pair_double_count ha.two_transitive ((d.u : M) : G)
    (twisted_involution_swaps h d).2.2

end BenderSuzuki.ZD.Section17
