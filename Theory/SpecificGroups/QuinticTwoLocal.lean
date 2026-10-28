module
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PerfectCentralCoverActions

/-!
# Quintic automorphisms of small two-local subgroups

Embed each small alternating group in A₈ ≃ GL₄(2). The normalizer of
any nontrivial two-subgroup has order prime to five. Since the outer
automorphism groups are two-groups, an order-five automorphism cannot
preserve such a subgroup. The same argument applies to SL₄(2).

Source: Aschbacher--Smith 14.6.15, p.1035, small-model comparison.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.QuinticTwoLocal
variable {C : Type*} [Group C] [Finite C]

omit [Finite C] in
/-- The local obstruction uses an actual embedding and actual outer group. -/
theorem no_order_five_of_embedding
    (f : C →* BinaryLinear.OuterCyclic.LinearGroup 4) (hf : Function.Injective f)
    (ho : IsPGroup 2 (MulAut.Outer C))
    (Q : Subgroup C) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (a : MulAut C) (ha : orderOf a = 5) (hfix : Q.map a.toMonoidHom = Q) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : a ∈ MulAut.innerSubgroup C := by
    by_contra hn
    have he := MulAut.outer_order_eq_prime_of_prime_order_not_inner a ha hn
    have hc := ho.orderOf_coprime (by decide : Nat.Coprime 2 5)
      (QuotientGroup.mk' (MulAut.innerSubgroup C) a)
    rw [he] at hc
    norm_num at hc
  obtain ⟨x,hx⟩ := hi
  have hxn : x ∈ normalizer (Q : Set C) := mem_normalizer_iff_map_conj_eq.mpr (hx ▸ hfix)
  have hn : f x ∈ normalizer (Q.map f : Set (BinaryLinear.OuterCyclic.LinearGroup 4)) :=
    Q.le_normalizer_map f (mem_map_of_mem f hxn)
  have hd : 5 ∣ Nat.card (normalizer (Q.map f : Set (BinaryLinear.OuterCyclic.LinearGroup 4))) := by
    have h1 : 5 ∣ orderOf x := ha ▸ hx ▸ orderOf_map_dvd MulAut.conj x
    have h2 := orderOf_dvd_natCard (⟨f x,hn⟩ : normalizer (Q.map f : Set (BinaryLinear.OuterCyclic.LinearGroup 4)))
    rw [Subgroup.orderOf_mk,orderOf_injective f hf] at h2
    exact h1.trans h2
  exact BinaryLinear.FourTwoLocalFive.five_not_dvd_normalizer (Q.map f) (hQ.map f)
    (fun h => hne ((Q.map_eq_bot_iff_of_injective hf).mp h)) hd

private noncomputable def alternatingInEight {n : ℕ} (hn : n ≤ 8) :
    alternatingGroup (Fin n) →* alternatingGroup (Fin 8) := by
  classical
  let j := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)
  exact (j.comp (alternatingGroup (Fin n)).subtype).codRestrict _ (by
    intro a
    change Equiv.Perm.sign (j a.val) = 1
    simp only [j,Equiv.Perm.viaEmbeddingHom,Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.mp a.property)

private theorem alternatingInEight_injective {n : ℕ} (hn : n ≤ 8) :
    Function.Injective (alternatingInEight hn) := by
  intro a b hab
  exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn)
    (congrArg Subtype.val hab))

private theorem alternating_outer_two {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases h6 : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin n) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [←A.index_eq_card,alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) h6).surjective a
  exact ⟨QuotientGroup.mk' A s,rfl⟩

omit [Finite C] in
/-- This excludes order-five actors preserving any nontrivial two-subgroup
in the four small alternating models, without a choice of Sylow marking. -/
theorem no_order_five_alternating {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : C ≃* alternatingGroup (Fin n)) (Q : Subgroup C)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) (a : MulAut C)
    (ha : orderOf a = 5) (hfix : Q.map a.toMonoidHom = Q) : False := by
  let b := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  let i := alternatingInEight (show n ≤ 8 by omega)
  exact no_order_five_of_embedding (b.toMonoidHom.comp (i.comp e.toMonoidHom))
    (b.injective.comp ((alternatingInEight_injective _).comp e.injective))
    ((alternating_outer_two hn).of_injective (MulAut.outerCongr e).toMonoidHom
      (MulAut.outerCongr e).injective) Q hQ hne a ha hfix

omit [Finite C] in
/-- The binary linear-four form uses the actual special-linear carrier. -/
theorem no_order_five_linear_four (e : C ≃* SL(4,ZMod 2))
    (Q : Subgroup C) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (a : MulAut C) (ha : orderOf a = 5) (hfix : Q.map a.toMonoidHom = Q) : False := by
  let b := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 4)
  exact no_order_five_of_embedding b.toMonoidHom b.injective
    ((Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two (Or.inl rfl)).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective)
    Q hQ hne a ha hfix
/-- Odd central covers retain the same obstruction: the two-subgroup
survives and perfectness makes the induced automorphism faithful. -/
theorem no_order_five_central_alternating [Group.IsPerfect C]
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : (C ⧸ center C) ≃* alternatingGroup (Fin n))
    (hz : Nat.Coprime 2 (Nat.card (center C)))
    (Q : Subgroup C) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (a : MulAut C) (ha : orderOf a = 5) (hfix : Q.map a.toMonoidHom = Q) : False := by
  let q := QuotientGroup.mk' (center C)
  let c : PerfectCentralCovering.Cover C (C ⧸ center C) :=
    ⟨q,QuotientGroup.mk'_surjective _,inferInstance,by simp [q]⟩
  have he : orderOf a = orderOf (quotientAut (center C) a) :=
    c.equivariantActions_order (MonoidHom.id (MulAut C)) (quotientAut (center C))
      (fun b x => (quotientAut_apply_mk (center C) b x).symm) a
  have hnon : Q.map q ≠ ⊥ := by
    intro hh
    have hle : Q ≤ center C := by
      simpa only [q,QuotientGroup.ker_mk'] using (Q.map_eq_bot_iff).mp hh
    obtain ⟨k,hk⟩ := hQ.exists_card_eq
    have hd : Disjoint Q (center C) := disjoint_of_coprime_natCard (by
      rw [hk]; exact hz.pow_left k)
    exact hne ((inf_eq_left.mpr hle).symm.trans hd.eq_bot)
  apply no_order_five_alternating hn e (Q.map q) (hQ.map q) hnon
    (quotientAut (center C) a) (he.symm.trans ha)
  rw [map_map]
  have heq : (quotientAut (center C) a).toMonoidHom.comp q = q.comp a.toMonoidHom := by
    ext x
    exact quotientAut_apply_mk (center C) a x
  rw [heq,←map_map,hfix]

end Theory.SpecificGroups.QuinticTwoLocal
