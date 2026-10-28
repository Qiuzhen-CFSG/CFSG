module
public import Theory.GroupTheory.ConjugacyCardinalityBound
public import Theory.Mathieu.M12.Properties.InvolutionFixedOrders.InnerData
public import Theory.Mathieu.M12.Properties.InvolutionFixedOrders.OuterData
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OuterInvolutions
public import Theory.Mathieu.M12.Properties.InvolutionFusion
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutory M₁₂ fixed-subgroup order separation

The two certified conjugacy families bound the marked inner 2A centralizer
and the outer involution centralizer in the full automorphism carrier by 297.
The other inner centralizer has the proved order 192. Full inner and outer
involution fusion applies those bounds to every abstract automorphism of
order two. In the outer case the original M₁₂ fixed subgroup embeds in the
centralizer in the faithful degree-24 carrier; the embedding and its action
are the existing marked automorphism identification.

Thus neither 360 nor 2520 divides an involutory fixed-subgroup order. These
are the literal numerical obstructions needed in Aschbacher–Smith E.6.23
and E.6.18. No unproved structural row of 16.1.5(4) is assumed, and the
finite certificates assert distinctness rather than class exhaustion.
-/

open Subgroup
namespace Sporadic.Mathieu.M12FixedOrders

private theorem inner_representative :
    (m12Involution2A : Equiv.Perm (Fin 12)) = Inner.representative := by
  rw [M12Centralizer2A.representative_coe]
  have h0 : Inner.gen0 = m12GeneratorA := congrFun Inner.generators_eq 0
  have h1 : Inner.gen1 = m12GeneratorB := congrFun Inner.generators_eq 1
  simp only [Inner.representative, h0, h1]

private theorem inner_evaluate_mem (w : List (Fin 3)) : Inner.evaluate w ∈ M12 := by
  have hg (i : Fin 3) : Inner.generators i ∈ M12 := by
    rw [Inner.generators_eq]
    fin_cases i
    · exact m12GeneratorA_mem
    · exact m12GeneratorB_mem
    · exact M12.inv_mem m12GeneratorB_mem
  induction w with
  | nil => exact M12.one_mem
  | cons i w ih => exact M12.mul_mem (hg i) ih

attribute [local irreducible] Inner.words Outer.words Inner.evaluate Outer.evaluate

public theorem inner_centralizer_bound :
    Nat.card (centralizer ({m12Involution2A} : Set M12)) ≤ 297 := by
  let g (i : Fin 320) : M12 := ⟨Inner.evaluate Inner.words[i.val]!, inner_evaluate_mem _⟩
  let f (i : Fin 320) : M12 := MulAut.conj (g i) m12Involution2A
  have he (i : Fin 320) : (f i).val = Inner.conjugate i := by
    change Inner.evaluate _ * (m12Involution2A : Equiv.Perm (Fin 12)) *
      (Inner.evaluate _)⁻¹ = _
    rw [inner_representative]
    rfl
  have hi : Function.Injective f := fun i j h => Inner.conjugate_injective (by
    rw [← he i, ← he j, h])
  have hc := Theory.GroupTheory.card_mul_le_of_injective_conjugates m12Involution2A f hi
    (fun i => isConj_iff.mpr ⟨g i, rfl⟩)
  rw [m12_order] at hc
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right
    (hc.trans_lt (by decide : 95040 < 298 * 320)))

open M12ExceptionalExtension
private theorem outer_representative : generatorA = Outer.representative :=
  (congrFun Outer.generators_eq 0).symm

private theorem outer_evaluate_mem (w : List (Fin 3)) : Outer.evaluate w ∈ group := by
  have ha : generatorA ∈ group := subset_closure (by simp)
  have hb : generatorB ∈ group := subset_closure (by simp)
  have hg (i : Fin 3) : Outer.generators i ∈ group := by
    rw [Outer.generators_eq]
    fin_cases i
    · exact ha
    · exact hb
    · exact group.inv_mem hb
  induction w with
  | nil => simpa only [Outer.evaluate] using group.one_mem
  | cons i w ih => simpa only [Outer.evaluate] using group.mul_mem (hg i) ih

public theorem outer_centralizer_bound :
    Nat.card (centralizer ({OuterInvolutions.seed} : Set Carrier)) ≤ 297 := by
  let g (i : Fin 640) : Carrier := ⟨Outer.evaluate Outer.words[i.val]!, outer_evaluate_mem _⟩
  let f (i : Fin 640) : Carrier := MulAut.conj (g i) OuterInvolutions.seed
  have he (i : Fin 640) : (f i).val = Outer.conjugate i := by
    change Outer.evaluate _ * generatorA * (Outer.evaluate _)⁻¹ = _
    rw [outer_representative]
    rfl
  have hi : Function.Injective f := fun i j h => Outer.conjugate_injective (by
    rw [← he i, ← he j, h])
  have hc := Theory.GroupTheory.card_mul_le_of_injective_conjugates OuterInvolutions.seed f hi
    (fun i => isConj_iff.mpr ⟨g i, rfl⟩)
  rw [carrier_order] at hc
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right
    (hc.trans_lt (by decide : 190080 < 298 * 640)))

private theorem fixed_card_le_carrier_centralizer (x : Carrier) :
    Nat.card (automorphismEquiv x).fixedSubgroup ≤
      Nat.card (centralizer ({x} : Set Carrier)) := by
  let f : (automorphismEquiv x).fixedSubgroup → centralizer ({x} : Set Carrier) :=
    fun a => ⟨innerModel.embedding a.val, by
      apply mem_centralizer_singleton_iff.mpr
      apply automorphismEquiv.injective
      rw [map_mul, map_mul, automorphismEquiv_embedding]
      have hf := (MulAut.mem_fixedSubgroup (automorphismEquiv x) a.val).mp a.property
      apply MulEquiv.ext
      intro y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hf]⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  apply Subtype.ext
  apply innerModel.embedding_injective
  exact congrArg (fun t : centralizer ({x} : Set Carrier) => t.val) h

public theorem fixed_card_bound (r : MulAut M12) (hr : orderOf r = 2) :
    Nat.card r.fixedSubgroup ≤ 297 := by
  by_cases hi : ∃ g, r = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hi
    have hg : orderOf g = 2 :=
      (orderOf_injective MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot m12_center_eq_bot) g).symm.trans hr
    rw [MulAut.fixedSubgroup_conj]
    rcases M12InvolutionFusion.involution_fusion g hg with h | h
    · rw [← card_centralizer_eq_of_isConj _ _ h]
      have hc : Nat.card (centralizer ({M12SmallPair.z} : Set M12)) = 192 :=
        M12SmallPair.card_firstParabolic
      omega
    · rw [← card_centralizer_eq_of_isConj _ _ h]
      exact inner_centralizer_bound
  · obtain ⟨x, rfl⟩ := automorphismEquiv.surjective r
    have hx : orderOf x = 2 := (automorphismEquiv.orderOf_eq x).symm.trans hr
    have hn : x ∉ M12ExceptionalExtension.inner := by
      intro hm
      rw [← innerModel.embedding_range] at hm
      obtain ⟨g, rfl⟩ := hm
      exact hi ⟨g, automorphismEquiv_embedding g⟩
    have hc := card_centralizer_eq_of_isConj _ _ (OuterInvolutions.fusion x hx hn)
    exact (fixed_card_le_carrier_centralizer x).trans (hc ▸ outer_centralizer_bound)

end Sporadic.Mathieu.M12FixedOrders

namespace Sporadic.Mathieu

/-- The full fixed subgroup of any involutory automorphism has order below 360. -/
public theorem m12_involution_fixed_card_le (r : MulAut M12) (hr : orderOf r = 2) :
    Nat.card r.fixedSubgroup ≤ 297 := M12FixedOrders.fixed_card_bound r hr

/-- The fixed subgroup cannot contain an alternating-six section of full order. -/
public theorem m12_involution_not_360_dvd_fixed_card (r : MulAut M12)
    (hr : orderOf r = 2) : ¬ 360 ∣ Nat.card r.fixedSubgroup := by
  intro h
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := r.fixedSubgroup)) h
  have hup := m12_involution_fixed_card_le r hr
  omega

/-- The same bound excludes the alternating-seven order used by E.6.18. -/
public theorem m12_involution_not_2520_dvd_fixed_card (r : MulAut M12)
    (hr : orderOf r = 2) : ¬ 2520 ∣ Nat.card r.fixedSubgroup :=
  fun h => m12_involution_not_360_dvd_fixed_card r hr
    (dvd_trans (by norm_num : 360 ∣ 2520) h)

end Sporadic.Mathieu
