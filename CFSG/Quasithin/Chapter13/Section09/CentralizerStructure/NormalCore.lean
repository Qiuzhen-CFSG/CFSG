module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.ReducedAction
public import Theory.GroupTheory.ElementaryEightCoreFreePointAction
/-!
# Normality of the marked extraspecial core in the wreath centralizer

In the actual central quotient C_G(z)/⟨z⟩, Q̄ is the elementary Thompson
subgroup of the Sylow two-subgroup. If Q̄ lies in the two-core, weak closure
makes it normal. Otherwise the reduced closure Ū has order at most eight.
The wreath hyperplane-fixer calculation forces the image of Q̄ on Ū to have
four-divisible order, contradicting the small reduced automizer theorem and
the two-group centralizer of the original marked point.

This proves the normality step of Aschbacher–Smith 13.9.8, printed p.972,
from the preceding source setup and the literal coordinate fixer identity.
Neither normality of Q nor any quotient recognition is assumed.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} {m : PairData d}
namespace CoreData
variable (q : CoreData m)

theorem tilde_sylow : ∃ S : Sylow 2 m.Tilde, (S : Subgroup m.Tilde) = m.tilde d.T := by
  exact ⟨(d.T.subtype m.z_central).mapSurjective
    (QuotientGroup.mk'_surjective (m.Z.subgroupOf m.C)),rfl⟩

theorem normal_of_tilde_normal (hn : (m.tilde q.Q).Normal) :
    (q.Q.subgroupOf m.C).Normal := by
  let π := QuotientGroup.mk' (m.Z.subgroupOf m.C)
  have he : (m.tilde q.Q).comap π = q.Q.subgroupOf m.C := by
    apply comap_map_eq_self
    rw [QuotientGroup.ker_mk']
    exact comap_mono q.Z_le
  rw [← he]
  exact hn.comap π

theorem tilde_normal_of_le_core (hq : m.tilde q.Q ≤ pCore 2 m.Tilde) :
    (m.tilde q.Q).Normal := by
  obtain ⟨S,hS⟩ := tilde_sylow (m := m)
  have hcore : pCore 2 m.Tilde ≤ m.tilde d.T := by
    rw [← hS]
    exact pCore_isPGroup.le_sylow_of_normal S
  apply normal_iff_map_conj_eq.mpr
  intro g
  rw [q.tilde_thompson]
  apply Stellmacher.elementaryAbelianMaxJ_map_eq_of_le
  rw [← q.tilde_thompson]
  exact (map_mono hq).trans ((Normal.map_conj_eq (pCore 2 m.Tilde) g).le.trans hcore)


theorem tilde_closure_card_le_eight_of_not_normal (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T) (hn : ¬ (q.Q.subgroupOf m.C).Normal) :
    Nat.card (m.tilde m.U) ≤ 8 := by
  let S := m.tilde d.T
  let U := m.tilde m.U
  have hUS : U ≤ S := map_mono (comap_mono (m.closure_normal_in_T h hE).1)
  have hUe : IsElementaryAbelian 2 U := (m.closure_reduced h hE).elementary
  obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty S
  have hAQ : A ≤ m.tilde q.Q := by
    rw [q.tilde_thompson]
    exact le_sSup hA
  have hU16 : Nat.card U ≤ 16 :=
    (hA.2.2 U hUS hUe).trans (q.tilde_card ▸ Nat.card_le_card_of_injective (inclusion hAQ) (inclusion_injective hAQ))
  have hUne : Nat.card U ≠ 16 := by
    intro hc
    have hUmax : U ∈ Stellmacher.elementaryAbelianMaxSubgroups S := by
      refine ⟨hUS,hUe,fun B hBS hBe => ?_⟩
      exact (hA.2.2 B hBS hBe).trans (hc ▸ q.tilde_card ▸ Nat.card_le_card_of_injective (inclusion hAQ) (inclusion_injective hAQ))
    have hUQ : U ≤ m.tilde q.Q := by
      rw [q.tilde_thompson]
      exact le_sSup hUmax
    have heq : U = m.tilde q.Q := eq_of_le_of_card_ge hUQ (by rw [hc,q.tilde_card])
    exact hn (q.normal_of_tilde_normal (heq ▸ (m.closure_reduced h hE).normal))
  obtain ⟨n,hnc⟩ := hUe.isPGroup.exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra! hng
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ n by omega)
    rw [← hnc] at hh
    norm_num at hh
    exact hUne (by omega)
  change Nat.card U ≤ 8
  rw [hnc]
  exact Nat.pow_le_pow_right (by decide) hnle

end CoreData

namespace PairData
variable (m : PairData d)

theorem tilde_closure_action_core_free (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T) :
    letI : (m.tilde m.U).Normal := (m.closure_reduced h hE).normal
    pCore 2 (MulAut.conjNormal : m.Tilde →* MulAut (m.tilde m.U)).range = ⊥ := by
  let := (m.closure_reduced h hE).normal
  let f : m.Tilde →* MulAut (m.tilde m.U) := MulAut.conjNormal
  have hk : f.ker = centralizer (m.tilde m.U : Set m.Tilde) :=
    MulAut.conjNormal_ker_eq_centralizer _
  let e : (m.Tilde ⧸ centralizer (m.tilde m.U : Set m.Tilde)) ≃* f.range :=
    (QuotientGroup.congr _ _ (MulEquiv.refl _) (by
      change (centralizer (m.tilde m.U : Set m.Tilde)).map (MonoidHom.id _) = f.ker
      rw [Subgroup.map_id,hk])).trans
      (QuotientGroup.quotientKerEquivRange f)
  rw [← pCore_map_iso 2 e,(m.closure_reduced h hE).quotient_pCore_eq_bot,Subgroup.map_bot]

theorem tilde_closure_action_point_stabilizer (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T) :
    letI : (m.tilde m.U).Normal := (m.closure_reduced h hE).normal
    IsPGroup 2 (MulAction.stabilizer
      (MulAut.conjNormal : m.Tilde →* MulAut (m.tilde m.U)).range
      (⟨m.tTilde,m.tTilde_mem_closure⟩ : m.tilde m.U)) := by
  let := (m.closure_reduced h hE).normal
  let f : m.Tilde →* MulAut (m.tilde m.U) := MulAut.conjNormal
  let v : m.tilde m.U := ⟨m.tTilde,m.tTilde_mem_closure⟩
  let D := centralizer ({m.tTilde} : Set m.Tilde)
  let j : D →* MulAction.stabilizer f.range v :=
    { toFun := fun x => ⟨f.rangeRestrict x,by
        change f x v = v
        apply Subtype.ext
        change (x : m.Tilde)*m.tTilde*(x : m.Tilde)⁻¹ = m.tTilde
        rw [mem_centralizer_singleton_iff.mp x.property]
        simp only [mul_assoc,mul_inv_cancel,mul_one]⟩
      map_one' := Subtype.ext (f.rangeRestrict.map_one)
      map_mul' := fun x y => Subtype.ext (f.rangeRestrict.map_mul x y) }
  apply (m.tilde_point_centralizer_isPGroup hE).of_surjective j
  intro a
  obtain ⟨x,hx⟩ := f.rangeRestrict_surjective a.val
  have hxD : x ∈ D := by
    apply mem_centralizer_singleton_iff.mpr
    have hh : f x v = v := by
      change (f.rangeRestrict x : MulAut (m.tilde m.U)) v = v
      rw [hx]
      exact a.property
    have he := congrArg Subtype.val hh
    change x*m.tTilde*x⁻¹ = m.tTilde at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact ⟨⟨x,hxD⟩,Subtype.ext hx⟩

end PairData

namespace CoreData
variable (q : CoreData m)

private theorem card_map_mul_card_inf_ker {H K : Type*} [Group H] [Finite H] [Group K]
    (f : H →* K) (Q : Subgroup H) :
    Nat.card (Q.map f) * Nat.card (Q ⊓ f.ker : Subgroup H) = Nat.card Q := by
  let g := f.comp Q.subtype
  let e : g.ker ≃* (Q ⊓ f.ker : Subgroup H) := {
    toFun := fun x => ⟨x.val,x.val.property,x.property⟩
    invFun := fun x => ⟨⟨x,x.property.1⟩,x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hr : g.range = Q.map f := by rw [MonoidHom.range_comp,Q.range_subtype]
  have hh := g.ker.index_mul_card
  rw [index_ker,hr,Nat.card_congr e.toEquiv] at hh
  exact hh

/-- The actual wreath hyperplane-fixer property forces a four-divisible
image of Q whenever Q has not yet been proved normal. -/
theorem four_dvd_closure_action_of_not_normal (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hn : ¬ (q.Q.subgroupOf m.C).Normal) :
    letI : (m.tilde m.U).Normal := (m.closure_reduced h hE).normal
    4 ∣ Nat.card (MulAut.conjNormal : m.Tilde →* MulAut (m.tilde m.U)).range := by
  let := (m.closure_reduced h hE).normal
  let f : m.Tilde →* MulAut (m.tilde m.U) := MulAut.conjNormal
  have hk : f.ker = pCore 2 m.Tilde := m.tilde_closure_action_ker h hE
  have hnot : ¬ m.tilde q.Q ≤ f.ker := by
    intro hq
    exact hn (q.normal_of_tilde_normal (q.tilde_normal_of_le_core (hk ▸ hq)))
  have hdiv : Nat.card ((m.tilde q.Q).map f) ∣ 16 :=
    q.tilde_card ▸ (m.tilde q.Q).card_map_dvd f
  have hsmall : Nat.card ((m.tilde q.Q).map f) = 1 ∨
      Nat.card ((m.tilde q.Q).map f) = 2 ∨ 4 ∣ Nat.card ((m.tilde q.Q).map f) := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    have hd : (16 : ℕ).divisors = {1,2,4,8,16} := by decide
    rw [hd] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h4 | h8 | h16
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (by rw [h4]))
    · exact Or.inr (Or.inr (by rw [h8]; decide))
    · exact Or.inr (Or.inr (by rw [h16]; decide))
  rcases hsmall with h1 | h2 | hfour
  · exfalso
    exact hnot ((map_eq_bot_iff (m.tilde q.Q)).mp (card_eq_one.mp h1))
  · exfalso
    let E := m.tilde q.Q ⊓ f.ker
    have hE8 : Nat.card E = 8 := by
      have hh := card_map_mul_card_inf_ker f (m.tilde q.Q)
      rw [q.tilde_card,h2] at hh
      change 2 * Nat.card E = 16 at hh
      omega
    have hUS : m.tilde m.U ≤ m.tilde d.T :=
      map_mono (comap_mono (m.closure_normal_in_T h hE).1)
    have hUE : m.tilde m.U ≤ centralizer (E : Set m.Tilde) := by
      apply ((m.closure_reduced h hE).le_centralizer_pCore).trans
      apply centralizer_le
      exact (show E ≤ f.ker from inf_le_right).trans hk.le
    have hUQ := (le_inf hUS hUE).trans (hfix E inf_le_left hE8)
    have hQU := le_centralizer_iff.mp hUQ
    rw [m.tilde_closure_centralizer_eq_pCore h hE] at hQU
    exact hnot (hk.symm ▸ hQU)
  · exact hfour.trans (card_dvd_of_le (map_le_range f (m.tilde q.Q)))

/-- Normality of the actual marked extraspecial core. The inputs are the
preceding source geometry and the literal wreath hyperplane-fixer identity;
normality is derived from the reduced-closure action, not supplied. -/
theorem normal_of_hyperplane_fixers (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde)) :
    (q.Q.subgroupOf m.C).Normal := by
  by_contra hn
  let := (m.closure_reduced h hE).normal
  let := (m.closure_reduced h hE).elementary
  exact not_four_dvd_card_small_elementary_automizer_of_pgroup_stabilizer
    (m.tilde m.U) (q.tilde_closure_card_le_eight_of_not_normal h hE hn)
    (MulAut.conjNormal : m.Tilde →* MulAut (m.tilde m.U)).range
    (m.tilde_closure_action_core_free h hE)
    ⟨m.tTilde,m.tTilde_mem_closure⟩ (m.tilde_closure_action_point_stabilizer h hE)
    (q.four_dvd_closure_action_of_not_normal h hE hfix hn)

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
