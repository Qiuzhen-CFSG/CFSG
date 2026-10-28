module
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Quotient
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

/-!
# Filling a five-by-three tensor subgroup

A subgroup containing A₅ in the first factor and a pure odd permutation
contains all of S₅ there. An elementary actor of rank at least three then
has a nontrivial involution in its S₃ projection. In a proper subgroup of
S₃ that involution is central. Removing its first coordinate gives a
central involution of the original group, contradicting its trivial two-core.
Thus the original embedding is onto S₅ × S₃.

The only finite check is the six-word generation calculation in S₃.
Source: the double-module recognition in Aschbacher--Smith G.11.7--8,
printed pp.366--368; used for the low-rank specialization of G.11.2(9).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymmetricFive

private theorem involution_central_of_proper (K : Subgroup (Equiv.Perm (Fin 3))) (hK : K ≠ ⊤)
    (t : (Equiv.Perm (Fin 3))) (ht : t ∈ K) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∀ u ∈ K, u * t = t * u := by
  intro u hu
  by_contra hne
  have hgen : ∀ t u : (Equiv.Perm (Fin 3)), t ^ 2 = 1 → t ≠ 1 → u * t ≠ t * u →
      ∀ w : (Equiv.Perm (Fin 3)), w = 1 ∨ w = t ∨ w = u ∨ w = t*u ∨ w = u*t ∨ w = t*u*t := by
    decide +kernel
  apply hK
  apply top_unique
  intro w _
  rcases hgen t u ht2 ht1 hne w with rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.one_mem
  · exact ht
  · exact hu
  · exact K.mul_mem ht hu
  · exact K.mul_mem hu ht
  · exact K.mul_mem (K.mul_mem ht hu) ht

/-- A subgroup containing the marked A₅ and an odd element of the first
factor fills S₅ × S₃ when its two-core is trivial and it contains an
 elementary actor of rank at least three. -/
theorem tensor_embedding_surjective
    {G : Type*} [Group G] [Finite G]
    (j : G →* ((Equiv.Perm (Fin 5)) × (Equiv.Perm (Fin 3)))) (hj : Function.Injective j)
    (hA : ∀ s ∈ alternatingGroup (Fin 5), (s,1) ∈ j.range)
    (ho : ∃ s : (Equiv.Perm (Fin 5)), Equiv.Perm.sign s = -1 ∧ (s,1) ∈ j.range)
    (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [IsElementaryAbelian 2 X] (hr : 3 ≤ Group.rank X) :
    Function.Surjective j := by
  have hbase (s : (Equiv.Perm (Fin 5))) : (s,1) ∈ j.range := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs
    · exact hA s (Equiv.Perm.mem_alternatingGroup.mpr hs)
    · obtain ⟨a,ha,ham⟩ := ho
      have hsa : s*a⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hs,ha]
        decide
      have hh := j.range.mul_mem (hA _ hsa) ham
      simpa only [Prod.mk_mul_mk,mul_one,inv_mul_cancel_right] using hh
  obtain ⟨x,hx⟩ : ∃ x : X, (j x).2 ≠ 1 := by
    by_contra! hh
    let f : X →* (Equiv.Perm (Fin 5)) := (MonoidHom.fst (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))).comp (j.comp X.subtype)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact Prod.ext hab ((hh a).trans (hh b).symm)
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hle := f.range.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 f.range)
    rw [← Group.rank_congr (MonoidHom.ofInjective hf)] at hle
    have hb := Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    exact (by omega : ¬ 3 ≤ (2 : ℕ)) (hr.trans (hle.trans hb))
  let t := (j x).2
  have ht2 : t ^ 2 = 1 := by
    have hh := congrArg (fun g => (j g).2) (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property)
    simpa [t] using hh
  let q := (MonoidHom.snd (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))).comp j
  have ht : t ∈ q.range := ⟨x,rfl⟩
  have hpure : (1,t) ∈ j.range := by
    have hh := j.range.mul_mem (j.range.inv_mem (hbase (j x).1)) (show j x ∈ j.range from ⟨x,rfl⟩)
    convert hh using 1
    exact (Prod.ext (by simp) (by simp [t])).symm
  have hq : q.range = ⊤ := by
    by_contra hn
    obtain ⟨c,hc⟩ := hpure
    have hc1 : c ≠ 1 := by
      intro he
      have hh := congrArg Prod.snd hc
      rw [he,map_one] at hh
      exact hx hh.symm
    have hc2 : c ^ 2 = 1 := by
      apply hj
      rw [map_pow,hc,map_one]
      exact Prod.ext (by simp) ht2
    have hcentral : c ∈ center G := by
      apply mem_center_iff.mpr
      intro g
      apply hj
      rw [map_mul,map_mul,hc]
      apply Prod.ext
      · simp
      · exact involution_central_of_proper q.range hn t ht ht2 hx (j g).2 ⟨g,rfl⟩
    have hzc : zpowers c ≤ center G := zpowers_le.mpr hcentral
    let : (zpowers c).Normal := ⟨by
      intro a ha g
      have hcomm := mem_center_iff.mp (hzc ha) g
      simpa only [hcomm,mul_assoc,mul_inv_cancel,mul_one] using ha⟩
    have htwo : IsPGroup 2 (zpowers c) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers,orderOf_eq_prime hc2 hc1,pow_one]
    have hle : zpowers c ≤ pCore 2 G := le_sSup ⟨inferInstance,htwo⟩
    exact hc1 (mem_bot.mp (hcore ▸ hle (mem_zpowers c)))
  intro p
  have hpr : p.2 ∈ q.range := hq ▸ mem_top _
  obtain ⟨g,hg⟩ := hpr
  have hmem : p ∈ j.range := by
    have hh := j.range.mul_mem (hbase (p.1 * (j g).1⁻¹)) (show j g ∈ j.range from ⟨g,rfl⟩)
    convert hh using 1
    apply Prod.ext
    · simp
    · exact hg.symm
  exact hmem
end Theory.SpecificGroups.SymmetricFive
