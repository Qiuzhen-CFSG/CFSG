module
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Solvable

/-!
# Pointwise automorphism fixers of seven-divisible subgroups of A₇

An automorphism of A₇ is induced by a permutation on its seven letters.
A seven-cycle has cyclic centralizer of order seven. Thus a permutation
centralizing a nonsolvable subgroup whose order is divisible by seven
must be the identity. The ambient-group version retains the original
subgroup inclusion and conjugation action.

The application in LocalConfigurationRigidityHigherSevenFixer uses this
pointwise statement to preserve the original commutator hyperplane.
Source: GLS III, Theorem 5.2.1 (via Theory.Alternating.Aut), and the
centralizer formula for a full cycle.
-/

public noncomputable section
open Subgroup Equiv Equiv.Perm
namespace AlternatingSeven.SevenFixer
private abbrev A7 := alternatingGroup (Fin 7)
private abbrev S7 := Perm (Fin 7)

private theorem centralizer_card (g : S7) (hg : orderOf g = 7) :
    Nat.card (centralizer ({g} : Set S7)) = 7 := by
  have hc : g.IsCycle := isCycle_of_prime_order' (by rw [hg]; decide) (by simp [hg])
  rw [nat_card_centralizer,hc.cycleType,←hc.orderOf,hg]
  norm_num

private theorem centralizer_eq_one (B : Subgroup A7)
    (hns : ¬ Group.IsSolvable B) (hseven : 7 ∣ Nat.card B)
    (x : S7) (hx : ∀ b : B, x * (b.val.val) = (b.val.val) * x) : x = 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 hseven
  have hb' : orderOf (b.val.val) = 7 := by simpa only [Subgroup.orderOf_coe] using hb
  have hd := (centralizer ({b.val.val} : Set S7)).orderOf_dvd_natCard
    (mem_centralizer_singleton_iff.mpr (hx b))
  rw [centralizer_card _ hb'] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with h1 | h7
  · exact orderOf_eq_one_iff.mp h1
  · let E := centralizer ({x} : Set S7)
    let : IsCyclic E := isCyclic_of_prime_card (centralizer_card x h7)
    let : Group.IsSolvable E := Group.isSolvable_of_comm
      (fun a b => IsCyclic.isMulCommutative.is_comm.comm a b)
    let f : B →* E := ((alternatingGroup (Fin 7)).subtype.comp B.subtype).codRestrict E
      (fun b => mem_centralizer_singleton_iff.mpr (hx b).symm)
    have hi : Function.Injective f := by
      intro b c he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : S7)) he))
    exact (hns (Group.isSolvable_of_isSolvable_injective hi)).elim

/-- An automorphism fixing a nonsolvable subgroup of order divisible by seven
pointwise is trivial, with the original subgroup embedding retained. -/
theorem automorphism_eq_one (B : Subgroup (alternatingGroup (Fin 7)))
    (hns : ¬ Group.IsSolvable B) (hseven : 7 ∣ Nat.card B)
    (a : MulAut (alternatingGroup (Fin 7))) (ha : ∀ b : B, a b.val = b.val) : a = 1 := by
  obtain ⟨x,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).surjective a
  have hx : x = 1 := centralizer_eq_one B hns hseven x (by
    intro b
    have hh := congrArg Subtype.val (ha b)
    change x * b.val.val * x⁻¹ = b.val.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh)
  rw [hx,map_one]

end AlternatingSeven.SevenFixer

namespace AlternatingSeven.SevenFixer
variable {X : Type*} [Group X]

/-- Centralizing a nonsolvable seven-divisible subgroup of A₇ forces an
ambient normalizer element to centralize the whole A₇, retaining both embeddings. -/
theorem centralizes_of_centralizes_subgroup
    (K B : Subgroup X) (hBK : B ≤ K) (e : K ≃* alternatingGroup (Fin 7))
    (hns : ¬ Group.IsSolvable B) (hseven : 7 ∣ Nat.card B)
    (x : X) (hxK : x ∈ normalizer (K : Set X))
    (hxB : x ∈ centralizer (B : Set X)) : x ∈ centralizer (K : Set X) := by
  let D := B.subgroupOf K
  let E := D.map e.toMonoidHom
  let j : B ≃* E := (subgroupOfEquivOfLe hBK).symm.trans
    (D.equivMapOfInjective e.toMonoidHom e.injective)
  have hE : ¬ Group.IsSolvable E := fun hs => hns (by
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  have h7 : 7 ∣ Nat.card E := (Nat.card_congr j.toEquiv) ▸ hseven
  let a := K.normalizerMonoidHom ⟨x,hxK⟩
  have ha : (MulAut.congr e) a = 1 := automorphism_eq_one E hE h7 _ (by
    intro b
    obtain ⟨c,rfl⟩ := j.surjective b
    change e (a (e.symm (e (⟨c,hBK c.property⟩ : K)))) = e (⟨c,hBK c.property⟩ : K)
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change x * (c : X) * x⁻¹ = (c : X)
    rw [← hxB c c.property,mul_inv_cancel_right])
  have ha' : a = 1 := (MulAut.congr e).injective (ha.trans (map_one _).symm)
  intro k hk
  have he := congrArg (fun z : MulAut K => (z ⟨k,hk⟩ : X)) ha'
  change x*k*x⁻¹ = k at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end AlternatingSeven.SevenFixer
