module
public import Theory.GroupTheory.Hall.TwoComplementConjugacy

/-!
# Lifting centralizers through a normal two-subgroup

An odd solvable subgroup acting trivially modulo a finite normal two-subgroup
has a centralizer supplement to that two-subgroup. Hall conjugacy corrects
each element by a two-element into the normalizer of the odd actor.
The remaining displacement lies in the disjoint odd and two-subgroups,
so the corrected element centralizes the actor.

Only the kernel and odd actor need be finite. This form applies to local
subgroups of an infinite amalgam completion.
Source application: DGS85 (3.2)(c) in the proof of (10.8), pp.160--161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Subgroup.OddHall
variable {G : Type*} [Group G]

/-- An odd actor trivial modulo a normal two-subgroup has enough actual
centralizers to cover that quotient. Only the two local factors need be finite. -/
theorem centralizer_sup_of_two_displacement
    (L Q H : Subgroup G) [Finite Q] [Finite H] [Group.IsSolvable H]
    (hQL : Q ≤ L) (hQ : IsPGroup 2 Q) (hH : Odd (Nat.card H))
    (hLQ : L ≤ normalizer (Q : Set G))
    (hHQ : H ≤ normalizer (Q : Set G))
    (hmove : ⁅L,H⁆ ≤ Q) :
    (L ⊓ centralizer (H : Set G)) ⊔ Q = L := by
  have hdis : Disjoint H Q := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hn]; exact hH.coprime_two_right.pow_right n)
  apply le_antisymm (sup_le inf_le_left hQL)
  intro g hg
  let C := H.map (MulAut.conj g).toMonoidHom
  let _ : Finite C := Finite.of_surjective
    (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective
  have hCg (x : G) (hx : x ∈ H) : g*x*g⁻¹ ∈ C :=
    mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  have hm (x : G) (hx : x ∈ H) : ⁅g,x⁆ ∈ Q :=
    hmove (commutator_mem_commutator hg hx)
  have he : Q ⊔ C = Q ⊔ H := by
    apply le_antisymm
    · apply sup_le le_sup_left
      rintro _ ⟨x,hx,rfl⟩
      have hh := (Q ⊔ H).mul_mem (mem_sup_left (hm x hx)) (mem_sup_right hx)
      change g*x*g⁻¹ ∈ Q ⊔ H
      simpa only [commutatorElement_def,inv_mul_cancel_right] using hh
    · apply sup_le le_sup_left
      intro x hx
      have hh := (Q ⊔ C).mul_mem (mem_sup_left (Q.inv_mem (hm x hx)))
        (mem_sup_right (hCg x hx))
      convert hh using 1
      simp only [commutatorElement_def]
      group
  have hCQ : C ≤ normalizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem (hLQ hg) (hHQ hx))
      ((normalizer (Q : Set G)).inv_mem (hLQ hg))
  have hCo : Nat.Coprime 2 (Nat.card C) := by
    rw [show Nat.card C = Nat.card H from card_map_of_injective (MulAut.conj g).injective]
    exact hH.coprime_two_left
  obtain ⟨q,hq,hqC⟩ := exists_two_conjugator_of_common_sup Q H C hQ hH.coprime_two_left hCo hHQ hCQ he
  have hnH : q*g ∈ normalizer (H : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh : (MulAut.conj q).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (q*g)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
      group
    change (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom = H at hqC
    rwa [Subgroup.map_map,hh] at hqC
  have hnL : q*g ∈ L := L.mul_mem (hQL hq) hg
  have hnC : q*g ∈ centralizer (H : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hmQ : ⁅q*g,x⁆ ∈ Q := hmove (commutator_mem_commutator hnL hx)
    have hmH : ⁅q*g,x⁆ ∈ H := H.mul_mem
      ((mem_normalizer_iff.mp hnH x).mp hx) (H.inv_mem hx)
    exact (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hdis hmH hmQ)).symm
  have hh := ((L ⊓ centralizer (H : Set G)) ⊔ Q).mul_mem
    (mem_sup_right (Q.inv_mem hq)) (mem_sup_left ⟨hnL,hnC⟩)
  simpa only [inv_mul_cancel_left] using hh

end Subgroup.OddHall
