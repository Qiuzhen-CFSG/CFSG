module

public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Two-central involutions in normal subgroups

An even normal subgroup of a finite group contains an involution central in
some ambient Sylow two-subgroup. Extend a nontrivial two-subgroup to an ambient
Sylow subgroup and apply the central intersection theorem inside that Sylow.
This is the elementary normal-subgroup step in GLS IV, Chapter 2, Lemma 15.4.
-/

public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup

theorem exists_twoCentral_involution_in_normal
    {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : 2 ∣ Nat.card N) :
    ∃ u : H, u ∈ N ∧ orderOf u = 2 ∧ TwoCentral u := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hN
  have hx' : orderOf (x : H) = 2 := by simpa using hx
  have hp : IsPGroup 2 (zpowers (x : H)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx')
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hxS : (x : H) ∈ S := hS (mem_zpowers _)
  let E := N.subgroupOf (S : Subgroup H)
  have hE : Nontrivial E := by
    refine ⟨⟨⟨⟨x, hxS⟩, x.property⟩, 1, ?_⟩⟩
    intro he
    have hx1 : x = 1 := Subtype.ext (congrArg (fun a : E => ((a : S) : H)) he)
    rw [hx1, orderOf_one] at hx
    omega
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨C, _, hCE, hC, hCZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) E hE
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hC])
  refine ⟨((u : S) : H), hCE u.property, ?_, S, (u : S).property, ?_⟩
  · simpa using hu
  · exact hCZ u.property

end Theory.GroupTheory.DoubleCoverCentralizer
