module

public import Theory.GroupAction.FiveFourSixteenOrbits
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Every five-four orbit meets an involution's fixed subgroup

In a faithful action of C5 semidirect C4 on a group of order sixteen,
every orbit meets the fixed subgroup of any prescribed involution.
Nonidentity orbits have size five or ten, so their stabilizers have even
order. All involutions of the acting group are conjugate, since its Sylow
two-subgroups are cyclic. Conjugating an involution in the point stabilizer
to the prescribed one moves the point into its fixed subgroup.

This is the quotient-orbit argument used to move derived involutions into
the common elementary eight in Thompson VI, printed pp.627--630.
-/

namespace Theory.GroupAction
open Subgroup MulAction

private theorem involutions_conjugate_of_cyclic_sylow
    {M : Type*} [Group M] [Finite M]
    (S : Sylow 2 M) [IsCyclic S]
    (a b : M) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha)
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hb)
  have horder (c : M) (hc : orderOf c = 2) (d : S) (hd : IsConj c (d : M)) :
      orderOf d = 2 := by
    rw [← Subgroup.orderOf_coe]
    obtain ⟨g, hg⟩ := isConj_iff.mp hd
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq c).trans hc
  have hxy : x = y := IsCyclic.eq_of_orderOf_eq_two (horder a ha x hx) (horder b hb y hy)
  exact hx.trans (hxy ▸ hy.symm)

/-- Every orbit meets the fixed subgroup of a prescribed involution.
Faithfulness of the semidirect-product action on its five-subgroup is not
needed for this orbit statement. -/
public theorem five_four_orbit_meets_involution_fixed
    {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (u : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hu : orderOf u = 2) (v : V) :
    ∃ g, f u (f g v) = f g v := by
  classical
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let _ : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let _ : MulDistribMulAction M V := MulDistribMulAction.compHom V f
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hv : v = 1
  · exact ⟨1, by simp [hv]⟩
  let O := orbit M v
  let B := stabilizer M v
  have hM : Nat.card M = 20 := by rw [SemidirectProduct.card]; norm_num
  have hcount : Nat.card O * Nat.card B = 20 := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup M v), hM]
  have hfive : 5 ∣ Nat.card O := five_dvd_orbit_card_of_faithful_five_four_action hV φ f hf v hv
  let _ : Nonempty O := ⟨⟨v, mem_orbit_self v⟩⟩
  have hpos : 0 < Nat.card O := Nat.card_pos
  have hbound : Nat.card O ≤ 15 := by
    let j : O → {w : V // w ≠ 1} := fun w => ⟨w, by
      intro hw
      obtain ⟨g, hg⟩ := w.property
      exact hv ((f g).injective (hg.trans (hw.trans (map_one (f g)).symm)))⟩
    have hj : Function.Injective j := by
      intro a b h
      exact Subtype.ext (congrArg (fun w : {w : V // w ≠ 1} => (w : V)) h)
    have hc : Nat.card {w : V // w ≠ 1} = 15 := by
      let _ : Fintype V := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        ← Nat.card_eq_fintype_card, hV]
      simp
    exact (Nat.card_le_card_of_injective j hj).trans_eq hc
  have hB : 2 ∣ Nat.card B := by
    obtain ⟨k, hk⟩ := hfive
    have hcases : Nat.card O = 5 ∨ Nat.card O = 10 ∨ Nat.card O = 15 := by omega
    rcases hcases with h | h | h <;> rw [h] at hcount <;> omega
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 hB
  let S : Sylow 2 M := default
  let _ : IsCyclic S := (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four
    φ (S : Subgroup M) S.isPGroup').1
  have hconj := involutions_conjugate_of_cyclic_sylow S (b : M) u
    (by simpa using hb) hu
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine ⟨g, ?_⟩
  have hfix : f (b : M) v = v := b.property
  have heq : u * g = g * (b : M) := by rw [← hg]; group
  calc
    f u (f g v) = f (u * g) v := by rw [map_mul]; rfl
    _ = f (g * (b : M)) v := by rw [heq]
    _ = f g v := by rw [map_mul]; change f g (f (b : M) v) = f g v; rw [hfix]

end Theory.GroupAction
