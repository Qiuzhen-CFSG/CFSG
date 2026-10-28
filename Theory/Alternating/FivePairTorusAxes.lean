module
public import Theory.Alternating.FivePairBorelTorus
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Coordinate axes of an order-nine torus in an A₅ pair

An embedded three-group of order nine in A₅ × A₅ has both coordinate images
of order three. The opposite projection kernels are disjoint subgroups of
order three and generate the original torus. This supplies the literal axes
for the natural A₅ branch of Aschbacher–Smith 10.2.3, printed p.746.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
local notation "A" => alternatingGroup (Fin 5)

theorem nine_torus_coordinate_kernels
    {D : Type*} [Group D] [Finite D] (q : D →* A × A)
    (hq : Function.Injective q) (hD : IsPGroup 3 D) (hc : Nat.card D = 9) :
    let q1 := (MonoidHom.fst A A).comp q
    let q2 := (MonoidHom.snd A A).comp q
    Nat.card q1.ker = 3 ∧ Nat.card q2.ker = 3 ∧
      Disjoint q1.ker q2.ker ∧ q1.ker ⊔ q2.ker = ⊤ := by
  dsimp only
  let q1 := (MonoidHom.fst A A).comp q
  let q2 := (MonoidHom.snd A A).comp q
  have hp1 : IsPGroup 3 q1.range := hD.of_surjective q1.rangeRestrict q1.rangeRestrict_surjective
  have hp2 : IsPGroup 3 q2.range := hD.of_surjective q2.rangeRestrict q2.rangeRestrict_surjective
  have h1 := three_subgroup_card_dvd_three q1.range hp1
  have h2 := three_subgroup_card_dvd_three q2.range hp2
  let f := q1.rangeRestrict.prod q2.rangeRestrict
  have hf : Function.Injective f := by
    intro x y h
    apply hq
    exact Prod.ext (congrArg (fun z => ((z.1 : q1.range) : A)) h)
      (congrArg (fun z => ((z.2 : q2.range) : A)) h)
  have hbound := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,hc] at hbound
  have hr1 : Nat.card q1.range = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ h1 with h|h
    · rcases Nat.prime_three.eq_one_or_self_of_dvd _ h2 with hh|hh <;>
        simp only [h,hh] at hbound <;> omega
    · exact h
  have hr2 : Nat.card q2.range = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ h2 with h|h
    · simp only [hr1,h] at hbound
      omega
    · exact h
  have hk1 : Nat.card q1.ker = 3 := by
    have hm := q1.ker.card_mul_index
    rw [index_ker,hr1,hc] at hm
    omega
  have hk2 : Nat.card q2.ker = 3 := by
    have hm := q2.ker.card_mul_index
    rw [index_ker,hr2,hc] at hm
    omega
  have hd : Disjoint q1.ker q2.ker := by
    apply disjoint_def.mpr
    intro x hx1 hx2
    apply hq
    rw [map_one]
    exact Prod.ext hx1 hx2
  refine ⟨hk1,hk2,hd,?_⟩
  apply eq_top_of_card_eq
  rw [card_sup_eq_mul_of_normalizes_of_disjoint q1.ker q2.ker
    (by rw [normalizer_eq_top]; exact le_top) hd,hk1,hk2,hc]

end Theory.AlternatingFive
