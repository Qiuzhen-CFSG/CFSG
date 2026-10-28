module
public import Theory.GroupAction.SolvablePrimitiveRegular
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree
public import Theory.SpecificGroups.Alternating.SmallSolvableFive
public import Theory.SpecificGroups.AlternatingSeven.OddConjugacyClasses

/-!
# Cyclic odd actors in solvable seven-point Sylow overgroups

A solvable subgroup containing a full Sylow two-subgroup of A7 has order
prime to seven: otherwise its prime-degree action is primitive, and its
characteristic regular abelian subgroup has order seven. The faithful
conjugation action then makes the whole order divide 42, contradicting
its Sylow subgroup of order eight. The established five-exclusion and the
seven-point odd cycle types leave only cyclic orders one and three.

The image form retains an arbitrary original homomorphism and a full
inner Sylow, so it applies to automorphism actions on either A7 cover.
Its source consumer is the original Cartan escape action in Chapter6.
Source: Aschbacher--Smith 5.1.13, printed pp.636--637, refs/quasithin.pdf.
The prime-degree and five-exclusion imports retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.Alternating.SevenCyclicSolvable

private theorem no_seven (J : Subgroup (alternatingGroup (Fin 7)))
    [Group.IsSolvable J] (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSJ : (S : Subgroup _) ≤ J) : ¬ 7 ∣ Nat.card J := by
  intro h7
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 7 h7
  let P := zpowers x
  have hP : Nat.card P = 7 := by rw [Nat.card_zpowers,hx]
  let : MulAction.IsPretransitive P (Fin 7) :=
    Atlas.GroupTheory.prime_subgroup_pretransitive 7 (by simp) P hP
  let : MulAction.IsPretransitive J (Fin 7) := ⟨fun a b => by
    obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P a b
    exact ⟨p,hp⟩⟩
  let : MulAction.IsPreprimitive J (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by norm_num)
  obtain ⟨N,hNc,hNa,_,hreg,hcent⟩ :=
    MulAction.exists_characteristic_abelian_regular (G := J) (0 : Fin 7)
  let := hNc
  let := hNa
  have hN : Nat.card N = 7 := by
    let g : N → Fin 7 := fun n => (n : J) • (0 : Fin 7)
    have hg : Function.Bijective g := by
      constructor
      · intro a b he
        obtain ⟨c,_,hc⟩ := hreg 0 (g b)
        exact (hc a he).trans (hc b rfl).symm
      · intro b
        obtain ⟨a,ha,_⟩ := hreg 0 b
        exact ⟨a,ha⟩
    exact (Nat.card_congr (Equiv.ofBijective g hg)).trans (Nat.card_fin 7)
  let : IsCyclic N := isCyclic_of_prime_card hN
  let f : J →* MulAut N := MulAut.conjNormal
  have hk : f.ker = N := (MulAut.conjNormal_ker_eq_centralizer N).trans hcent
  have hr : Nat.card f.range ∣ 6 := by
    have hh := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut,hN,show Nat.totient 7 = 6 from rfl] at hh
  have hj : Nat.card J ∣ 42 := by
    have hc : Nat.card J = Nat.card f.ker * Nat.card f.range := by
      rw [←index_ker,card_mul_index]
    rw [hc,hk,hN]
    exact Nat.mul_dvd_mul_left 7 hr
  have hs : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hd : 8 ∣ 42 := (hs ▸ card_dvd_of_le hSJ).trans hj
  norm_num at hd

private theorem cyclic_small (J E : Subgroup (alternatingGroup (Fin 7)))
    [Group.IsSolvable J] [IsCyclic E] (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSJ : (S : Subgroup _) ≤ J) (hEJ : E ≤ J) (ho : Odd (Nat.card E)) :
    Nat.card E = 1 ∨ Nat.card E = 3 := by
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hx' : orderOf (x : alternatingGroup (Fin 7)) = Nat.card E :=
    (Subgroup.orderOf_coe x).trans hx
  have ht := alternatingGroup.SevenOddConjugacyClasses.cycleType_of_odd_order
    (x : alternatingGroup (Fin 7)) (by rw [hx']; exact ho.not_two_dvd_nat)
  have he := (x : Equiv.Perm (Fin 7)).lcm_cycleType
  rw [Subgroup.orderOf_coe,hx'] at he
  rcases ht with ht | ht | ht | ht | ht <;> rw [ht] at he <;>
    norm_num [lcm_eq_nat_lcm] at he
  · exact .inl he.symm
  · exact .inr he.symm
  · exact .inr he.symm
  · exact (Theory.SpecificGroups.Alternating.SmallSolvableFive.seven_not_five_dvd
      J inferInstance S hSJ (by have hd := card_dvd_of_le hEJ; rwa [←he] at hd)).elim
  · exact (no_seven J S hSJ (by have hd := card_dvd_of_le hEJ; rwa [←he] at hd)).elim

/-- A cyclic odd image in a solvable permutation group containing a full
Sylow of A7 has order one or three. The original homomorphism is retained. -/
theorem image_card_one_or_three {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 7)) (E J : Subgroup G)
    [IsCyclic E] [Group.IsSolvable J] (hEJ : E ≤ J) (ho : Odd (Nat.card E))
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    (hPJ : (P : Subgroup _).map (alternatingGroup (Fin 7)).subtype ≤ J.map f) :
    Nat.card (E.map f) = 1 ∨ Nat.card (E.map f) = 3 := by
  have hEa : E.map f ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x,hx,rfl⟩
    have hp : f x ^ Nat.card E = 1 := by
      have hh := congrArg (fun y : E => f y) (pow_card_eq_one' (x := (⟨x,hx⟩ : E)))
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using hh
    rw [Equiv.Perm.mem_alternatingGroup]
    have hh := congrArg Equiv.Perm.sign hp
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f x)) with hs | hs
    · exact hs
    · simp only [map_pow,map_one,hs,ho.neg_one_pow] at hh
      exact (by decide : (-1 : ℤˣ) ≠ 1) hh |>.elim
  let J' := (J.map f).subgroupOf (alternatingGroup (Fin 7))
  let E' := (E.map f).subgroupOf (alternatingGroup (Fin 7))
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  let : Group.IsSolvable J' := Group.isSolvable_of_isSolvable_injective
    (f := (alternatingGroup (Fin 7)).subtype.subgroupComap (J.map f))
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : J.map f => (z : Equiv.Perm (Fin 7))) he)))
  let : IsCyclic (E.map f) := isCyclic_of_surjective (f.subgroupMap E) (f.subgroupMap_surjective E)
  let e := subgroupOfEquivOfLe hEa
  let : IsCyclic E' := isCyclic_of_injective e.toMonoidHom e.injective
  have he : Nat.card E' = Nat.card (E.map f) := Nat.card_congr e.toEquiv
  have hh := cyclic_small J' E' P
    (fun x hx => hPJ (mem_map_of_mem (alternatingGroup (Fin 7)).subtype hx))
    (comap_mono (map_mono hEJ)) (by rw [he]; exact ho.of_dvd_nat (card_map_dvd E f))
  rwa [he] at hh


end Theory.SpecificGroups.Alternating.SevenCyclicSolvable
