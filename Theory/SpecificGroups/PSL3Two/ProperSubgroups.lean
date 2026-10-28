module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PCoreImage

/-!
# Solvable proper subgroups of the binary linear three-group

The faithful coset action of SL₃(2) forces a proper subgroup to have index
at least six and hence order at most 28. If seven divides its order, a Sylow
seven-subgroup has index at most four. Otherwise only two and three divide
its order. Both cases are solvable. The result lifts over a two-core when
the subgroup contains that whole core.

Source application: Aschbacher--Smith 10.2.10, printed p.753, for the
opposite component's point stabilizer in the original linear-three pair.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two

/-- Every proper subgroup of the actual SL₃(2) is solvable. -/
theorem isSolvable_subgroup_SL_of_ne_top
    (H : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))) (hne : H ≠ ⊤) :
    Group.IsSolvable H := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hi : 6 ≤ H.index := by
    by_contra h
    apply hne
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show H.index ≤ 5 by omega)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hc : Nat.card H ≤ 28 := by
    have hh := H.card_mul_index
    rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hh
    nlinarith
  by_cases hseven : 7 ∣ Nat.card H
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let P : Sylow 7 H := Classical.choice inferInstance
    let := P.isPGroup'.isNilpotent
    apply P.toSubgroup.isSolvable_of_index_le_four
    have hP : 7 ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (P.dvd_card_of_dvd_card hseven)
    have hh := P.toSubgroup.card_mul_index
    nlinarith
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hd' : p ∣ 2 ^ 3 * 3 * 7 := by
    simpa only [Atlas.Comparisons.Exceptional.sl3Two_card, Nat.reducePow, Nat.reduceMul] using
      hd.trans H.card_subgroup_dvd_card
  rcases hp.dvd_mul.mp hd' with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)
  · have he : p = 7 := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h
      |>.resolve_left hp.ne_one
    exact (hseven (he ▸ hd)).elim

/-- A proper subgroup over the full two-core of an SL₃(2) extension is solvable. -/
theorem isSolvable_proper_subgroup_containing_twoCore
    {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ pCore 2 K) ≃* SpecialLinearGroup (Fin 3) (ZMod 2))
    (H : Subgroup K) (hne : H ≠ ⊤) (hcore : pCore 2 K ≤ H) :
    Group.IsSolvable H := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hproper : H.map q ≠ ⊤ := by
    intro he
    apply hne
    have hh := congrArg (comap q) he
    rwa [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,comap_top] at hh
  have hp : (H.map q).map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hproper
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  let : Group.IsSolvable ((H.map q).map e.toMonoidHom) :=
    isSolvable_subgroup_SL_of_ne_top _ hp
  let : Group.IsSolvable (H.map q) := Group.isSolvable_of_isSolvable_injective
    (f := (equivMapOfInjective (H.map q) e.toMonoidHom e.injective).toMonoidHom)
    (equivMapOfInjective (H.map q) e.toMonoidHom e.injective).injective
  let := (pCore_isPGroup (p := 2) (G := K)).isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable ((H.map q).comap q) := isSolvable_comap_of_solvable_ker q _
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map q H)) (inclusion_injective _)

end Matrix.PSL3Two
