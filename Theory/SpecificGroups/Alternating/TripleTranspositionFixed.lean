module
public import Theory.SpecificGroups.Alternating.SmallFixedComponents

/-!
# Solvable fixed groups for a triple transposition on A₇

The cycle type `2³` gives centralizer order 48 in S₇. The alternating fixed
group embeds into that centralizer and is therefore solvable. A compatible
map with central kernel lifts solvability to the covering fixed group,
preserving the specified permutation and action.

This applies to the A₇ and 3.A₇ actions of Aschbacher–Smith 1.1.5(3)(d),
printed p.501, and the containing-row inspection in 14.2.15, pp.985–986.
It makes no claim about the nonsolvable transposition fixed subgroup.
-/

public section
open Subgroup Equiv Equiv.Perm Theory.GroupTheory GLS3.Chapter5
namespace alternatingGroup.TripleTranspositionFixed

/-- A literal triple transposition fixes a solvable subgroup of A₇. -/
theorem fixed_solvable (σ : Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2}) :
    Group.IsSolvable (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ).fixedSubgroup := by
  have hc : Nat.card (centralizer ({σ} : Set (Perm (Fin 7)))) = 48 := by
    rw [nat_card_centralizer,hσ]
    norm_num [Nat.factorial]
  let C := centralizer ({σ} : Set (Perm (Fin 7)))
  let : Group.IsSolvable C := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three C
    intro p hp hd
    have hd' : p ∣ 2^4 * 3 := hd.trans (by rw [hc]; norm_num)
    rcases hp.dvd_mul.mp hd' with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  have he : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ).fixedSubgroup =
      automorphismFixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  rw [he]
  exact Group.isSolvable_of_isSolvable_injective
    (f := (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.toMonoidHom)
    (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.injective

/-- A central-kernel map intertwining the literal triple-transposition action
makes the covering fixed subgroup solvable as well. -/
theorem fixed_solvable_of_central_map
    {E : Type*} [Group E] (a : MulAut E)
    (σ : Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (f : E →* alternatingGroup (Fin 7)) (hker : f.ker ≤ center E)
    (hcompat : ∀ x : E, (f (a x) : Perm (Fin 7)) = σ * f x * σ⁻¹) :
    Group.IsSolvable a.fixedSubgroup := by
  let b := MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ
  let := fixed_solvable σ hσ
  let g : a.fixedSubgroup →* b.fixedSubgroup :=
    (f.comp a.fixedSubgroup.subtype).codRestrict _ (by
      intro x
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      change σ * (f x.val : Perm (Fin 7)) * σ⁻¹ = (f x.val : Perm (Fin 7))
      rw [←hcompat, (MulAut.mem_fixedSubgroup _ _).mp x.property])
  have hk (x : g.ker) : (x.val.val : E) ∈ center E :=
    hker (show f x.val.val = 1 from congrArg Subtype.val x.property)
  let j : g.ker →* center E :=
    (a.fixedSubgroup.subtype.comp g.ker.subtype).codRestrict _ hk
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center E => (z : E)) h
  let : Group.IsSolvable (center E) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext ((mem_center_iff.mp x.property y).symm)
  let : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by simp)

end alternatingGroup.TripleTranspositionFixed
