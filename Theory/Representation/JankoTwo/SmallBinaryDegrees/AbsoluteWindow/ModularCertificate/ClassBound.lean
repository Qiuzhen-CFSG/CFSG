module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Mathlib.Algebra.Group.ConjFinite

/-!
# The ten-class bound for Hall--Janko modular saturation

Eleven of the 21 literal representatives have even order. For each, the kernel
checks that the power at twice a specified exponent is the identity, and that
the power at that exponent is not. The four-point carrier base suffices for the
identity checks. Coprimality then forces even order. Thus exhaustive coverage
by the 21 representatives implies at most ten odd-order conjugacy classes.

Coverage remains an explicit input, owned by the independent power-fusion
calculation. No external class sizes, element orders, or class counts are used
as premises. `ModularCertificate` applies this bound to actual simple actions.

Source: the literal ATLAS `J2G1-p100B0` normal forms and representative indices
in `PowerFusion/Data.lean`; original data attribution is retained there.
-/

open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate


private def evenIndex : Fin 11 → Fin 21 := ![6,8,9,12,13,14,15,16,17,18,20]
private def halfOrder : Fin 11 → ℕ := ![1,3,1,5,5,3,5,5,2,6,4]
/-- The ten indices left after the even-order representatives are removed. -/
@[expose] def oddIndex : Fin 10 → Fin 21 := ![0,1,2,3,4,5,7,10,11,19]

set_option maxRecDepth 10000 in
private theorem even_pow_check : ∀ j : Fin 11, ∀ x : Fin 4,
    (normalForm (representativeIndex (evenIndex j)) ^ (halfOrder j * 2))
      (x.castLE (by decide)) = x.castLE (by decide) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem even_ne_check : ∀ j : Fin 11, ∃ x : Fin 4,
    (normalForm (representativeIndex (evenIndex j)) ^ halfOrder j)
      (x.castLE (by decide)) ≠ x.castLE (by decide) := by
  apply allFin
  decide +kernel

private theorem even_order (j : Fin 11) : 2 ∣ orderOf (representative (evenIndex j)) := by
  have hp : representative (evenIndex j) ^ (halfOrder j * 2) = 1 := by
    apply carrier_ext_base
    intro x
    simpa only [map_pow, representative, inclusion_element, map_one, Equiv.Perm.one_apply]
      using even_pow_check j x
  have hn : representative (evenIndex j) ^ halfOrder j ≠ 1 := by
    intro h
    obtain ⟨x,hx⟩ := even_ne_check j
    apply hx
    have he := congrArg (fun g : Carrier => inclusion g (x.castLE (by decide))) h
    simpa only [map_pow, representative, inclusion_element, map_one, Equiv.Perm.one_apply]
      using he
  by_contra h
  have hc := (Nat.prime_two.coprime_iff_not_dvd.mpr h).symm
  exact hn (orderOf_dvd_iff_pow_eq_one.mp
    (hc.dvd_mul_right.mp (orderOf_dvd_of_pow_eq_one hp)))

private theorem split_index (i : Fin 21) :
    (∃ j, oddIndex j = i) ∨ ∃ j, evenIndex j = i := by
  revert i
  decide

/-- Any odd-order element is conjugate to one of ten representatives, once
exhaustive coverage of the existing 21 representatives is supplied. -/
theorem odd_cover (hcover : RepresentativeCoverage) (g : Carrier) (hg : ¬2 ∣ orderOf g) :
    ∃ j : Fin 10, IsConj (representative (oddIndex j)) g := by
  obtain ⟨i,hi⟩ := hcover g
  rcases split_index i with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · exact ⟨j,hi⟩
  · obtain ⟨c,hc⟩ := hi
    exact (hg (hc.orderOf_eq (↑c : Carrier) ▸ even_order j)).elim

/-- The checked even-order exclusions turn the existing coverage contract into
the characteristic-two class bound used by modular trace saturation. -/
theorem odd_class_bound (hcover : RepresentativeCoverage) :
    Nat.card (ConjClasses.mk '' {g : Carrier | ¬2 ∣ orderOf g}) ≤ 10 := by
  classical
  let f : Fin 10 → ConjClasses Carrier := fun j => ConjClasses.mk (representative (oddIndex j))
  have hsub : ConjClasses.mk '' {g : Carrier | ¬2 ∣ orderOf g} ⊆ Set.range f := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨j,hj⟩ := odd_cover hcover g hg
    exact ⟨j, ConjClasses.mk_eq_mk_iff_isConj.mpr hj⟩
  calc
    _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    _ ≤ Nat.card (Fin 10) := Nat.card_le_card_of_surjective
      (fun j => (⟨f j, Set.mem_range_self j⟩ : Set.range f)) (by
        rintro ⟨_,j,rfl⟩
        exact ⟨j,rfl⟩)
    _ = 10 := Nat.card_fin _

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
