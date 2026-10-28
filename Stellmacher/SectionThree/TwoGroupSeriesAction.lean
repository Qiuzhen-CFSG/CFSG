module

public import FeitThompson.GroupAction.SeriesPiGroup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Two-group images of actions stabilizing a normal series

A finite group acting on a finite two-group has two-group image in its
multiplicative automorphism group if it stabilizes an explicit normal series
and acts trivially on each factor. The action and the supplied series are
retained exactly. This is the series-action kernel bound used in Stellmacher's
Section Three local quotient recognition.

The proof specializes the Feit–Thompson normal-series pi-group theorem
(Lemma 1.9) to the singleton prime set `{2}`. The two-group is nilpotent and
hence solvable, so that theorem applies. Its fixing subgroup is the kernel of
the actual action homomorphism; the first isomorphism theorem transports the
pi-group property to the image. Its prime divisors are therefore all two.
-/

namespace Stellmacher.SectionThree

public theorem isPGroup_range_of_stabilizes_two_group_series
    {Q A : Type*} [Group Q] [Finite Q] [Group A] [Finite A]
    [MulDistribMulAction A Q] (hQ : IsPGroup 2 Q)
    {ι : Type*} (Gi : ι → Subgroup Q) (next : ι → ι)
    (hstab : StabilizesNormalSeries (G := Q) (A := A) Gi next) :
    IsPGroup 2 (MulDistribMulAction.toMulAut A Q).range := by
  let : Group.IsNilpotent Q := hQ.isNilpotent
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hpi : IsPiGroup ({two} : Set Nat.Primes) Q := by
    rw [IsPiGroup_iff]
    intro p hp
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    have hp2 : p.val ∣ 2 := p.property.dvd_of_dvd_pow (hn ▸ hp)
    exact Set.mem_singleton_iff.mpr (Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp hp2))
  have hker : (fixingSubgroupOf A Q (Set.univ : Set Q)).Normal := by
    rw [show fixingSubgroupOf A Q (Set.univ : Set Q) =
      (MulDistribMulAction.toMulAut A Q).ker from fixingSubgroup_univ_eq_ker_toMulAut]
    infer_instance
  have hquot := isPiGroup_quotient_fixingSubgroup_of_stabilizesNormalSeries
    ({two} : Set Nat.Primes) (inferInstance : Group.IsSolvable Q) hpi
    ⟨ι, Gi, next, hstab⟩ hker
  have hquotker := hquot.of_equiv
    (QuotientGroup.quotientMulEquivOfEq
      (show fixingSubgroupOf A Q (Set.univ : Set Q) =
        (MulDistribMulAction.toMulAut A Q).ker from
        fixingSubgroup_univ_eq_ker_toMulAut)).symm
  have hrange := hquotker.of_equiv
    (QuotientGroup.quotientKerEquivRange (MulDistribMulAction.toMulAut A Q)).symm
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hp2 := (IsPiGroup_iff _ _).mp hrange ⟨p, hpprime⟩
    (Nat.dvd_of_mem_primeFactors hp)
  have heq : p = 2 := congrArg Subtype.val (Set.mem_singleton_iff.mp hp2)
  simpa only [heq] using Nat.prime_two.mem_primeFactors_self

end Stellmacher.SectionThree
