module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.PrimeSupport
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoExponent
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Recognition
public import Mathlib.GroupTheory.Schreier

/-!
# The exceptional PSL₃(4) universal kernel has order at most 48

The odd part of the actual canonical universal kernel divides three.
Its two-primary part is abelian, has at most two generators, and has
exponent dividing four, so its order divides sixteen. Thus the whole
kernel order divides 48. The two-primary inputs come respectively from
the checked four-relator presentation of the actual matrix group and
central Sylow transfer with the commutator calculation over UT₃(F₄).

The resulting unconditional bound discharges the upper-bound premise of
`Recognition.isUniversal_of_cover_and_bound` and
`Recognition.kernelEquivOfCoverAndBound`. The independent extension
realizing C₄ × C₄ × C₃ supplies their remaining lower-bound input.

This proves the upper-bound part of Aschbacher–Smith I.1.3(6), printed
p.407 (PDF p.418), and GLS3 §6.1, Theorem 6.1.4, without assuming a
multiplier table or a realization of the exceptional kernel.
-/

public section

open Theory.GroupTheory
open scoped IsMulCommutative

namespace Matrix.PSL3.ExceptionalFourCover

universe w

/-- A two-primary bound combines with the proved odd part to bound the
literal universal kernel. -/
theorem kernel_card_dvd_of_two_sylow_card_dvd
    (P : Sylow 2 cover.toMonoidHom.ker) (hP : Nat.card P ∣ 16) :
    Nat.card cover.toMonoidHom.ker ∣ 48 := by
  have h := Nat.mul_dvd_mul hP kernel_odd_part_dvd_three
  rw [P.card_eq_multiplicity, Nat.ordProj_mul_ordCompl_eq_self] at h
  exact h

/-- An abelian two-primary kernel with two generators and exponent at most
four has order dividing sixteen. The odd part then contributes at most three. -/
theorem kernel_card_dvd_of_two_rank_and_exponent
    (P : Sylow 2 cover.toMonoidHom.ker)
    (hrank : Group.rank P ≤ 2) (hexp : ∀ x : P, x ^ 4 = 1) :
    Nat.card cover.toMonoidHom.ker ∣ 48 := by
  let : IsMulCommutative cover.toMonoidHom.ker := by
    refine ⟨⟨fun x y => ?_⟩⟩
    exact Subtype.ext (Subgroup.mem_center_iff.mp
      (cover.ker_le_center x.property) y).symm
  let : CommGroup P := IsMulCommutative.instCommGroup
  apply kernel_card_dvd_of_two_sylow_card_dvd P
  exact (card_dvd_exponent_pow_rank' P hexp).trans
    (show (4 : ℕ) ^ Group.rank P ∣ 16 from pow_dvd_pow (4 : ℕ) hrank)

/-- Assemble the upper bound from the two-primary structure inputs. -/
theorem kernel_card_le_of_two_rank_and_exponent
    (P : Sylow 2 cover.toMonoidHom.ker)
    (hrank : Group.rank P ≤ 2) (hexp : ∀ x : P, x ^ 4 = 1) :
    Nat.card cover.toMonoidHom.ker ≤ 48 :=
  Nat.le_of_dvd (by decide) (kernel_card_dvd_of_two_rank_and_exponent P hrank hexp)

/-- Apply the two-primary structure bounds to the actual recognition consumer.
The independently constructed extension supplies the lower bound. -/
theorem isUniversal_of_cover_and_two_bounds
    {L : Type} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (P : Sylow 2 cover.toMonoidHom.ker)
    (hrank : Group.rank P ≤ 2) (hexp : ∀ x : P, x ^ 4 = 1) :
    Covering.IsUniversal.{0, 0, w} f :=
  isUniversal_of_cover_and_bound f e
    (kernel_card_le_of_two_rank_and_exponent P hrank hexp)

/-- The order of the actual canonical universal kernel of PSL₃(4) divides 48. -/
theorem kernel_card_dvd : Nat.card cover.toMonoidHom.ker ∣ 48 := by
  let P : Sylow 2 cover.toMonoidHom.ker := Classical.choice inferInstance
  exact kernel_card_dvd_of_two_rank_and_exponent P
    (two_sylow_rank_le_two P) (two_sylow_pow_four P)

/-- The upper bound for the actual canonical universal kernel of PSL₃(4). -/
theorem kernel_card_le : Nat.card cover.toMonoidHom.ker ≤ 48 :=
  Nat.le_of_dvd (by decide) kernel_card_dvd

/-- An extension realizing C₄ × C₄ × C₃ is universal: the upper-bound
premise of `isUniversal_of_cover_and_bound` is now discharged. -/
theorem isUniversal_of_cover
    {L : Type} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier) :
    Covering.IsUniversal.{0, 0, w} f :=
  isUniversal_of_cover_and_bound f e kernel_card_le

/-- An extension realizing the exceptional kernel identifies the literal
canonical kernel, with no additional cardinal-bound premise. -/
noncomputable def kernelEquivOfCover
    {L : Type} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier) :
    cover.toMonoidHom.ker ≃* Multiplier :=
  kernelEquivOfCoverAndBound f e kernel_card_le

end Matrix.PSL3.ExceptionalFourCover
