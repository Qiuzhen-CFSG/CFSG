module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.PrimeSupport
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.Presentation
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.MatrixMarking
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder
public import Theory.GroupTheory.PresentedCentralKernelRank
public import Theory.GroupTheory.CentralCoprimeCardLift

/-!
# From the four-relator presentation to two kernel generators

Five does not divide the actual canonical kernel order, by the already proved
prime-support theorem. Thus the order-five presentation generators have lifts
whose fifth powers are one. Perfectness makes these lifts generate the cover,
and centrality makes the two remaining relator images generate its full kernel.
Transfer then gives the same generator bound for the literal Sylow two-subgroup.

The checked coset certificate proves that the abstract presentation is finite
of order at most 20160. The explicit matrix marking maps it onto matrix PSL₃(4),
whose order is 20160, so this map is an isomorphism. Together these results
discharge the presentation comparison and prove the unconditional Sylow rank
bound, without using the paper's multiplier assertion.

Sources: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11;
Aschbacher–Smith I.1.3(6), printed p.407 (PDF p.418); GLS3 §6.1.
-/

public section

open scoped IsMulCommutative

namespace Matrix.PSL3.ExceptionalFourCover

open TwoGeneratorPresentation

/-- The complete presentation comparison bounds even the full canonical kernel
by two generators. No kernel order, exponent or realization is assumed. -/
theorem kernel_rank_le_two_of_presentation_equiv
    (e : Presentation ≃* PSL3Four.PSL) : Group.rank cover.toMonoidHom.ker ≤ 2 := by
  classical
  have hcop : (Nat.card cover.toMonoidHom.ker).Coprime 5 := by
    apply Nat.Coprime.symm
    apply (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr
    intro hd
    have h := kernel_prime_dvd_eq_two_or_three (by decide : Nat.Prime 5) hd
    omega
  have hlift (i : Fin 2) : ∃ x : CoverGroup,
      cover x = e (PresentedGroup.of i) ∧ x ^ 5 = 1 :=
    cover.toMonoidHom.exists_pow_eq_one_lift_of_central_coprime_ker
      cover.surjective cover.ker_le_center hcop (e (PresentedGroup.of i))
      (by rw [← map_pow, generator_pow_five, map_one])
  choose x hx hpow using hlift
  let f := FreeGroup.lift x
  have hk := PresentedGroup.ker_eq_closure_relator_images relators cover.toMonoidHom
    cover.ker_le_center e x hx
  let t : Finset CoverGroup := {f ((a * b) ^ 3), f mixed}
  have hkt : cover.toMonoidHom.ker = Subgroup.closure (t : Set CoverGroup) := by
    rw [hk]
    simp only [relators, Set.image_insert_eq, Set.image_singleton,
      map_pow, a, b, FreeGroup.lift_apply_of, hpow]
    simp [t, f, a, b]
  rw [Subgroup.rank_congr hkt]
  exact (Subgroup.rank_closure_finset_le_card t).trans Finset.card_le_two

/-- Apply the presentation argument to the literal Sylow subgroup of the actual
canonical universal kernel, using transfer inside that abelian kernel. -/
theorem two_sylow_rank_le_two_of_presentation_equiv
    (e : Presentation ≃* PSL3Four.PSL)
    (P : Sylow 2 cover.toMonoidHom.ker) : Group.rank P ≤ 2 := by
  let : IsMulCommutative cover.toMonoidHom.ker := by
    refine ⟨⟨fun x y => ?_⟩⟩
    exact Subtype.ext (Subgroup.mem_center_iff.mp (cover.ker_le_center x.property) y).symm
  exact P.rank_le_of_isMulCommutative.trans (kernel_rank_le_two_of_presentation_equiv e)

/-- Independent abstract-order and concrete-surjectivity inputs identify the
presentation and give the required kernel rank bound. Finiteness is essential:
`Nat.card` alone would give no upper bound for an infinite presented group. -/
theorem two_sylow_rank_le_two_of_presentation_surjective [Finite Presentation]
    (f : Presentation →* PSL3Four.PSL) (hf : Function.Surjective f)
    (hcard : Nat.card Presentation ≤ 20160)
    (P : Sylow 2 cover.toMonoidHom.ker) : Group.rank P ≤ 2 := by
  apply two_sylow_rank_le_two_of_presentation_equiv
    (MulEquiv.ofBijective f (hf.bijective_of_nat_card_le ?_)) P
  simpa only [PSL3Four.card_PSL] using hcard

/-- The two-primary part of the actual canonical universal kernel needs at most
two generators. The checked presentation order and matrix marking discharge all
comparison premises in the presentation argument. This supplies the rank input
to `kernel_card_le_of_two_rank_and_exponent` in `KernelBound`. -/
theorem two_sylow_rank_le_two (P : Sylow 2 cover.toMonoidHom.ker) :
    Group.rank P ≤ 2 := by
  let : Finite Presentation := finite_and_card_le.1
  exact two_sylow_rank_le_two_of_presentation_surjective
    matrixMap matrixMap_surjective finite_and_card_le.2 P

end Matrix.PSL3.ExceptionalFourCover
