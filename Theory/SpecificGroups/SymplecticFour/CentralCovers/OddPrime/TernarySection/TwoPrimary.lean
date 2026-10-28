module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.PrimeSupport
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.MatrixGeometry
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.PrimaryReduction
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# Two-primary kernel exclusion over the literal Sp₄(3)

First quotient a finite perfect central cover by the odd-order complement
in its kernel. The remaining kernel is a two-group. The embedded SL₂(3) wreath C₂
subgroup permutes two orthogonal hyperbolic planes and has index 45. Its rank-one factors lift uniquely,
and the plane swap is conjugate to the involution acting as minus identity
on one plane. This constructs a section over the subgroup. Central transfer
therefore excludes two from the covering kernel. The primary reduction
then gives the same exclusion for the original arbitrary central kernel.

The conclusion is the exact two-primary input of
`TernarySection.exists_section_of_not_two_dvd_of_not_three_dvd`. Neither
three-primary exclusion nor a Schur multiplier table is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.4(1),
printed p.408, and GLS3 §6.1. The source lists the isomorphic projective
endpoint as U₄(2); the present theorem works directly with
`Matrix.symplecticGroup (Fin 2) (ZMod 3)`.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary

/-- The embedded rank-one wreath product has odd index in the literal matrix group. -/
theorem wreath_range_index (j : Wreath →* OddPrime.Sp (ZMod 3))
    (hj : Function.Injective j) : j.range.index = 45 := by
  have hc : Nat.card j.range = 1152 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans wreath_card
  have hi := j.range.card_mul_index
  rw [hc, card_sp_three] at hi
  omega

/-- Matrix embedding and involution fusion exclude a two-group kernel. -/
theorem not_two_dvd_kernel_of_wreath_of_isPGroup
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3)))
    (hk : IsPGroup 2 f.toMonoidHom.ker)
    (j : Wreath →* OddPrime.Sp (ZMod 3)) (hj : Function.Injective j)
    (hfusion : ∃ g : OddPrime.Sp (ZMod 3),
      g * j planeInvolution * g⁻¹ = j swap) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨s,hs⟩ := exists_wreath_lift f.toMonoidHom f.surjective f.ker_le_center hk j hfusion
  let e : Wreath ≃* j.range := MonoidHom.ofInjective hj
  let t : j.range →* E := s.comp e.symm.toMonoidHom
  have ht : f.toMonoidHom.comp t = j.range.subtype := by
    apply MonoidHom.ext
    intro x
    change f.toMonoidHom (s (e.symm x)) = x.val
    rw [show f.toMonoidHom (s (e.symm x)) = j (e.symm x) from
      DFunLike.congr_fun hs (e.symm x)]
    exact congrArg Subtype.val (e.apply_symm_apply x)
  apply PerfectCentralCovering.not_dvd_card_kernel_of_section f j.range _ t ht
  rw [wreath_range_index j hj]
  decide

/-- Two does not divide the kernel of any finite perfect central cover of
Sp₄(3), with its literal symplectic matrix carrier. -/
theorem not_two_dvd_kernel
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3))) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  apply not_two_dvd_kernel_of_twoGroup_case (G := OddPrime.Sp (ZMod 3)) ?_ f
  intro D _ _ g hg
  exact not_two_dvd_kernel_of_wreath_of_isPGroup g hg matrixWreath
    matrixWreath_injective matrixWreath_fusion

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
