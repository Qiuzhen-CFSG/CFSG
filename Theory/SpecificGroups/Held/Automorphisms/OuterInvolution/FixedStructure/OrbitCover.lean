module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.CentralKernel
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.Image
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.Kernel

/-!
# The actual central A7 quotient of the Held cover candidate

The action on the literal orbit of letter 30 is conjugate to the faithful
A7 action on two-subsets of seven letters. Its kernel consists precisely of
the powers of the checked central element of order three: graph signatures
show that a kernel element is determined by its image of zero, and the three
possible images are supplied by those powers.

Both conclusions are unconditional and independent of the order bound for
the full fixed subgroup. Combined with the published perfectness, these are
the central-cover inputs for GLS3 Table 5.3p, outer 2C row, interpreted by
the perfect-cover convention on pp.260–261. The fixed-subgroup index-two
assembly remains in the parent `FixedStructure` development.
-/

namespace Held.OuterInvolution.FixedStructure
open Subgroup

/-- The actual orbit image, identified through its action on pairs. -/
public noncomputable def orbitImage_equiv_alternatingGroup : orbitImage ≃* alternatingGroup (Fin 7) :=
  orbitImagePairEquiv.trans
    ((MulEquiv.subgroupCongr pairActionHom_range_eq).trans pairPermEquiv.symm)

/-- Every element of the actual orbit kernel is a power of the central word. -/
public theorem orbitKernel_le_centralZpowers : orbitKernel ≤ zpowers centralGenerator := by
  intro d hd
  rcases orbitKernel_zero_image d hd with h0 | h1 | h2
  · rw [orbitKernel_eq_one_of_fixes_zero d hd h0]
    exact (zpowers centralGenerator).one_mem
  · have he : d = centralGenerator := orbitKernel_eq_of_zero hd
      centralGenerator_mem_orbitKernel (h1.trans centralGenerator_zero.symm)
    rw [he]
    exact mem_zpowers _
  · have he : d = centralGenerator ^ 2 := orbitKernel_eq_of_zero hd
      (orbitKernel.pow_mem centralGenerator_mem_orbitKernel 2)
      (h2.trans centralGenerator_square_zero.symm)
    rw [he]
    exact npow_mem_zpowers _ _

/-- The full kernel is the central subgroup of order three. -/
public theorem orbitKernel_eq_centralZpowers_exact :
    orbitKernel = zpowers centralGenerator :=
  orbitKernel_eq_centralZpowers orbitKernel_le_centralZpowers

end Held.OuterInvolution.FixedStructure
