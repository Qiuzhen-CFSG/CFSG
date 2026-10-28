module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.NormalAction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement

/-!
# The kernel-to-partner bridge for the equality row

In the equality row the full normalizer action on the cubic section is already
known to have a dihedral image of order eight, hence a kernel of index prime to
three containing `O^{3'}(Mc)`.  The remaining source step only needs the
prime-to-three residual of that kernel to lie in the embedded residual.  This
file records both that exact conditional consumer and the stronger sufficient
full-kernel variant.  It does not identify the kernel; the source
action/centralizer argument remains its owner.

Source: Aschbacher--Smith 15.2.12(4), printed p.1111.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- A stronger sufficient source bridge: if the full action kernel on
`K/O₂(K)` is contained in `K`, then the equality row identifies `Kc` with
the literal `O^{3'}` residual of `Mc`. -/
theorem ResidualInput.residual_equality_of_eq_of_action_kernel_le
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H)
    (hker : (partnerQuotientAction H Mc he).ker ≤ (residual H).subgroupOf Mc) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  have hHM : H ≤ Mc :=
    (Section01.source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (Section03.InitialSource.centralizer_le_partner T h.partner)
  have hKM : residual H ≤ Mc := (map_subtype_le _).trans hHM
  have hleft : partnerSpan H Mc ≤ threePrimeResidual Mc :=
    partnerSpan_le_threePrimeResidual hHM d.quotient.some
  have hright : threePrimeResidual Mc ≤ residual H := by
    have hk := d.threePrimeResidual_le_action_kernel_of_eq he
    have hm := map_mono (f := Mc.subtype) hker
    rw [map_subgroupOf_eq_of_le hKM] at hm
    exact hk.trans hm
  apply le_antisymm hleft
  rw [he]
  exact hright

/-- The exact source-strength bridge: it is enough to contain the
prime-to-three residual of the action kernel, rather than the whole kernel. -/
theorem ResidualInput.residual_equality_of_eq_of_action_kernel_residual_le
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H)
    (hker : (primeToResidual 3 (partnerQuotientAction H Mc he).ker).map
      (partnerQuotientAction H Mc he).ker.subtype ≤ (residual H).subgroupOf Mc) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  have hHM : H ≤ Mc :=
    (Section01.source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (Section03.InitialSource.centralizer_le_partner T h.partner)
  have hKM : residual H ≤ Mc := (map_subtype_le _).trans hHM
  have hleft : partnerSpan H Mc ≤ threePrimeResidual Mc :=
    partnerSpan_le_threePrimeResidual hHM d.quotient.some
  have hres : primeToResidual 3 Mc ≤ (residual H).subgroupOf Mc := by
    rw [← embedded_primeToResidual_eq_of_normal 3
      (partnerQuotientAction H Mc he).ker
      (d.threeResidual_le_action_kernel_of_eq he)]
    exact hker
  have hright : threePrimeResidual Mc ≤ residual H := by
    rw [threePrimeResidual_eq]
    have hm := map_mono (f := Mc.subtype) hres
    simpa only [map_subgroupOf_eq_of_le hKM] using hm
  apply le_antisymm hleft
  rw [he]
  exact hright

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

