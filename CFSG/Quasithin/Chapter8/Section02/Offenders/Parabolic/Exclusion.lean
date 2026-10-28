module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.Actors
public import Theory.GroupTheory.TwoThreeCoreQuotient
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The terminal quotient obstruction for the two-core exclusion

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 8.2.2(1), printed pp.714–715 (PDF pp.731–732), combined
manuscript of 1 March 2004.

The source's D₈/3^(1+2) and SD₁₆/E₉ denote extensions, with the odd group
normal. If H/O₂(H) has a normal three-subgroup with quotient SD₁₆, that
subgroup is O₃(H/O₂(H)). Hence H/O₂,₃(H) has order sixteen. This contradicts
the earlier identification of the same quotient with D₈, of order eight.
The argument uses the actual two-core projection and requires no splitting.
The residual inclusion below also proves the passage from H ≤ C_G(z) to
O²(H) ≤ K_z, once A.3.18 identifies K_z = O^{3′}(C_G(z)) and the parabolic
quotient calculation gives the {2,3}-prime support of H.

This module does not yet prove the full exclusion V not ≤ O₂(H). The
exceptional branch must still verify 3.1.9 with LT as M₀, reconstruct the
parabolic quotient from its chief action, construct X = O²(H) in Ξ and
L_z ≤ K_z inside C_G(z), and apply the adequate intrinsic Ξ theorem with
its genuine Sylow hypothesis. Held must remain until the complete A.3.12
list excludes it. The source model arguments must construct the two
quotient identifications used below; they are not inferred from tags.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The actual embedded residual lies in the component once A.3.18 has
identified that component. The {2,3}-order premise is supplied by the
reconstructed parabolic quotient; H need not be normal in C_G(z). -/
theorem twoResidual_le_involution_component [Finite G]
    (H K : Subgroup G) (z : G) (hHC : H ≤ centralizer ({z} : Set G))
    (hH : IsPiGroup twoThreePrimes H)
    (hK : (primeToResidual 3 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = K) :
    (pResidual 2 H).map H.subtype ≤ K := by
  rw [twoResidual_eq_primeToResidual_three hH, ← hK]
  exact embedded_primeToResidual_mono 3 hHC

/-- The last contradiction in the exceptional Aut(M₂₂) branch. `N` is the
normal odd kernel in the source's extension SD₁₆/E₉; the proof needs only
that it is a three-group, so neither splitting nor an extra E₉ marking is
assumed. Both identifications concern the original H and its literal cores. -/
theorem incompatible_parabolic_quotients (H : Subgroup G)
    (hD : Nonempty
      (H ⧸ (pCore 3 (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≃*
        DihedralGroup 4))
    (N : Subgroup (H ⧸ pCore 2 H)) [N.Normal] (hN : IsPGroup 3 N)
    (hS : Nonempty ((H ⧸ pCore 2 H) ⧸ N ≃*
      Semidihedral.StandardModel 4 (by decide))) : False := by
  obtain ⟨d⟩ := hD
  obtain ⟨s⟩ := hS
  have hp : IsPGroup 2 (Semidihedral.StandardModel 4 (by decide)) :=
    IsPGroup.of_card (Semidihedral.standardModel_card 4 (by decide))
  let e := twoThreeCoreQuotientEquivOfExtension hp N hN s
  have hc := Nat.card_congr (d.symm.trans e).toEquiv
  rw [DihedralGroup.nat_card, Semidihedral.standardModel_card] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion
