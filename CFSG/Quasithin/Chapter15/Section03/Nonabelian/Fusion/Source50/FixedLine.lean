module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Centralizer

/-!
# The distinguished line is fixed by the original Sylow group

The earlier commutator bound [ZS,T]≤Z says exactly that T fixes ZS/Z
under the actual quotient action. This supplies the uniform fixed-line
field of the final fusion consumer for any subsequently chosen t in T.

Source: Aschbacher–Smith, the fixed-plane notation preceding 15.3.5 and
15.3.56(7), printed pp.1121,1148.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Core.ResidualGeneration
variable {G : Type*} [Group G] {T Z ZS : Subgroup G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

theorem quotient_fixed_line_of_commutator
    (hc : ⁅ZS,T⁆ ≤ Z) (t : centralizerH Z) (ht : (t : G) ∈ T)
    (x : closureU Z ZS) (hx : (x : G) ∈ ZS) :
    quotientAction Z ZS t (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x := by
  have hmem : closureCommutator t x ∈ Z.subgroupOf (closureU Z ZS) := by
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator ht hx
  have hq := (QuotientGroup.eq_one_iff (N := Z.subgroupOf (closureU Z ZS))
    (closureCommutator t x)).mpr hmem
  change QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) (closureCommutator t x) = 1 at hq
  rw [quotient_closureCommutator] at hq
  exact mul_inv_eq_one.mp hq

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
