module

public import Stellmacher.TwoResidualIdentification
public import BenderSuzuki.External.Huppert.IV.ResidualCommutator

/-!
# Idempotence of the ambient two-residual action

A finite two-subgroup `M` normalized by `P` satisfies
`[[M,O²(P)],O²(P)] = [M,O²(P)]`, where the residual is viewed in the common
ambient group. No containment `M ≤ P` is needed.

Convert the index-based internal residual to Huppert's quotient-based residual,
then apply the generic theorem for residual actions on p-subgroups. This is the
commutator reduction used in Stellmacher (1997), (9.1), relation (3).
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher
open BenderSuzuki.External

public theorem commutator_twoResidualAmbient_idempotent
    {G : Type*} [Group G] [Finite G]
    (M P : Subgroup G) (hM : IsPGroup 2 M) (hPM : P ≤ normalizer M) :
    ⁅⁅M,twoResidualAmbient P⁆,twoResidualAmbient P⁆ = ⁅M,twoResidualAmbient P⁆ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [twoResidualAmbient, SectionThree.twoResidualSubgroup_eq_hktPResidual']
  exact commutator_map_pResidual_idempotent_of_isPGroup 2 M P hM hPM

end Stellmacher
