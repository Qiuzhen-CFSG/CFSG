module

public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# The dual natural cohomology of SL₃(2)

The graph automorphism interchanges the natural module and its dual.
Transporting first cohomology along that automorphism gives the dual bound
from the established natural-module computation. This bounds the kernel
of a perfect central cover in the L₃(2) block normalizer argument.

Source: Aschbacher–Smith C.1.7 and 3.3.25–31, pp.123,599–602.
-/

public noncomputable section
open Representation Representation.OneCohomology

namespace BinaryLinearThree

theorem natural_dual_H1_finrank : Module.finrank (ZMod 2) (H1 W.dual) = 1 := by
  let e := AutomorphismAction.graphNaturalDual.toLinearEquiv
  have he : ∀ g v, e (W g v) = W.dual (AutomorphismAction.graph g) (e v) := by
    intro g v
    have hh := AutomorphismAction.graphNaturalDual.toIntertwiningMap.isIntertwining _ _
      (AutomorphismAction.graph g) v
    change e (W (AutomorphismAction.graph (AutomorphismAction.graph g)) v) =
      W.dual (AutomorphismAction.graph g) (e v) at hh
    rwa [AutomorphismAction.graph_graph] at hh
  rw [← (H1Congr W W.dual AutomorphismAction.graph e he).finrank_eq]
  exact SLHigherNatural.finrank_H1_sl3_two
end BinaryLinearThree
