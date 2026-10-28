module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.Representation.PSL3Two.SmallModules


/-!
# The recognized natural and contragredient action used by 15.3.59

This input is the action clause of 15.3.58, with an actual equivalence of
H/O₂(H) and Aut(SL₃(2)), and equivariant coordinates on the literal U/Z.
The coordinates identify the inner action with the concrete natural and
contragredient representations. The source element t exchanges the two
summands and remains outside U C_T(V). Over F₂ the additive equivalence
underlying these coordinates is automatically linear.

This is an earlier-source input, not a recognition theorem. It includes
none of the residual generation, Sylow size, or transfer conclusions.
The earlier marked X-action of 15.3.56 must also be retained when using
this interface to prove the partner calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58(1,3), printed pp.1148–1149.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

/-- The concrete binary natural three-space plus its actual linear dual. -/
abbrev NaturalDualSpace := BinaryLinearThree.Vector ×
  Module.Dual (ZMod 2) BinaryLinearThree.Vector

variable {G : Type*} [Group G]

/-- Literal group and module identifications, retaining the source summand swap. -/
structure RecognizedAction (T Z ZS V : Subgroup G) (t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] where
  actorEquiv : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL
  coordinates : VectorQuotient Z ZS ≃* Multiplicative NaturalDualSpace
  equivariant : ∀ (h : centralizerH Z) (g : Matrix.PSL3Two.SL),
    actorEquiv (QuotientGroup.mk' _ h) = MulAut.conj g →
    ∀ w : VectorQuotient Z ZS,
      (coordinates (quotientAction Z ZS h w)).toAdd =
        (BinaryLinearThree.W g (coordinates w).toAdd.1,
          BinaryLinearThree.W.dual g (coordinates w).toAdd.2)
  t_mem : t ∈ T
  t_mem_H : t ∈ centralizerH Z
  t_outside : t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))
  swaps_natural : ∀ v : BinaryLinearThree.Vector,
    (coordinates (quotientAction Z ZS ⟨t, t_mem_H⟩
      (coordinates.symm (Multiplicative.ofAdd (v, 0))))).toAdd.1 = 0
  swaps_dual : ∀ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector,
    (coordinates (quotientAction Z ZS ⟨t, t_mem_H⟩
      (coordinates.symm (Multiplicative.ofAdd (0, f))))).toAdd.2 = 0

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
