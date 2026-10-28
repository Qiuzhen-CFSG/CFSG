module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The ordinary A₆ natural-section setup

These are the earlier action data preceding Notation 13.2.1: the actual
A₆ quotient of L, its compatible six-letter permutation action on LT,
and the natural binary section of V with its T-stable line. The line
subgroup is the full preimage in V of that one-dimensional subspace.

No order or flag position of L₁ is included. Its cubic two-core quotient
must be calculated from this action and the literal definition
L₁ = O²(N_LT(V₁)). The record only specifies the earlier natural action;
it is not a conclusion of 13.8.25.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§13.2, printed pp.876–877; application to 13.8.25, printed p.959.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

abbrev Natural := BinaryPermutation.natural (Fin 6)

variable {G : Type*} [Group G]

/-- The full preimage of a subspace in the actual natural section of V. -/
def sourceLinePreimage {V : Subgroup G} (f : V →* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) : Subgroup G :=
  ((P.toAddSubgroup.toSubgroup).comap f).map V.subtype

/-- The genuine ordinary natural action and its marked line, with no local
residual order or parabolic-position conclusion assumed. -/
structure NaturalSetup (L T V V₁ : Subgroup G) where
  model : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)
  normalizes_L : T ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ T ≤ normalizer (V : Set G)
  sylow : Sylow 2 (L ⊔ T : Subgroup G)
  sylow_eq : (sylow : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T)
  permutation : (L ⊔ T : Subgroup G) →* Equiv.Perm (Fin 6)
  model_compatible : ∀ l : L,
    permutation (inclusion le_sup_left l) = (model (QuotientGroup.mk' (pCore 2 L) l)).val
  naturalMap : V →* Multiplicative Natural
  naturalMap_surjective : Function.Surjective naturalMap
  naturalMap_kernel : naturalMap.ker = (centralizer (L : Set G)).comap V.subtype
  conjugation : ∀ (g : (L ⊔ T : Subgroup G)) (v : V),
    (naturalMap (V.normalizerMonoidHom ⟨g.val, normalizes_V g.property⟩ v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (permutation g) (naturalMap v).toAdd
  point : Submodule (ZMod 2) Natural
  point_dim : Module.finrank (ZMod 2) point = 1
  line_eq : V₁ = sourceLinePreimage naturalMap point
  line_stable : T ≤ normalizer (V₁ : Set G)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
