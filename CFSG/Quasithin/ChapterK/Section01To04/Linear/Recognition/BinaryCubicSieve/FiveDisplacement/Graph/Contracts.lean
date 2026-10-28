module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Branches
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Standard graph displacement obligations for binary SL₅

The graph involution is an actual operator on the original representation,
implementing inverse transpose on every marked group element. These two
contracts ask for nine independent moved dimensions, separating the local
endpoint support `{0,3}` from all other multiple supports. They impose no
absolute-irreducibility or degree assumption and assert no classification.

`Graph.Reduction` proves that an elementary outer actor has rank at most four,
and conjugates one of its involutions to this standard action without changing
its displacement. `Graph` therefore applies these contracts to the full actor's
common fixed space. The estimates themselves remain to be proved. The adjoint
example moves ten dimensions, so it is compatible with the bound requested here.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3A–3B), pp.27–28; Aschbacher–Smith K.3.2, printed pp.454–455.
The endpoint label is local root data; identifying its module with the adjoint
module, or using highest-weight comparisons in the other branch, requires proof.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- A literal involutory operator implementing inverse transpose on the marked SL₅. -/
@[expose] def IsStandardGraph (t : linearNormalizer σ) : Prop :=
  t ^ 2 = 1 ∧ ∀ g : SL5TenDimensional.Group,
    t.val * σ.asGroupHom g * t.val⁻¹ = σ.asGroupHom (graphSL 5 g)

/-- The endpoint-pair fixed-space obligation. This is a contract, not a proved estimate. -/
@[expose] def EndpointDisplacement : Prop :=
  ∀ v : V, v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ {0, 3} v →
    ∀ t : linearNormalizer σ, IsStandardGraph σ t →
      9 ≤ fixedCodim (normalizerRepresentation σ) (zpowers t)

/-- The remaining multiple-support fixed-space obligation, excluding the endpoint pair. -/
@[expose] def HigherDisplacement : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ J.card → J ≠ {0, 3} →
    ∀ t : linearNormalizer σ, IsStandardGraph σ t →
      9 ≤ fixedCodim (normalizerRepresentation σ) (zpowers t)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
