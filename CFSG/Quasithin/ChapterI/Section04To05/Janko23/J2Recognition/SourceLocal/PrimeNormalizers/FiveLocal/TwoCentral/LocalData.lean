module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation

/-!
# The marked local calculation for the two-central five-subgroup

These are intermediate conclusions in the middle paragraph of Aschbacher,
*Sporadic Groups* (1994), 47.2, printed p.261. They describe the literal
intersections with C_G(z), together with the two independent inversion
actions on the factors of P. No ambient normalizer isomorphism, normal odd
complement, or self-centralization conclusion is a field.

The source producer must use Y = P ∩ E(C_G(E)) and the inverter and
extraspecial complement supplied by `RootFiveWitness`. A separate
odd-complement argument can use these local identities to identify N_G(Y).
Both steps remain proof obligations of the two-central assembly.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral

variable {G : Type*} [Group G]

/-- The local product and actions, before the normal odd-complement argument. -/
structure LocalData (E Y : Subgroup G) (P : Sylow 5 G) (z : G) where
  card_E : Nat.card E = 5
  card_Y : Nat.card Y = 5
  product : E ⊔ Y = (P : Subgroup G)
  disjoint : Disjoint E Y
  involution_z : orderOf z = 2
  centralizes_Y : Y ≤ involutionCentralizer z
  inverts_E : ∀ x ∈ E, z * x * z⁻¹ = x⁻¹
  t : G
  involution_t : orderOf t = 2
  commutes : Commute z t
  centralizes_E : E ≤ involutionCentralizer t
  inverts_Y : ∀ x ∈ Y, t * x * t⁻¹ = x⁻¹
  local_centralizer : involutionCentralizer z ⊓ centralizer (Y : Set G) =
    Y ⊔ zpowers z
  local_normalizer : involutionCentralizer z ⊓ normalizer (Y : Set G) =
    Y ⊔ (zpowers z ⊔ zpowers t)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral
