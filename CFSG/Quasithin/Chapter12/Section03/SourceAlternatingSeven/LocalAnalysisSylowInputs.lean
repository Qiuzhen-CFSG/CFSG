module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.GroupTheory.SolvableResidual

/-!
# Intermediate objects for the earlier A₇ Sylow-normalizer proof

The source uses C_L(e₂)^∞ and C_L(e₆)^∞, with quotient by O₂ followed by
the centre, and compares the actual ambient O^{3′}-centralizer residuals.
These definitions retain those embeddings and conventions. In particular,
the fixed subgroup is C_{Ω₁Z(T)}(L), not the fixed part of the chosen V.

`Points.Models` and `Points.AmbientResiduals` are separate, unproved input
contracts. Their producers and the escaping action on the Sylow centre
must all be supplied before the conditional assembly proves N(T) ≤ N(L).
The local model producer, ambient residual producer and centre-action
producer can work independently with these explicit interfaces.

Source: Aschbacher--Smith, 3.3.22, printed pp.597--598, as used by
3.3.1(1) and 12.3.5. This file asserts no instance of those source theorems.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace SylowNormalizer

/-- The terminal derived subgroup C_L(x)^∞, embedded in G. -/
def pointResidual (L : Subgroup G) (x : G) : Subgroup G :=
  (solvableResidual (L ⊓ centralizer ({x} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({x} : Set G)).subtype

/-- The prime-to-three residual O^{3′}(C_G(x)), embedded in G. -/
def pointThreeResidual (x : G) : Subgroup G :=
  (primeToResidual 3 (centralizer ({x} : Set G))).map
    (centralizer ({x} : Set G)).subtype

/-- The literal projection through O₂,Z(K), including the central-cover kernel. -/
def projection (K : Subgroup G) (e : CentralQuotient K ≃* alternatingGroup (Fin 6)) :
    K →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 K)))

/-- Central representatives of the weight-two and weight-six L-orbits. -/
structure Points (E : S.NaturalCoordinates) where
  two : V
  six : V
  two_weight : weight (E.coordinates two).toAdd.val = 2
  six_weight : weight (E.coordinates six).toAdd.val = 6
  two_central : (two : G) ∈ centralizer (T : Set G)
  six_central : (six : G) ∈ centralizer (T : Set G)

variable {E : S.NaturalCoordinates}
namespace Points
variable (P : Points E)
abbrev five : Subgroup G := pointResidual L P.two
abbrev sixGroup : Subgroup G := pointResidual L P.six
abbrev fixed (_P : Points E) : Subgroup G := omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)

/-- Local point-residual facts used by source 3.3.22. These are proof
obligations, not part of `Setup`. In `five_image` the inclusion is an explicit
input: the ambient residual argument proves it before applying this model fact. -/
structure Models where
  six_quotient : CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6)
  core_eq : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2
  five_le_three : P.five ≤ pointThreeResidual (P.two : G)
  five_image : ∀ (g : G), g ∈ normalizer (T : Set G) →
    g * (P.two : G) * g⁻¹ = P.six →
    P.five.map (MulAut.conj g).toMonoidHom ≤ P.sixGroup →
    Nonempty (((P.five.map (MulAut.conj g).toMonoidHom).subgroupOf P.sixGroup).map
      (projection P.sixGroup six_quotient) ≃* alternatingGroup (Fin 5))

/-- The two ambient identities (*) and (**) in source 3.3.22, p.597.
The nonidentity restriction in the second identity is essential. No ambient
centralizer bound, fusion statement, or normalizer conclusion is a field. -/
structure AmbientResiduals : Prop where
  six_residual : ∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup
  fixed_residual : ∀ c ∈ P.fixed, c ≠ 1 → pointThreeResidual c = L

end Points

end SylowNormalizer
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
