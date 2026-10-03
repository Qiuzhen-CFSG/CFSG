module

public import Stellmacher.SectionsOneToFourDefs


/-!
# Automorphism translates used in Stellmacher (2.5)

This module defines the subgroup of a Sylow 2-subgroup corresponding to
`V = ⟨Ω₁(Z(S))^G⟩` and its image in the ambient group after applying an
automorphism of `S`.  The latter is the formal version of the paper's notation
`V^τ` in result (2.5), at `refs/latex/stellmacher-n-group.tex`, lines 641–649.
The copy `pushingUpQ S` of the ambient two-core in the same Sylow subgroup
is the source `Q_α` used in the square-control and contained-orbit arguments
from *Pushing up* (1986), (3.2)--(3.5).

The definitions are separated from the quoted pushing-up theorem so that both
that theorem and the final (2.5) wrapper can use the same exposed objects without
an upward or cyclic import.
-/

namespace Stellmacher.SectionTwo

universe u

/-- The ambient two-core pulled back to the fixed Sylow subgroup. -/
@[expose] public noncomputable def pushingUpQ
    {G : Type u} [Group G] (S : Sylow 2 G) : Subgroup S :=
  (pCore 2 G).comap (S : Subgroup G).subtype

/-- The copy of `vSubgroup S` inside the abstract Sylow subgroup `S`. -/
@[expose] public noncomputable def vSubgroupInSylow
    {G : Type u} [Group G] (S : Sylow 2 G) : Subgroup S :=
  (vSubgroup S).comap (S : Subgroup G).subtype

/-- The ambient image of `V` after applying an automorphism `τ` of `S`. -/
@[expose] public noncomputable def automorphismTranslateV
    {G : Type u} [Group G] (S : Sylow 2 G)
    (τ : MulAut S) : Subgroup G :=
  ((vSubgroupInSylow S).map (τ : S →* S)).map (S : Subgroup G).subtype

end Stellmacher.SectionTwo
