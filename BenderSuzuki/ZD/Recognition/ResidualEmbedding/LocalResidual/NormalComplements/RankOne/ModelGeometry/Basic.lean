module

public import BenderSuzuki.SE.Models
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Subgroups in the Section 16 model geometry

The two-point subgroup uses right conjugation, `B ∩ t⁻¹Bt`.
The generated subgroup uses the ambient image of the actual first omega
subgroup of the Sylow subgroup. These definitions carry no model conclusions.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2, and Chapter 2, Lemma 16.2.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open PFchapter1section1
variable {G : Type*} [Group G]

/-- The literal two-point Borel intersection. -/
@[expose] public def twoPoint (B : Subgroup G) (t : G) : Subgroup G :=
  B ⊓ rightConjugate B t

/-- The subgroup `⟨Ω₁(P),t⟩` in the original model, including central covers. -/
@[expose] public def rootGenerated (P : Subgroup G) (t : G) : Subgroup G :=
  omegaOneAmbient P ⊔ Subgroup.zpowers t

end BenderSuzuki.ZD.RankOneModelGeometry
