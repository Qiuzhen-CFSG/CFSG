module

public import Stellmacher.Recognition.Parrott.AmbientOrder

/-!
# Recognition of the Tits group from Parrott's centralizer hypotheses

A finite nonsolvable simple N₂-group satisfying Parrott's original
involution-centralizer hypotheses is isomorphic to the actual ten-generator,
37-relator model of the Tits group.

The compatible local generators realize the full presentation and generate
the ambient group. The resulting homomorphism is injective by the certified
simplicity of the presented model and the nontrivial image of the distinguished
involution word. The bijective lift supplied by `AmbientOrder` therefore gives
the required multiplicative equivalence, with its direction reversed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§5, p.683, and §6, p.684.
-/

namespace Stellmacher.Recognition

/-- Parrott's original centralizer hypotheses recognize the actual Tits model
in a finite nonsolvable simple N₂-group. -/
public theorem nonempty_equiv_tits_of_parrott
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    {z : G} (h : ParrottCentralizerHypotheses z) :
    Nonempty (G ≃* Tits.ParrottGroup) := by
  obtain ⟨g, hrels, _, hbij⟩ := parrott_exists_bijective_lift hns hN h
  exact ⟨(MulEquiv.ofBijective (Tits.parrottLift g hrels) hbij).symm⟩

end Stellmacher.Recognition
