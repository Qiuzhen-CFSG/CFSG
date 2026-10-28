module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Orders
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Lifting
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Fusion
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.InnerFusion
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.OuterFusion

/-!
# The two J₂ Sylow geometries in 16.3.4

The full model equivalences prove both strict order comparisons. The chosen
J₂ Sylow has exactly the central involution line as its center. The proved
inner and outer component-fusion calculations pass through actual fixed-subgroup
and ambient subgroup maps, producing the whole-center equality for every V.

The sole earlier-source input retained by `j2_sylowModels` is the outer
fixed-subgroup identification from 16.1.5(8). No center, fusion or embedding
assertion is assumed. `j2_sylowModels_of_1615` accepts the existing full
16.1.5(8) specification; its source owner must establish that table.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195,
with 16.1.5(8) and the component pairs of 16.1.7(f),(g), printed p.1172.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup ClassificationModels
open OtherPreliminaries.JankoTwoHigmanSims
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t i : G} {L K : Subgroup G}

/-- The remaining intrinsic fusion premise yields both exact requested contracts. -/
theorem j2_sylowModels_of_component_fusion
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.j2.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2)
    (fusion : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf r = 2 → J2ComponentInvolutionFusion r) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K := by
  refine ⟨?_, j2_sylowOrderGap eK hL⟩
  exact j2_involutionCenterLifting_of_element_fusion eK
    (h.componentL.1.trans inf_le_left) (j2_element_fusion_of_component_fusion h eK fusion)

/-- Both J₂ component alternatives have the required entire Sylow centers and
strict Sylow-order gap, using only the exact earlier outer-centralizer clause. -/
theorem j2_sylowModels
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.j2.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2)
    (outer_1615 : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf r = 2 → (¬ ∃ g, r = MulAut.conj g) →
        Nonempty (r.fixedSubgroup ≃*
          MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K := by
  apply j2_sylowModels_of_component_fusion h eK hL
  intro r hr
  by_cases hi : ∃ g, r = MulAut.conj g
  · exact j2_inner_component_involution_fusion r hr hi
  · exact j2_outer_component_involution_fusion r hr hi (outer_1615 r hr hi)

/-- The existing full 16.1.5(8) specification supplies the sole earlier-source
input to the J₂ model calculation. This does not assert that earlier table. -/
theorem j2_sylowModels_of_1615
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.j2.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2)
    (table_1615 : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf r = 2 → J2InvolutionAlternative r) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K := by
  apply j2_sylowModels h eK hL
  intro r hr ho
  rcases table_1615 r hr with ⟨hi, _⟩ | ⟨_, model⟩
  · exact (ho hi).elim
  · exact model

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
