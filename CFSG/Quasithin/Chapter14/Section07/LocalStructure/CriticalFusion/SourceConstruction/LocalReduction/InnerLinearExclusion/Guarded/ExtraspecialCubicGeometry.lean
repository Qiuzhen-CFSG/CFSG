module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicGeometry
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicLocalStructure

/-!
# Same-group structural-input version

This proof uses only `Structural1222At` and `Theorem12213At` at the original G,T.
It preserves the literal groups and quotient maps of the source argument below.

# The action kernel of the original cubic completion

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the Sylow-central seed makes the
literal conjugation quotient D/C_D(W) two-reduced. In the normal-point
branch, the plane-span obstruction shows that Y's image does not normalize
L₂'s image under the actual quotient map.

Both local residuals act nontrivially on W. The Goldschmidt intersection
lemma then gives C_T(W) = O₂(D). The application constructs this geometry
from the original order-four chief interval, retaining its escaping cubic,
normalization of L₁, and exact star kernel.

These are the initial geometric and kernel steps of the containment
argument. Solvability of D and the later exclusions proving 14.5.3(2)
remain necessary; the small interval is not excluded here.

Source: Aschbacher–Smith, 14.5.6 and 14.5.7(2--3), printed p.1014,
B.2.14, printed p.78, and 14.7.20(2), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point span has two-reduced conjugation action in the generated
local group, as required by source 14.5.7(3). -/
theorem cubic_generated_span_reduced
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Theory.GroupTheory.IsPReduced 2 ((conjugateSpanBy (F.Vi 1) D).subgroupOf D) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hh := (cubic_generated_local_structure h hab structural previous Y hYH he).1
  apply Theory.GroupTheory.reduced_conjugateSpan_of_sylow_central T
  · exact le_sup_right.trans le_sup_right
  · exact (F.le_seed 1).trans h.chosen.le_sylow
  · exact le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  · exact (Theory.GroupTheory.inf_centralizer_pCoreIn_le_iff 2 _).mp hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
