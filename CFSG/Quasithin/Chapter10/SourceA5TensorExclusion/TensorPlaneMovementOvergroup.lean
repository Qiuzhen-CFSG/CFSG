module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPlaneMovement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFF

/-!
# Original Cartan movement in the tensor overgroup argument

An actual order-three subgroup of the old residual, contained in the
original tensor local orbit, moves V₂. Substituting this proved movement
and the original two-core centralization gives the common-component
product and the FF conclusion for the literal overgroup and its action.
The Cartan existence, line centralization and earlier local hypotheses
remain explicit for their source producers.

Source: Aschbacher–Smith9.3.5–9.3.7, printed pp.733–734.
-/

public section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Source 9.3.5 supplies the common-component product for the actual old residual. -/
theorem old_residual_component_product_of_cartan
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (oldH H B : Subgroup G)
    (hBK : B ≤ (pResidual 2 oldH).map oldH.subtype)
    (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3)
    (hcore : pCore 2 H ≠ ⊥)
    (hgen : H = (L ⊔ (pResidual 2 oldH).map oldH.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hout : ¬ H ≤ D.maximalLocal)
    (hK : (pResidual 2 oldH).map oldH.subtype ∈
      Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 oldH).map oldH.subtype ≤ centralizer (m.tensorLine : Set G)) :
    (pResidual 2 H).IsCComponent ∧ L.subgroupOf H ≤ pResidual 2 H ∧
      ((pResidual 2 oldH).map oldH.subtype).subgroupOf H ≤ pResidual 2 H ∧
      ∀ g : H, ∃ k ∈ pResidual 2 H,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r = g :=
  source_a5_tensor_pair_component_product D e hn H ((pResidual 2 oldH).map oldH.subtype)
    m.tensorLine hcore hgen hout hK m.component_core_centralizes_tensorPlane hKU
      (m.old_residual_moves_tensorPlane_of_cartan oldH B hBK hBL hB)

open ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction Representation.BinaryOffender

/-- The original Cartan supplies movement in the actual overgroup FF action. -/
theorem old_residual_overgroup_ff_of_cartan
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (oldH H B A : Subgroup G)
    (hBK : B ≤ (pResidual 2 oldH).map oldH.subtype)
    (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3)
    (hcore : pCore 2 H ≠ ⊥)
    (hgen : H = (L ⊔ (pResidual 2 oldH).map oldH.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hout : ¬ H ≤ D.maximalLocal)
    (hK : (pResidual 2 oldH).map oldH.subtype ∈
      Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 oldH).map oldH.subtype ≤ centralizer (m.tensorLine : Set G))
    (hUH : m.tensorLine ≤ H)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hOmega : omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ m.tensorLine)
    (hAH : A ≤ H) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ m.tensorLine → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = m.tensorLine)
    (hcomm : (pResidual 2 oldH).map oldH.subtype =
      ⁅(pResidual 2 oldH).map oldH.subtype,elementaryAbelianMaxJ
        ((T : Subgroup G) ⊓ normalizer (L : Set G))⁆) :
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf H ≤ W ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 H).map (actionMk W)).subgroupOf N)) :=
  source_a5_tensor_overgroup_ff D e hn H ((pResidual 2 oldH).map oldH.subtype)
    m.tensorLine A hcore hgen hout hK m.component_core_centralizes_tensorPlane hKU
    (m.old_residual_moves_tensorPlane_of_cartan oldH B hBK hBL hB)
    hUH hchar hOmega hAH hAU hirr hcomm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
