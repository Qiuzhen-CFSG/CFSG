module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFF
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupTensor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentTensor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentLocal

/-!
# The original old residual in the tensor FF overgroup

This application preserves the original H-star residual and original tensor
line. The original cubic actor supplies irreducibility and the trivial center;
the proved non-FF action supplies the Thompson commutator identity. All tensor
cardinality, central-involution, orbit-centralizer and old-core-containment
premises of the structural steps are discharged here.

The remaining hypotheses are the source 9.2.7 old A₅ marking, the larger-Omega
commutator bound, source 9.3.1 line centralization, source 9.3.2 Sylow placement,
source 9.3.3 nonzero overgroup core, and source 9.3.5 plane movement.
Source: Aschbacher–Smith, 9.3.6–9.3.7, printed pp.733–734.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_overgroup_core_and_ff
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ A : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hAH : A ≤ M₀) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N)) := by
  have hK := m.old_residual_mem_local_at_stabilizer hn hH eK hSyl
  have hout : ¬ M₀ ≤ D.maximalLocal := by
    intro hm
    exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH ((hgen ▸ (show (pResidual 2 H).map H.subtype ≤
      (L ⊔ (pResidual 2 H).map H.subtype) ⊔
        ((T : Subgroup G) ⊓ normalizer (L : Set G)) from
      le_sup_of_le_left le_sup_right)).trans hm)
  have hLH : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ M₀ := hgen ▸ le_sup_right
  obtain ⟨hU,hHe,hF,hZ⟩ := m.outside_core_and_center_of_original_tensor_cubic
    hn houtside hcomm M₀ A hcore hLH hRH hout hAH hAU d hdA hd3 hdC
  refine ⟨hU,hHe,hF,hZ,?_⟩
  apply source_a5_tensor_overgroup_ff D e hn M₀ ((pResidual 2 H).map H.subtype)
    m.tensorLine A hcore hgen hout hK m.component_core_centralizes_tensorPlane
    hKU hmove (hU.trans (map_subtype_le _)) (Chapter1.mem_He_iff.mp hHe)
    (m.omegaCenter_stabilizer_le_tensorLine hn houtside hcomm) hAH hAU
    (m.tensorLine_cartan_irreducible A hAU d hdA hd3 hdC)
  rw [m.thompson_stabilizer_eq]
  exact m.old_residual_eq_thompson_commutator hH eK
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
