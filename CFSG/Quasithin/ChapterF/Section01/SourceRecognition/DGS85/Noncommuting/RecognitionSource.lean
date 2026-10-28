module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.Parameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Centers

/-!
# Recognized noncommuting sections on the reduced F1.11 graph

The original reduced graph supplies the two critical centralizer intersections,
core centralization and elementary centers. Odd local indices give opposite
center placement and fixed generation on the same section. Corrected quadratic
recognition then produces actual SL₂ coordinates with equal field orders.
The opposite-center products are Sylows of the full vertex stabilizers.
They give the radius-two escape in both orientations via (7.2).

The local actors/models and faithful sections with vanishing O²-fixed space
remain explicit earlier-source inputs. The section kernel is literally
Ω₁(Z(L)), and the acting quotient is literally L/O₂(G_delta). No local kernel
is identified with the two-core. Final source assembly must discharge those
inputs; the later epsilon-two distance exclusion remains with Chapter 7.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126--127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Actual reduced-source application of both corrected module bounds and recognition. -/
theorem reduced_sections_recognized (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w))
    [((Q F v).subgroupOf c₀.Pstar).Normal]
    [((Q F w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v) (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w) (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))))
    (M₀ : BinaryRankOneModel (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
    (M₁ : BinaryRankOneModel (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
    (∀ (T₀ : Sylow 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
      (T₁ : Sylow 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)),
      Nat.card (omegaCenterIn (T₀ : Subgroup (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))) =
        Nat.card (omegaCenterIn (T₁ : Subgroup (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)))) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) ∧
    (2 < b F → (¬ V F v 2 ≤ stabilizer F w) ∧ (¬ V F w 2 ≤ stabilizer F v)) := by
  let ht := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  have hgen : F false ⊔ F true = ⊤ := ht.generate
  have hi := reduced_noncommuting_critical_intersections h hc hne
  have h₁₀ : Z F w ≤ c₀.Pstar := local_twoGroup_le_star c₀ ho₀ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F hgen hc).1
  have h₀₁ : Z F v ≤ c₁.Pstar := local_twoGroup_le_star c₁ ho₁ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F hgen hi.1).1
  let : (((stabilizer F v).pCoreIn 2).subgroupOf c₀.Pstar).Normal :=
    inferInstanceAs (((Q F v).subgroupOf c₀.Pstar).Normal)
  let : (((stabilizer F w).pCoreIn 2).subgroupOf c₁.Pstar).Normal :=
    inferInstanceAs (((Q F w).subgroupOf c₁.Pstar).Normal)
  have hh := source_sections_recognized (stabilizer F v) (stabilizer F w)
    c₀.Pstar c₁.Pstar (Z F v) (Z F w) σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
    (local_center_span _ _ c₀ ho₀) (local_center_span _ _ c₁ ho₁)
    c₀.Pstar_le c₁.Pstar_le h₁₀ h₀₁ (source_core_le_star c₀) (source_core_le_star c₁)
    (graph_Q_centralizes_Z ht v) (graph_Q_centralizes_Z ht w) hi.2.1 hi.2.2 hne
  have hs₀ := sylow_in_overgroup_of_odd_relIndex _ _ _ c₀.Pstar_le hh.2.1 ho₀
  have hs₁ := sylow_in_overgroup_of_odd_relIndex _ _ _ c₁.Pstar_le hh.2.2 ho₁
  refine ⟨hh.1,hh.1.sylow_omega_card_eq,hs₀,hs₁,?_⟩
  intro hb
  exact ⟨graph_radius_two_escape_of_maximal_edges ht (reduced_kernel_sylow h) hc hne hb hs₁
      (fun _ he => graph_edge_isCoatom ht he),
    graph_radius_two_escape_of_maximal_edges ht (reduced_kernel_sylow h) hi.1
      (by rwa [commutator_comm]) hb hs₀ (fun _ he => graph_edge_isCoatom ht he)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
