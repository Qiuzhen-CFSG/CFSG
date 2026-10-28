module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalBoundSource

/-!
# Constructed critical endpoint modules on the reduced source graph

Construct the literal nonzero Z/Ω₁(Z(L)) section, its original quotient
coordinates, fixed-space generation and faithful Sylow action. Apply the
two-sided quadratic estimates to these constructed modules. This gives
actual linear model isomorphisms for both local two-core quotients and
equality of the two opposite-center image orders.

Only the actual local actors and their odd indices remain explicit here;
no representation, faithful action, residual fixed space, selected model
or numerical estimate is an input. Natural-module coordinates, equality
of defining field orders and their application to the distance theorem
remain with the Chapter 7 owner. This does not yet assert the unconditional
b=1 or b=2 conclusion.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126–127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The original reduced source supplies the actual nonzero section and its Sylow action. -/
theorem reduced_endpoint_section_exists (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E : Subgroup (G₀ L₀ S₀)) (c : LocalRankOneData (stabilizer F v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v)) :
    letI : ((Q F v).subgroupOf c.Pstar).Normal := graph_local_core_normal v c
    let A := Z F v
    let C := Stellmacher.omegaOneCenterAmbient c.Pstar
    letI : IsElementaryAbelian 2 A := graph_Z_elementary (reduced_triple h) v
    ∃ (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q F v).subgroupOf c.Pstar)
      (Additive (A ⧸ C.subgroupOf A)))
      (s : BinaryConjugationSection c.Pstar A C
        (σ.comp (QuotientGroup.mk' ((Q F v).subgroupOf c.Pstar)))),
      (∀ z : A, (s.coordinates z).toAdd =
        Additive.ofMul (QuotientGroup.mk' (C.subgroupOf A) z)) ∧
      Nontrivial (Additive (A ⧸ C.subgroupOf A)) ∧
      (∀ T : Sylow 2 c.Pstar, GeneratedByFixedSpace σ
        ((T : Subgroup c.Pstar).map (QuotientGroup.mk' ((Q F v).subgroupOf c.Pstar))) ∧
        Disjoint σ.ker ((T : Subgroup c.Pstar).map
          (QuotientGroup.mk' ((Q F v).subgroupOf c.Pstar)))) := by
  dsimp only [reducedFamily] at *
  let ht := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let := graph_local_core_normal v c
  let : ((Q F v).subgroupOf c.Pstar).Normal := graph_local_core_normal v c
  let := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  obtain ⟨σ,s,hcoords,hgen⟩ := graph_endpoint_section_exists ht v E c hodd
  have hplacement : Z F w ≤ c.Pstar := local_twoGroup_le_star c hodd _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F ht.generate hc).1
  have hnontrivial : Nontrivial (Additive (Z F v ⧸
      (Stellmacher.omegaOneCenterAmbient c.Pstar).subgroupOf (Z F v))) := by
    classical
    by_contra hn
    have hsub : Subsingleton (Additive (Z F v ⧸
        (Stellmacher.omegaOneCenterAmbient c.Pstar).subgroupOf (Z F v))) :=
      not_nontrivial_iff_subsingleton.mp hn
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    have hzC := (s.coordinates_eq_one_iff ⟨z,hz⟩).mp
      (Multiplicative.toAdd.injective (@Subsingleton.elim _ hsub _ _))
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzC |>.2.2 x (hplacement hx)
  exact ⟨σ,s,hcoords,hnontrivial,fun T => ⟨hgen T,
    graph_critical_endpoint_section_sylow_kernel ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hc E c hodd σ s T⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Apply reciprocal recognition to constructed modules at both actual critical endpoints. -/
theorem reduced_critical_quotients_linear_and_indices (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w)) :
    letI : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
    letI : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) 2 (2^n)) ∧
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) 2 (2^n)) ∧
    Nat.card (((Z F w).subgroupOf c₀.Pstar).map
      (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))) =
    Nat.card (((Z F v).subgroupOf c₁.Pstar).map
      (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))) := by
  dsimp only [reducedFamily] at *
  let ht := reduced_triple h
  let := graph_local_core_normal v c₀
  let := graph_local_core_normal w c₁
  let : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  let := graph_Z_elementary ht v
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  obtain ⟨σ₀,d₀,_⟩ := reduced_endpoint_section_exists h hc hne E₀ c₀ ho₀
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨σ₁,d₁,_⟩ := reduced_endpoint_section_exists h hc' (by rwa [commutator_comm]) E₁ c₁ ho₁
  have hr := graph_endpoint_sections_linear_and_sharp ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc hne E₀ E₁ c₀ c₁ ho₀ ho₁ σ₀ σ₁ d₀ d₁
  exact ⟨hr.1,hr.2.1,hr.2.2.2.2.1⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
