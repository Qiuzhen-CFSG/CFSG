module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointSource

/-!
# Natural critical endpoint sections with equal actual fields

Construct the nonzero literal Z/Ω₁(Z(L)) sections at both critical ends.
The sharp reciprocal estimates first recognize the actual quotients as
linear. The residual and faithfulness argument then discharges the remaining
hypotheses of corrected (5.12) on those same sections. Recognition supplies
literal equivariant natural coordinates over fields of equal order, equality
of the original Sylow-omega parameters, and both full-stabilizer Sylow products.
These products and natural centers feed both branches in `DistanceBoundSource`.

Only actual local rank-one actors and their odd indices remain inputs here.
Their source construction, the earlier local obstruction and the remaining
classification assembly are not asserted by this module.
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

/-- Recognition on any two actual nonzero endpoint sections, with the representation
premises discharged from the source critical pair. -/
theorem reduced_endpoint_sections_recognized (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w))
    [((Q F v).subgroupOf c₀.Pstar).Normal]
    [((Q F w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [Nontrivial W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁] [Nontrivial W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v) (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w) (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar)))) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
    (∀ (T₀ : Sylow 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
      (T₁ : Sylow 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)),
      Nat.card (omegaCenterIn (T₀ : Subgroup (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))) =
        Nat.card (omegaCenterIn (T₁ : Subgroup (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)))) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) ∧
    (2 < b F → (¬ V F v 2 ≤ stabilizer F w) ∧ (¬ V F w 2 ≤ stabilizer F v)) := by
  dsimp only [reducedFamily] at *
  let ht := reduced_triple h
  let := graph_local_core_normal v c₀
  let := graph_local_core_normal w c₁
  have hi := graph_endpoint_sections_linear_and_sharp ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc hne E₀ E₁ c₀ c₁ ho₀ ho₁ σ₀ σ₁ d₀ d₁
  obtain ⟨n₀,hn₀,hm₀⟩ := hi.1
  obtain ⟨n₁,hn₁,hm₁⟩ := hi.2.1
  obtain ⟨⟨M₀⟩,hf₀,hr₀⟩ := graph_endpoint_linear_recognition_inputs ht v E₀ c₀ ho₀ σ₀ d₀ hn₀ hm₀
  obtain ⟨⟨M₁⟩,hf₁,hr₁⟩ := graph_endpoint_linear_recognition_inputs ht w E₁ c₁ ho₁ σ₁ d₁ hn₁ hm₁
  exact reduced_sections_recognized h hc hne E₀ E₁ c₀ c₁ ho₀ ho₁
    σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁

/-- Construct both literal quotient sections and their equal-field natural coordinates. -/
theorem reduced_natural_endpoint_sections_exists (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w)) :
    letI : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
    letI : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
    let C₀ := Stellmacher.omegaOneCenterAmbient c₀.Pstar
    let C₁ := Stellmacher.omegaOneCenterAmbient c₁.Pstar
    letI : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary (reduced_triple h) v
    letI : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary (reduced_triple h) w
    ∃ (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)
        (Additive (Z F v ⧸ C₀.subgroupOf (Z F v))))
      (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)
        (Additive (Z F w ⧸ C₁.subgroupOf (Z F w))))
      (s₀ : BinaryConjugationSection c₀.Pstar (Z F v) C₀
        (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
      (s₁ : BinaryConjugationSection c₁.Pstar (Z F w) C₁
        (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar)))),
      (∀ z : Z F v, (s₀.coordinates z).toAdd =
        Additive.ofMul (QuotientGroup.mk' (C₀.subgroupOf (Z F v)) z)) ∧
      (∀ z : Z F w, (s₁.coordinates z).toAdd =
        Additive.ofMul (QuotientGroup.mk' (C₁.subgroupOf (Z F w)) z)) ∧
      EqualFieldNaturalSections σ₀ σ₁ ∧
      Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
      Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
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
  obtain ⟨σ₀,s₀,hcoord₀,hn₀,_⟩ := reduced_endpoint_section_exists h hc hne E₀ c₀ ho₀
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨σ₁,s₁,hcoord₁,hn₁,_⟩ := reduced_endpoint_section_exists h hc'
    (by rwa [commutator_comm]) E₁ c₁ ho₁
  let := hn₀
  let := hn₁
  have hr := reduced_endpoint_sections_recognized h hc hne E₀ E₁ c₀ c₁ ho₀ ho₁ σ₀ σ₁ s₀ s₁
  exact ⟨σ₀,σ₁,s₀,s₁,hcoord₀,hcoord₁,hr.1,hr.2.2.1,hr.2.2.2.1⟩

/-- The constructed natural centers and Sylow products needed by both distance branches. -/
theorem reduced_critical_natural_centers_and_products (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w)) :
    HasNaturalCenter c₀.Pstar (Z F v) (Q F v) ∧
    HasNaturalCenter c₁.Pstar (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  let := graph_local_core_normal v c₀
  let := graph_local_core_normal w c₁
  let : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  let := graph_Z_elementary (reduced_triple h) v
  let := graph_Z_elementary (reduced_triple h) w
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary (reduced_triple h) v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary (reduced_triple h) w
  obtain ⟨σ₀,σ₁,s₀,s₁,_,_,hn,hs₀,hs₁⟩ :=
    reduced_natural_endpoint_sections_exists h hc hne E₀ E₁ c₀ c₁ ho₀ ho₁
  have hc := hn.hasNaturalCenters s₀ s₁
  exact ⟨hc.1,hc.2,hs₀,hs₁⟩

/-- Use the same edge-local actors at both critical ends; no module data are supplied. -/
theorem reduced_critical_natural_centers_of_localData (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    HasNaturalCenter (L v) (Z F v) (Q F v) ∧
    HasNaturalCenter (L w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  let ht := reduced_triple h
  have hvw : v ≠ w := by
    intro he
    have hd := hc.1
    have hp : 0 < b F := source_b_positive ht
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨u,hvu,_⟩ := exists_predecessor F ht.generate w v hvw.symm
  obtain ⟨t,hwt,_⟩ := exists_predecessor F ht.generate v w hvw
  have hr := reduced_critical_natural_centers_and_products h hc hne _ _
    (d v u hvu) (d w t hwt)
    (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hodd w)
  simpa only [hstar] using hr

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
