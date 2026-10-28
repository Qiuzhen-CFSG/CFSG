module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusTwoControl

/-!
# The reduced-source radius-two configuration

Corrected quadratic recognition supplies the two literal natural sections and
the full-vertex Sylow product. The original F1.11 reduction supplies the
kernel Sylows and the full edge two-core. If the epsilon-two distance is not
two, these facts construct the final two vertices of a critical geodesic,
place V_alpha^2 in Q_(alpha'-2), and prove that it escapes Q_(alpha'-1).
Its second commutator with V_(alpha'-1)^1 vanishes. Consequently its image
in the actual last odd actor quotient is nontrivial and quadratic on the
literal radius-one section.

The local models, faithful center sections and residual fixed-space inputs
remain earlier-source premises. The path and index arguments excluding the
long-distance branch are not asserted here.

Source: DGS, *Groups and Graphs* (1985), (7.5)(1)--(3), pp.129--130.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The reduced F1.11 graph supplies the kernel Sylows and full edge core;
recognition supplies natural coordinates and the full vertex Sylow product.
The contrary branch constructs the last two vertices, with core escape and
quadratic commutator control, rather than assuming such a configuration. -/
theorem reduced_epsilonTwo_radius_two_configuration
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x)
        (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤ normalizer
      ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w u : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hvu : (graph F).Adj v u)
    (hdu : (graph F).dist u w + 1 = b F)
    (hepsilon : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2))
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (h₀ : c₀.Pstar = L v) (h₁ : c₁.Pstar = L w)
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
      (b F = 2 ∨ (6 ≤ b F ∧ ∃ t y : Vertex F,
        (graph F).Adj w t ∧ (graph F).Adj t y ∧
        (graph F).dist v t + 1 = b F ∧
        (graph F).dist v y + 2 = b F ∧
        V F v 2 ≤ Q F y ∧ (¬ V F v 2 ≤ Q F t) ∧
        ⁅V F v 2,⁅V F v 2,V F t 1⁆⁆ = ⊥)) := by
  have hr := reduced_sections_recognized h hc hne E₀ E₁ c₀ c₁
    (by rw [h₀]; exact hodd v) (by rw [h₁]; exact hodd w)
    σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  have hn := hr.1.hasNaturalCenters d₀ d₁
  rw [h₀,h₁] at hn
  exact ⟨hr.1,graph_epsilonTwo_radius_two_configuration
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_kernel_sylow h)
    L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hn.1 hn.2 hr.2.2.2.1⟩

/-- Apply the constructed radius-two containment and escape to the literal
radius-one quotient section. The actor image is nontrivial and quadratic. -/
theorem reduced_radius_two_section_quadratic
    (h : HypothesisF11 L₀ S₀)
    {v t y : Vertex F} (hty : (graph F).Adj t y)
    (hdt : (graph F).dist v t + 1 = b F) (hb : 4 < b F)
    (hcore : V F v 2 ≤ Q F y) (hesc : ¬ V F v 2 ≤ Q F t)
    (c : LocalRankOneData (stabilizer F t) (stabilizer F t ⊓ stabilizer F y))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F t))
    [((Q F t).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q F t).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (V F t 1) (Z F t)
      (σ.comp (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar)))) :
    V F v 2 ≤ c.Pstar ∧
      (((V F v 2).subgroupOf c.Pstar).map
        (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar)) ≠ ⊥) ∧
      IsQuadratic σ (((V F v 2).subgroupOf c.Pstar).map
        (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar))) := by
  let : ((Q (family (fun i => (P₀ L₀ S₀ i).subgroupOf (G₀ L₀ S₀))) t).subgroupOf c.Pstar).Normal :=
    inferInstanceAs (((Q F t).subgroupOf c.Pstar).Normal)
  have hh := graph_radius_two_quadratic_section (reduced_triple h) (reduced_kernel_sylow h)
    hty hdt hb hcore c ho σ s
  refine ⟨hh.1,?_,hh.2⟩
  intro he
  have hle := (Subgroup.map_eq_bot_iff _).mp he
  rw [QuotientGroup.ker_mk'] at hle
  apply hesc
  intro a ha
  exact hle (show (⟨a,hh.1 ha⟩ : c.Pstar) ∈ (V F v 2).subgroupOf c.Pstar from ha)

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
