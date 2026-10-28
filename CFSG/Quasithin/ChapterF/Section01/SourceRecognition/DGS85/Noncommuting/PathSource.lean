module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusTwoSource

/-!
# Source recognition supplies the first singular path

The actual reduced F1.11 graph supplies the finite faithful local triple,
full edge core and kernel Sylows. Corrected recognition on the two literal
critical sections constructs their natural coordinates. The center identities
then give either b=2 or a first singular length s with 0<s≤b−2, together
with regularity of every shorter path and same-type path transitivity through
length s. Both vertex orbits participate in this minimum.

Local models, faithful marked sections, residual fixed-space vanishing and
the earlier adjacent-core obstruction remain explicit source inputs. This
application does not assume path regularity or a distance bound. The quotient
exclusion in (7.5)(5) and final index comparison remain unproved here.

Source: DGS, *Groups and Graphs* (1985), (3.4), pp.73--74, and (7.5)(4), p.130.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Literal source application, constructing natural coordinates and the minimum
nonregular length from the two actual critical sections. -/
theorem reduced_epsilonTwo_path_regularity
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
      (b F = 2 ∨ ∃ s : ℕ, 0 < s ∧ s + 2 ≤ b F ∧
      (∀ k x (q : BasedWalk (graph F) k x),
        k < s → q.Nonbacktracking → Regular (A := (G₀ L₀ S₀)) q) ∧
      (∃ x, ∃ q : BasedWalk (graph F) s x,
        q.Nonbacktracking ∧ ¬ RightRegular (A := (G₀ L₀ S₀)) q) ∧
      (∀ k (_hk : k ≤ s) x y
        (q : BasedWalk (graph F) k x)
        (r : BasedWalk (graph F) k y),
        q.Nonbacktracking → r.Nonbacktracking → x.type = y.type →
        ∃ g : G₀ L₀ S₀, q.vertices.map (g • ·) = r.vertices)) := by
  have hr := reduced_sections_recognized h hc hne E₀ E₁ c₀ c₁
    (by rw [h₀]; exact hodd v) (by rw [h₁]; exact hodd w)
    σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  have hn := hr.1.hasNaturalCenters d₀ d₁
  rw [h₀,h₁] at hn
  exact ⟨hr.1,graph_epsilonTwo_regularity_length
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_kernel_sylow h)
    L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hn.1 hn.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
