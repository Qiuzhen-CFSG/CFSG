module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LastOddQuotient

/-!
# The last odd quotient exclusion on the reduced F.1.11 graph

The original F.1.11 reduction supplies the faithful graph, full edge core
and kernel Sylows. Corrected quadratic recognition constructs the natural
critical sections and opposite-center Sylow product. Applying the complete
(7.5)(5) path argument constructs the last odd vertex and excludes both
linear quotient models there, unless b=2. The local actor, its actual O₂
quotient, and equal-field natural coordinates are retained.

Local model, faithful-action, residual-fixed-space and branching inputs
remain earlier-source premises. This does not assert the unfinished final
index comparison or the unconditional Chapter 7 distance bound.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126--127, and (7.5)(5), p.130.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- DGS (7.5)(5) on the literal reduced source graph, with natural-section
recognition and all path-complement and path-fixing premises discharged. -/
theorem reduced_epsilonTwo_last_odd_not_linear
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
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
      (b F = 2 ∨ (6 ≤ b F ∧ ∃ t y : Vertex F,
        (graph F).Adj w t ∧ (graph F).Adj t y ∧
        (graph F).dist v t + 1 = b F ∧ (graph F).dist v y + 2 = b F ∧
        V F v 2 ≤ Q F y ∧ (¬ V F v 2 ≤ Q F t) ∧
        ∀ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
          (¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃* SL(2,k))) ∧
          (¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)))) := by
  have hr := reduced_sections_recognized h hc hne E₀ E₁ c₀ c₁
    (by rw [h₀]; exact hodd v) (by rw [h₁]; exact hodd w)
    σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  have hn := hr.1.hasNaturalCenters d₀ d₁
  rw [h₀,h₁] at hn
  exact ⟨hr.1,graph_epsilonTwo_last_odd_not_linear
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_kernel_sylow h)
    L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hn.1 hn.2 hr.2.2.2.1 hbranch⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
