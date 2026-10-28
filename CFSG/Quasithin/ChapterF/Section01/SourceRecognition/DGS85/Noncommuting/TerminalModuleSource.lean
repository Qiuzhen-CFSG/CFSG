module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalModule

/-!
# Reduced-source application of the terminal module construction

The generic Chapter 7 terminal argument is applied to the actual reduced
F.1.11 carrier.  The preceding recognized sections discharge the natural
center and Sylow inputs; the terminal quotient module remains literal.
Its Sylow action is faithful and its quotient is neither D₁₀ nor SL₂.
Full faithfulness, residual-fixed-space vanishing and the remaining model
comparison are retained by the final source assembly.

Source: DGS, *Groups and Graphs* (1985), (7.1), (7.4)--(7.5), pp.126--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

theorem reduced_epsilonTwo_terminal_module
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
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
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v)
      (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w)
      (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))))
    (M₀ : BinaryRankOneModel (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
    (M₁ : BinaryRankOneModel (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
      (b F = 2 ∨ ∃ t y : Vertex F, ∃ hty : (graph F).Adj t y,
        let c := d t y hty
        letI := c.finite_P
        letI : Finite c.Pstar := Finite.of_injective
          (inclusion c.Pstar_le) (inclusion_injective _)
        letI : ((Q F t).subgroupOf c.Pstar).Normal := graph_local_core_normal t c
        ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
          ∃ σ : Representation (ZMod 2) (c.Pstar ⧸ (Q F t).subgroupOf c.Pstar) W,
            Nonempty (BinaryConjugationSection c.Pstar (V F t 1) (Z F t)
              (σ.comp (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar)))) ∧
            Nontrivial W ∧ Finite W ∧
            let π := QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar)
            let T := c.sylow.mapSurjective
              (QuotientGroup.mk'_surjective ((Q F t).subgroupOf c.Pstar))
            GeneratedByFixedSpace σ T ∧ Disjoint σ.ker (T : Subgroup _) ∧
            (∃ a : Vertex F, (graph F).Adj v a ∧ V F a 1 ≤ c.Pstar ∧
              let A := ((V F a 1).subgroupOf c.Pstar).map π
              A ≤ T ∧ 1 < Nat.card A ∧ IsQuadratic σ A ∧
              Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) ∧
            ¬ Nonempty ((c.Pstar ⧸ (Q F t).subgroupOf c.Pstar) ≃* DihedralGroup 5) ∧
            ∀ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
              ¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃* SL(2,k))) := by
  have hr := reduced_sections_recognized h hc hne E₀ E₁ c₀ c₁
    (by rw [h₀]; exact hodd v) (by rw [h₁]; exact hodd w)
    σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  have hn := hr.1.hasNaturalCenters d₀ d₁
  rw [h₀,h₁] at hn
  refine ⟨hr.1, ?_⟩
  rcases graph_epsilonTwo_distance_gap (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_kernel_sylow h)
    L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hn.1 hn.2 with hb | hb
  · exact Or.inl hb
  · exact Or.inr (graph_epsilonTwo_terminal_module
      (reduced_triple h) (reduced_borel_core_sylow h) (reduced_kernel_sylow h)
      L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hn.1 hn.2
      hr.2.2.2.1 hbranch (by omega))

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
