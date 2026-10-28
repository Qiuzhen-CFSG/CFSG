module
public import CFSG.Quasithin.ChapterG.Section11.NaturalSixExclusion
public import CFSG.Quasithin.ChapterG.Section11.ExchangedModels

/-!
# Finite constituent models in the remaining exchanged G.11 branch

The proper marked constituent has already been closed. In the exchanged
branch, the original low-rank witness now supplies a complementary pair
filling V and the complete G.6.4 coordinates on the literal stabilizer-action
quotient. Only GL_3(2), GL_4(2), GL_5(2), and natural S_5 through S_8 remain
on that constituent. The marked point, form, component orbit and elementary
actor are retained throughout.

This is a reduction of G.11.1(3ii). The solvable degree-six recognition,
whole component-orbit G.9 branch, and reconstruction or exclusion of these
exchanged models remain necessary for the full G.11.2 conclusion.
Source: Aschbacher--Smith G.10.16, G.11.5--7, printed pp.363--367.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The remaining component alternatives, now with actual finite models on
the exchanged constituent and its complementary pair in the original V. -/
def WholeOrExchangedModelReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
  ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
    Section10.ComponentOrthogonalData ρ B L ∧
    (Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive X)) ∨
      ∃ I : Submodule (ZMod 2) V,
        ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
          v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I ∧
          (∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x))) ∧
          finrank (ZMod 2) V = 2 * finrank (ZMod 2) I ∧
          finrank (ZMod 2) I ≤ 6 ∧ ExchangedRankOneModels ρ X L I hI)

/-- Apply the exchanged transvection classification to the original G.11
inputs. No full-linear properness, fixed-space equality or model is assumed. -/
theorem conclusion_or_whole_or_exchanged_models
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ WholeOrExchangedModelReduction ρ B v W X))) := by
  rcases conclusion_or_whole_or_exchanged_component_reduction h cover hw hS with
    hc | ⟨hi,hd,hs | ⟨hn,L,hL,hm,horth,hwhole | ⟨I,hI,hv,hgeo⟩⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inl hwhole⟩⟩
  · obtain ⟨x,hx,hcompl,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
    obtain ⟨hdim,hbound⟩ := exchanged_degree_le_twelve h cover hw hS hn hL hm hI hgeo
    exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inr
      ⟨I,hI,hv,hgeo,⟨x,hx,hcompl⟩,hdim,hbound,
        exchanged_constituent_models h cover hw hS hn hL hm hI hgeo⟩⟩⟩

end CFSG.Quasithin.ChapterG.Section11
