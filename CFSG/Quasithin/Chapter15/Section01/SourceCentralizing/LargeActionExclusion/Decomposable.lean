module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Dimensions of the original large decomposable action

The marked involution in each dihedral factor has displacement at most half
the factor dimension. Cubic ratio two forces displacement at least two,
so the original prime/dimension options force dimension four. The original
complementary supports then give dimension eight for the whole module.
The ratio-one orthogonal alternative is outside this implication.

Source: Aschbacher--Smith 15.1.7(6), printed pp.1087--1088.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.RatioDecomposition
universe u
variable {D W G : Type u} [Group D] [Finite D] [Group G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem marked_dimension_four {ρ : Representation (ZMod 2) D W}
    (l : CyclicSource.LocalGeneration ρ) {p m : ℕ}
    (hpm : CyclicSource.PrimeDimensionOptions p m)
    (hmark : CyclicSource.DihedralMarking l p m) (hq : cubicRatio ρ = 2) :
    m = 2 ∧ Module.finrank (ZMod 2) W = 4 := by
  obtain ⟨he,hr,hquad,hhalf⟩ := involution_actor_rank_and_fixedCodim ρ l.involution l.order_two
  have hlo : cubicRatio ρ ≤ actionRatio ρ (zpowers l.involution) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
  rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hlo
  have hlo' : 2 ≤ fixedCodim ρ (zpowers l.involution) := by exact_mod_cast hlo
  have hd := hmark.dimension
  have hm : m = 2 := by
    rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨_,hm⟩ | ⟨_,hm⟩ <;> omega
  exact ⟨hm,by omega⟩

omit [Finite D] in
/-- The large decomposable row has the original two four-dimensional factors,
with the original dihedral markings; the whole module has dimension eight. -/
theorem SourceCases.Decomposable.ratio_two_dimensions
    {ρ : Representation (ZMod 2) D W} {T M : Subgroup G} {f : M →* D}
    {U : Submodule (ZMod 2) W} {c : FactorData ρ (Jhat ρ) U}
    {d : Decomposition c.representation} {π : D →* Equiv.Perm d.Index}
    (h : SourceCases.Decomposable ρ T M f c d π) (hq : cubicRatio ρ = 2) :
    Module.finrank (ZMod 2) W = 8 ∧
      ∃ p, (p = 3 ∨ p = 5) ∧
        (∀ k, ∃ l : CyclicSource.LocalGeneration (d.factor k).action,
          CyclicSource.DihedralMarking l p 2) ∧
        ∀ k, Module.finrank (ZMod 2) (d.factor k).Space = 4 ∧
          Module.finrank (ZMod 2) (c.ambientFactor d k).space = 4 := by
  obtain ⟨_,p,m,hpm,hmarks,i,j,_,_,_,_,_,hcompl,_⟩ := h
  obtain ⟨l,hl⟩ := hmarks i
  have hm := (marked_dimension_four l hpm hl
    ((d.factor i).embedding.ratio.trans (c.ratio.trans hq))).1
  subst m
  have hd (k : d.Index) : Module.finrank (ZMod 2) (d.factor k).Space = 4 := by
    obtain ⟨l,hl⟩ := hmarks k
    exact hl.dimension
  have ha (k : d.Index) : Module.finrank (ZMod 2) (c.ambientFactor d k).space = 4 := by
    let a := (c.ambientFactor d k).embedding.spaceMap
    let e := LinearEquiv.ofInjective a (c.ambientFactor d k).embedding.space_injective
    exact e.finrank_eq.symm.trans (hd k)
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [ha i,ha j] at hdim
  refine ⟨hdim.symm,p,?_,hmarks,fun k => ⟨hd k,ha k⟩⟩
  rcases (CyclicSource.primeDimensionOptions_iff p 2).mp hpm with ⟨hp,_⟩ | ⟨hp,_⟩
  · exact Or.inl hp
  · exact Or.inr hp

end CFSG.Quasithin.Chapter15.Section01
