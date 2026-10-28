module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter12.Section09.SourceSetup
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.Quotient

/-!
# Marking the original module in the two branches of 12.5.1

An equivalence of the chosen Irr⁺ action gives coordinates on its actual
ambient image V, with the original map L → L/O₂(L). In the ten-dimensional
irreducible case, I.1.6(7) gives the exterior square or cube. Complementary
wedges turn the cube into the square by changing the quotient marking by
inverse transpose. Thus the subsequent ambient argument needs only one
exterior model, without discarding the dual case.

The natural case supplies exactly the full AmbientNaturalMarking required
by Section 12.9. These are representation-theoretic reductions, not the
ambient exclusion of the exterior branch.

Source: Aschbacher--Smith, 12.5.1, printed pp.816--817, and I.1.6(7), p.408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterB.QuasisimpleSource
open Representation.SL5TenDimensional
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Coordinates on the entire original subgroup, intertwining its literal
conjugation action and quotient projection. -/
structure AmbientMarking (D : ChosenModule T L V)
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* A
  coordinates : V ≃* Multiplicative W
  equivariant : ∀ (l : L) (v : V),
    coordinates ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (D.normalizes l.property) v).mp v.property⟩ =
        Multiplicative.ofAdd (σ (quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
          (coordinates v).toAdd)

/-- Transport the chosen-space marking through its original ambient inclusion. -/
def ambientMarking (D : ChosenModule T L V)
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) A W} (e : ActionEquiv D.quotientAction σ) :
    AmbientMarking D σ := by
  apply Classical.choice
  obtain ⟨a, f, hf⟩ := D.conjugationModel_of_quotientAction e
  refine ⟨⟨a, f, ?_⟩⟩
  intro l v
  apply f.symm.injective
  apply Subtype.ext
  simpa only [MulEquiv.symm_apply_apply] using (hf l v).symm

/-- The exterior marking may absorb inverse transpose in its quotient map. -/
abbrev ExteriorMarking (D : ChosenModule T L V) := AmbientMarking D (exteriorAction 2)

/-- Full natural coordinates, with exactly the ambient convention of 12.8.1. -/
theorem naturalModule_of_actionEquiv (D : ChosenModule T L V) (n : ℕ)
    (e : ActionEquiv D.quotientAction (specialLinearNatural (k := ZMod 2) n)) :
    Section09.NaturalModule D n := by
  let := D.elementary
  let a := ambientMarking D e
  let c : Additive V ≃+ (Fin n → ZMod 2) := {
    toFun v := (a.coordinates v.toMul).toAdd
    invFun w := Additive.ofMul (a.coordinates.symm (Multiplicative.ofAdd w))
    left_inv v := congrArg Additive.ofMul (a.coordinates.symm_apply_apply v.toMul)
    right_inv w := congrArg Multiplicative.toAdd
      (a.coordinates.apply_symm_apply (Multiplicative.ofAdd w))
    map_add' v w := congrArg Multiplicative.toAdd (a.coordinates.map_mul v.toMul w.toMul) }
  refine ⟨a.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n),
    c.toLinearEquiv (ZMod.map_smul c), ?_⟩
  intro l v
  exact congrArg Multiplicative.toAdd (a.equivariant l v.toMul)

/-- I.1.6(7), applied to the literal ten-dimensional chosen action. The cube
is transported by the actual complementary-wedge equivalence and graph automorphism. -/
theorem exteriorMarking_of_irreducible_ten (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 10)
    (hi : Representation.IsIrreducible D.quotientAction) :
    Nonempty (ExteriorMarking D) := by
  let ρ := D.quotientAction.comp e.symm.toMonoidHom
  let : Representation.IsIrreducible ρ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      D.quotientAction).mpr hi
  rcases Classification.identification_of_finrank_ten ρ hd with hs | hc
  · obtain ⟨f⟩ := hs
    refine ⟨ambientMarking D ⟨e, f.toLinearEquiv, ?_⟩⟩
    intro q v
    have hf := LinearMap.congr_fun (f.isIntertwining' (e q)) v
    change f (D.quotientAction (e.symm (e q)) v) = _ at hf
    simpa only [MulEquiv.symm_apply_apply, LinearMap.comp_apply,
      Representation.Equiv.toLinearEquiv_apply,
      Representation.IntertwiningMap.toLinearMap_apply,
      Representation.Equiv.coe_toIntertwiningMap] using hf
  · obtain ⟨f⟩ := hc
    refine ⟨ambientMarking D ⟨e.trans SL5ExteriorSquare.Duality.graph,
      f.toLinearEquiv.trans SL5ExteriorSquare.Duality.hodge, ?_⟩⟩
    intro q v
    have hf : f (D.quotientAction q v) = exteriorAction 3 (e q) (f v) := by
      have hf := LinearMap.congr_fun (f.isIntertwining' (e q)) v
      change f (D.quotientAction (e.symm (e q)) v) = _ at hf
      simpa only [MulEquiv.symm_apply_apply, LinearMap.comp_apply,
        Representation.IntertwiningMap.toLinearMap_apply,
        Representation.Equiv.coe_toIntertwiningMap] using hf
    change SL5ExteriorSquare.Duality.hodge (f (D.quotientAction q v)) = _
    rw [hf]
    exact SL5ExteriorSquare.Duality.hodge_action (e q) (f v)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
