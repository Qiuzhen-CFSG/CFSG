module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Statement
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cohomology and the fixed supplement in the natural-plus-dual branch

The dot-product identification sends the contragredient natural action to
the natural action twisted by inverse transpose. Consequently the proved
natural SL cohomology vanishing applies to both summands. Componentwise
principality proves vanishing for their product. The connecting cocycle of
[V,G] then gives V = [V,G] + C_V(G), with no splitting premise.

`MovedSection.fixed_supplement_of_naturalDual` applies these constructions
to the literal moved subrepresentation used by B.5.1(6). This is an
unconditional consequence of that branch's actual action equivalence.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.6(6),
printed p.408, and B.5.1, printed pp.102–103.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource


universe u v w z
variable {G : Type u} {H : Type v} [Group G] [Group H]
  {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

/-- Vanishing of first cohomology is preserved by the given action equivalence. -/
theorem ActionEquiv.H1_subsingleton (e : ActionEquiv ρ σ)
    [Subsingleton (H1 σ)] : Subsingleton (H1 ρ) :=
  (H1Congr ρ σ e.groupEquiv e.linearEquiv e.intertwines).injective.subsingleton

variable {τ : Representation (ZMod 2) G W}

/-- A cocycle on a product is principal when both coordinate cocycles are. -/
theorem H1_prod_subsingleton [Subsingleton (H1 ρ)] [Subsingleton (H1 τ)] :
    Subsingleton (H1 (ρ.prod τ)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let f₁ : cocycles ρ := ⟨fun g => (f.val g).1, fun g h => congrArg Prod.fst (f.property g h)⟩
  let f₂ : cocycles τ := ⟨fun g => (f.val g).2, fun g h => congrArg Prod.snd (f.property g h)⟩
  obtain ⟨v, hv⟩ := (classMap_eq_zero_iff ρ f₁).mp (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := (classMap_eq_zero_iff τ f₂).mp (Subsingleton.elim _ _)
  refine ⟨(v, w), ?_⟩
  apply Subtype.ext
  funext g
  apply Prod.ext
  · exact congrArg (fun c : cocycles ρ => c.val g) hv
  · exact congrArg (fun c : cocycles τ => c.val g) hw

/-- The actual dual-to-natural identification twists the group by inverse transpose. -/
noncomputable def dualNaturalEquiv (d : ℕ) :
    ActionEquiv (linearNatural BinaryField.two d).dual (linearNatural BinaryField.two d) := by
  change ActionEquiv (specialLinearNatural (k := ZMod 2) d).dual
    (specialLinearNatural (k := ZMod 2) d)
  refine { groupEquiv := BinaryLinear.OuterCyclic.graphSL d
           linearEquiv := (dotProductEquiv (ZMod 2) (Fin d)).symm
           intertwines := ?_ }
  intro g f
  apply (dotProductEquiv (ZMod 2) (Fin d)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  let w := (dotProductEquiv (ZMod 2) (Fin d)).symm f
  have hw : dotProductEquiv (ZMod 2) (Fin d) w = f := LinearEquiv.apply_symm_apply _ _
  change f ((g⁻¹).val.mulVec v) = ((BinaryLinear.OuterCyclic.graphSL d g).val.mulVec w) ⬝ᵥ v
  rw [← hw]
  change w ⬝ᵥ ((g⁻¹).val.mulVec v) =
    ((BinaryLinear.OuterCyclic.graphSL d g).val.mulVec w) ⬝ᵥ v
  have he : (BinaryLinear.OuterCyclic.graphSL d g).val = (g⁻¹).val.transpose := by
    change ((Matrix.SpecialLinearGroup.transpose g)⁻¹).val = _
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose]
  rw [he]
  exact (Matrix.dotProduct_transpose_mulVec (g⁻¹).val v w).symm.trans (dotProduct_comm _ _)

/-- The proved natural SL calculation, under the native binary action convention. -/
theorem H1_linearNatural_subsingleton {d : ℕ} (hd : 4 ≤ d) :
    Subsingleton (H1 (linearNatural BinaryField.two d)) := by
  let := OneCohomology.SLHigherNatural.H1_subsingleton_of_four_le (K := ZMod 2) hd
  exact (H1RestrictEquiv (k := ZMod 2) (specialLinearNatural (k := ZMod 2) d)).injective.subsingleton

/-- Both natural and dual cohomology vanish in dimension at least four. -/
theorem H1_naturalPlusDual_subsingleton {d : ℕ} (hd : 4 ≤ d) :
    Subsingleton (H1 (naturalPlusDual d)) := by
  let := H1_linearNatural_subsingleton hd
  let := (dualNaturalEquiv d).H1_subsingleton
  exact H1_prod_subsingleton

/-- Remove the harmless restriction to the top subgroup, retaining both maps. -/
noncomputable def ActionEquiv.ofTop
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup G).subtype) σ) : ActionEquiv ρ σ where
  groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, Subgroup.mem_top g⟩ v

variable (ρ)

/-- The connecting class of the literal moved module produces a fixed supplement. -/
theorem MovedSection.fixed_supplement_of_H1_subsingleton (s : MovedSection ρ ⊤)
    [Subsingleton (H1 s.space.toRepresentation)] :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  have htriv : OneCohomology.HasTrivialQuotient s.space := by
    intro g v
    change ρ g v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩
  apply top_unique
  intro v _
  exact (OneCohomology.extensionClass_eq_zero_iff s.space htriv v).mp
    (Subsingleton.elim _ _)

/-- The natural-plus-dual branch has a fixed supplement without any extension input. -/
theorem MovedSection.fixed_supplement_of_naturalDual {L : Subgroup G}
    (s : MovedSection ρ L) {d : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hnat : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  subst L
  obtain ⟨e⟩ := hnat
  let := H1_naturalPlusDual_subsingleton hd
  let := e.ofTop.H1_subsingleton
  exact s.fixed_supplement_of_H1_subsingleton ρ

end CFSG.Quasithin.ChapterB.QuasisimpleSource
