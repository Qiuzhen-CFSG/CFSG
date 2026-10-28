module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalTypes
public import CFSG.Quasithin.Chapter10.SourceA5ProductMixedTypes
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedTypes
/-!
# Literal models of the original proper moved A₅ seed

The irreducible central image of the original seed has one of four literal
binary product-module types: the two relative Frobenius natural tensors and
the natural/deleted tensors in either orientation. A single specified A₅ to
SL₂(4) baseline marks both factors in all four models.

For the natural branch, transport through the PSL₂(4) factor of the proved
cubic-free tensor recognition and cancel that transport in the intertwiner.
Perfectness is derived from A₅. The source product alternatives supply the
mixed markings, and original homogeneity excludes the invariant deleted
square for a proper seed. Thus the actual source consumer has no additional
classification or marking witness premise. The dependent model carriers and
actions are exposed so case analysis retains their exact model instances.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, printed pp.195–196;
GLS2 Theorem 25.14, Step 5, for the natural tensor recognition.
-/

@[expose] public noncomputable section
open Representation Representation.QuadraticFourGroup Representation.QuadraticFourGroup.TensorClassification
open Representation.AlternatingFiveMovedPair
namespace CFSG.Quasithin.Chapter10
local notation "Alt" => alternatingGroup (Fin 5)

/-- Cubic-free natural tensors have a unique label under one original marking. -/
theorem source_a5_cubicFree_marked_unique_type
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (Alt × Alt) U) [ρ.IsIrreducible]
    (h : CubicFreeOnFactors ρ) (base : Alt ≃* SL2FourNatural.SL) :
    ∃! c : Bool, Nonempty (Representation.Equiv ρ
      ((NaturalTypes.model c).comp (base.prodCongr base).toMonoidHom)) := by
  let j : Alt ≃* Factor 2 :=
    (base.trans SL2FourNatural.standardGroupEquiv).trans (specialLinearEquivFactor 2)
  let σ : Representation (ZMod 2) (Factor 2 × Factor 2) U :=
    ρ.comp (j.symm.prodCongr j.symm).toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (j.symm.prodCongr j.symm).toMonoidHom
      (j.symm.prodCongr j.symm).surjective ρ).mpr inferInstance
  let : Group.IsPerfect Alt := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Factor 2) :=
    Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
  have hs : CubicFreeOnFactors σ := by
    constructor
    · intro g hg v hv
      apply h.1 (j.symm g) ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change ρ (j.symm g,j.symm 1) v = v at hv
      simpa only [map_one] using hv
    · intro g hg v hv
      apply h.2 (j.symm g) ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change ρ (j.symm 1,j.symm g) v = v at hv
      simpa only [map_one] using hv
  obtain ⟨c,⟨e⟩,_⟩ := NaturalTypes.cubicFree_marked_unique_type σ hs (j.symm.trans base)
  have he : Nonempty (Representation.Equiv ρ
      ((NaturalTypes.model c).comp (base.prodCongr base).toMonoidHom)) := by
    refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
    intro g
    apply LinearMap.ext
    intro v
    change e.toLinearEquiv (ρ g v) =
      NaturalTypes.model c (base g.1,base g.2) (e.toLinearEquiv v)
    have hv := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
      (j g.1,j g.2) v
    change e.toLinearEquiv (ρ (j.symm (j g.1),j.symm (j g.2)) v) =
      NaturalTypes.model c (base (j.symm (j g.1)),base (j.symm (j g.2))) (e.toLinearEquiv v) at hv
    simpa only [MulEquiv.symm_apply_apply] using hv
  exact ⟨c,he,fun d hd => NaturalTypes.marked_label_unique ρ base hd he⟩

namespace SourceA5MovedSeedModels
/-- The four literal proper moved-seed models, with the original factor labels. -/
inductive Label
  | nn0 | nn1 | nd | dn
  deriving DecidableEq

instance labelFintype : Fintype Label where
  elems := {.nn0, .nn1, .nd, .dn}
  complete a := by cases a <;> simp

/-- The literal carrier of each displacement-model constituent. -/
def Space : Label → Type
  | .nn0 => Natural.Tensor
  | .nn1 => Natural.Tensor
  | .nd => Mixed.ND
  | .dn => Mixed.DN

instance spaceAddCommGroup : (a : Label) → AddCommGroup (Space a)
  | .nn0 => inferInstanceAs (AddCommGroup Natural.Tensor)
  | .nn1 => inferInstanceAs (AddCommGroup Natural.Tensor)
  | .nd => inferInstanceAs (AddCommGroup Mixed.ND)
  | .dn => inferInstanceAs (AddCommGroup Mixed.DN)
instance spaceModule : (a : Label) → Module (ZMod 2) (Space a)
  | .nn0 => inferInstanceAs (Module (ZMod 2) Natural.Tensor)
  | .nn1 => inferInstanceAs (Module (ZMod 2) Natural.Tensor)
  | .nd => inferInstanceAs (Module (ZMod 2) Mixed.ND)
  | .dn => inferInstanceAs (Module (ZMod 2) Mixed.DN)

/-- The actions use the exact SL factors of the natural and mixed models. -/
def action : (a : Label) → Representation (ZMod 2)
    (SL2FourNatural.SL × SL2FourNatural.SL) (Space a)
  | .nn0 => Natural.first
  | .nn1 => Natural.second
  | .nd => MixedTypes.firstSL
  | .dn => MixedTypes.secondSL

/-- One specified baseline marks every constituent of the finite catalogue. -/
def markedAction (base : Alt ≃* SL2FourNatural.SL) (a : Label) :
    Representation (ZMod 2) (Alt × Alt) (Space a) :=
  (action a).comp (base.prodCongr base).toMonoidHom
end SourceA5MovedSeedModels

open Subgroup Theory.GroupTheory
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* Alt)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

/-- The original proper moved seed has one of four literal model labels.
All equivalences retain the same chosen original A₅ factor baseline. -/
theorem source_a5_moved_seed_model
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hleft : ∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1)
    (hright : ∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1)
    (base : Alt ≃* SL2FourNatural.SL) :
    ∃ a : SourceA5MovedSeedModels.Label,
      Nonempty (Representation.Equiv (originalA5SeedAction D e hn ht htn)
        (SourceA5MovedSeedModels.markedAction base a)) := by
  let := originalA5SeedAction_irreducible D e hn ht htn
  rcases source_a5_product_module_alternatives_fixed_mixed_marking
      (originalA5SeedAction D e hn ht htn) hleft hright base with hf | hdn | hnd | hdd
  · obtain ⟨c,hc,_⟩ := source_a5_cubicFree_marked_unique_type
      (originalA5SeedAction D e hn ht htn) hf base
    cases c
    · exact ⟨.nn0,hc⟩
    · exact ⟨.nn1,hc⟩
  · exact ⟨.dn,hdn⟩
  · exact ⟨.nd,hnd⟩
  · exact (source_a5_moved_seed_not_deleted_square D e hn ht htn hproper hdd).elim

/-- A disjunction form directly names the four displacement constituents. -/
theorem source_a5_moved_seed_fixed_model_alternatives
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hleft : ∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1)
    (hright : ∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1)
    (base : Alt ≃* SL2FourNatural.SL) :
    Nonempty (Representation.Equiv (originalA5SeedAction D e hn ht htn)
      (Natural.first.comp (base.prodCongr base).toMonoidHom)) ∨
    Nonempty (Representation.Equiv (originalA5SeedAction D e hn ht htn)
      (Natural.second.comp (base.prodCongr base).toMonoidHom)) ∨
    Nonempty (Representation.Equiv (originalA5SeedAction D e hn ht htn)
      (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
    Nonempty (Representation.Equiv (originalA5SeedAction D e hn ht htn)
      (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨a,ha⟩ := source_a5_moved_seed_model D e hn ht htn hproper hleft hright base
  cases a with
  | nn0 => exact Or.inl ha
  | nn1 => exact Or.inr (Or.inl ha)
  | nd => exact Or.inr (Or.inr (Or.inl ha))
  | dn => exact Or.inr (Or.inr (Or.inr ha))
end CFSG.Quasithin.Chapter10
