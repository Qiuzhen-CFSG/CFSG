module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefComparison
public import Theory.Representation.BinaryOffender.MovedPlaneFaithfulHead

/-!
# Recovering original faithful component coordinates

A faithful section identifies the original actor with its action image.
The component marking gives the same identification on the generalized
Fitting subgroup. Simplicity then proves that the original component has
trivial centralizer. Top-section transport supplies the literal chief
representatives used by the source catalogue.
Source application: Aschbacher–Smith13.5.21, printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open ChapterB.QuasisimpleSource
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) E W)

def faithfulImageEquiv (hf : Function.Injective ρ) : E ≃* actionImage ρ :=
  MulEquiv.ofBijective (actionHom ρ) ⟨fun _ _ hh => hf (congrArg (fun x : actionImage ρ => x.val.val) hh),
    ρ.asGroupHom.rangeRestrict_surjective⟩

def faithfulComponentEquiv (L : Subgroup E) (hf : Function.Injective ρ)
    (hL : actionSubgroup ρ L = generalizedFitting (actionImage ρ)) :
    L ≃* generalizedFitting (actionImage ρ) :=
  (L.equivMapOfInjective (actionHom ρ) (faithfulImageEquiv ρ hf).injective).trans
    (MulEquiv.subgroupCongr hL)

def faithfulComponentActionEquiv (L : Subgroup E) (hf : Function.Injective ρ)
    (hL : actionSubgroup ρ L = generalizedFitting (actionImage ρ)) :
    ActionEquiv (ρ.comp L.subtype)
      ((imageRepresentation ρ).comp (generalizedFitting (actionImage ρ)).subtype) where
  groupEquiv := faithfulComponentEquiv ρ L hf hL
  linearEquiv := LinearEquiv.refl _ _
  intertwines _ _ := rfl

/-- The original actor centralizer is trivial when its faithful chief image
has precisely the simple component as generalized Fitting subgroup. -/
theorem centralizer_eq_bot_of_faithful_component [Finite E]
    (L : Subgroup E) [IsSimpleGroup L] [Group.IsPerfect L]
    (hf : Function.Injective ρ)
    (hL : actionSubgroup ρ L = generalizedFitting (actionImage ρ)) :
    center (generalizedFitting (actionImage ρ)) = ⊥ ∧ centralizer (L : Set E) = ⊥ := by
  let e := faithfulComponentEquiv ρ L hf hL
  let : IsSimpleGroup (generalizedFitting (actionImage ρ)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (generalizedFitting (actionImage ρ)) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz : center (generalizedFitting (actionImage ρ)) = ⊥ :=
    (inferInstance : (center (generalizedFitting (actionImage ρ))).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  refine ⟨hz,?_⟩
  apply bot_unique
  intro g hg
  apply (faithfulImageEquiv ρ hf).injective
  apply (show actionHom ρ g = 1 from ?_).trans (map_one _).symm
  have hc := SimpleSocle.centralizer_eq_bot (G := actionImage ρ)
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting (actionImage ρ)))
  apply show actionHom ρ g ∈ (⊥ : Subgroup (actionImage ρ)) from ?_
  rw [← hc]
  apply mem_centralizer_iff.mpr
  intro y hy
  rw [← hL] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  exact (map_mul (actionHom ρ) x g).symm.trans
    ((congrArg (actionHom ρ) (mem_centralizer_iff.mp hg x hx)).trans
      (map_mul (actionHom ρ) g x))

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

namespace Representation.BinaryOffender
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) E W)

theorem top_section_irreducible (N : Subrepresentation ρ) (hN : IsCoatom N) :
    IsIrreducible (sectionRepresentation ρ N ⊤) :=
  irreducible_of_surjective_equivariant _ N.quotientRepresentation (MonoidHom.id E)
    Function.surjective_id (topSectionEquiv ρ N) (topSectionEquiv_intertwines ρ N)
    (SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN)

theorem top_section_noncentral (N : Subrepresentation ρ) (L : Subgroup E)
    (hn : ¬ L ≤ N.quotientRepresentation.ker) :
    ¬ L ≤ (sectionRepresentation ρ N ⊤).ker := by
  intro hh
  apply hn
  intro g hg
  apply LinearMap.ext
  intro w
  obtain ⟨w,rfl⟩ := (topSectionEquiv ρ N).surjective w
  rw [← topSectionEquiv_intertwines]
  rw [show sectionRepresentation ρ N ⊤ g = 1 from hh hg]
  rfl
end Representation.BinaryOffender
