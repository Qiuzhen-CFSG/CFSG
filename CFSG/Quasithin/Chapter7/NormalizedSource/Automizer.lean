module

public import CFSG.Quasithin.Chapter3.Section01.OffenderBranch
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# Non-FF for the actual ambient automizer

If N_G(W) normalizes L, its faithful action on W normalizes the image of L.
An equivariant marking of that image therefore transfers non-FF from the
full linear normalizer to Aut_G(W). A moving maximum elementary subgroup
would be an FF-offender, so the original J(T) centralizes W.

The Chapter12 application constructs the normalizer containment and the
marking on the full chosen-module orbit. These deductions supply the first
paragraph after Hypothesis7.0.2; they do not classify the remaining modules.
Source: Aschbacher--Smith, printed p.695, using B.2.7--8.
-/

public noncomputable section
open Stellmacher Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
variable {G K E : Type*} [Group G] [Group K]
  [AddCommGroup E] [Module (ZMod 2) E]

/-- An actual normal component marking controls the full ambient automizer. -/
theorem automizer_nonFF (W L : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G))
    (hNL : normalizer (W : Set G) ≤ normalizer (L : Set G))
    (ρ : Representation (ZMod 2) K E) (f : L →* K) (hf : Function.Surjective f)
    (e : E ≃ₗ[ZMod 2] Additive W)
    (he : ∀ (l : L) (v : E),
      e (ρ (f l) v) = Additive.ofMul
        ⟨(l : G) * ((e v).toMul : G) * (l : G)⁻¹,
          (mem_normalizer_iff.mp (hLN l.property) _).mp (e v).toMul.property⟩)
    (hnon : ¬ IsFFModule (normalizerRepresentation ρ)) :
    ¬ IsFFModule (ChapterE.automizerRepresentation W) := by
  let N := normalizer (W : Set G)
  let q := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W := q.comp (inclusion hLN)
  have hi : i.range = (L.subgroupOf N).map q := by
    ext a
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨inclusion hLN l, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNL
  let : i.range.Normal := hi ▸ Normal.map inferInstance q
    W.normalizerMonoidHom.rangeRestrict_surjective
  let b : Representation.Equiv ((ChapterE.automizerRepresentation W).comp i)
      (ρ.comp f) :=
    { __ := e.symm
      isIntertwining' l := by
        ext v
        apply e.injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        change ChapterE.automizerRepresentation W (i l) v = e (ρ (f l) (e.symm v))
        rw [he]
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [LinearEquiv.apply_symm_apply]
        rfl }
  exact not_isFFModule_of_marked_normal_range (ChapterE.automizerRepresentation W)
    (ChapterE.automizerRepresentation_injective W) i ρ f hf b hnon

/-- Non-FF of the full automizer forces the original elementary Thompson
subgroup to centralize the module. -/
theorem thompson_centralizes [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]
    {T : Sylow 2 G} (hT : ChapterE.HypothesisE322 W T)
    (hnon : ¬ IsFFModule (ChapterE.automizerRepresentation W)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  by_contra hJ
  have hff := Chapter3.internalActionImage_isFFModule_of_thompson_not_le T
    (normalizer (W : Set G)) W hT.normalizes hT.le_sylow le_rfl hJ
  let f : ChapterD.internalActionImage (normalizer (W : Set G)) W le_rfl →*
      ChapterE.Automizer W :=
    { toFun a := ⟨a.val, by obtain ⟨n, hn⟩ := a.property; exact ⟨n, hn⟩⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply hnon
  exact hff.map_equivariant _ _ f (fun _ _ he => Subtype.ext (congrArg Subtype.val he))
    (LinearEquiv.refl _ _) (fun _ _ => rfl)
end CFSG.Quasithin.Chapter7.NormalizedSource
