module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SylowOvergroups
/-!
# Quasisimple residuals cannot occur in solvable-Fitting parabolics

The literal solvable residual is normal. If it were quasisimple, it would
be a component and hence lie in the generalized Fitting subgroup. The
proved parabolic bound contradicts its nontrivial perfectness.
Source: Aschbacher–Smith A.3.12(2), applied in C.5.13, pp.47,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
theorem not_parabolicResidual_of_solvable_fitting {B L : Subgroup G}
    [IsQuasisimple B] (hres : IsParabolicResidual B L true)
    (hproper : ∀ (S : Sylow 2 L) (P : Subgroup L), normalizer (S : Set L) ≤ P → P ≠ ⊤ →
      Group.IsSolvable (generalizedFitting P)) : False := by
  obtain ⟨P,⟨S,hSP⟩,hP,he⟩ := hres
  have hne : P ≠ ⊤ := (hP rfl).ne_top
  let f : P →* G := L.subtype.comp P.subtype
  have hf : Function.Injective f := L.subtype_injective.comp P.subtype_injective
  let e : solvableResidual P ≃* B :=
    ((solvableResidual P).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)
  have hq : IsQuasisimple (solvableResidual P) := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple (solvableResidual P) := hq
  have hle := component_le_generalizedFitting P (solvableResidual P)
    ⟨Normal.isSubnormal inferInstance,hq⟩
  let := hproper S P hSP hne
  have hs : Group.IsSolvable (solvableResidual P) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hle) (inclusion_injective hle)
  let : IsSimpleGroup ((solvableResidual P) ⧸ center (solvableResidual P)) := hq.simple
  let : Nontrivial (solvableResidual P) := (QuotientGroup.mk'_surjective (center (solvableResidual P))).nontrivial
  exact Group.IsPerfect.not_isSolvable (solvableResidual P) hs
/-- Transport the actual parabolic and its residual through a carrier model. -/
theorem not_parabolicResidual_of_model {B L : Subgroup G}
    [IsQuasisimple B] (hres : IsParabolicResidual B L true)
    {D : Type*} [Group D] [Finite D] (e : L ≃* D)
    (hproper : ∀ (S : Sylow 2 D) (P : Subgroup D), normalizer (S : Set D) ≤ P → P ≠ ⊤ →
      Group.IsSolvable (generalizedFitting P)) : False := by
  apply not_parabolicResidual_of_solvable_fitting hres
  intro S P hSP hne
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let X := P.map e.toMonoidHom
  have hX : X ≠ ⊤ := by
    intro he
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  have hQX : normalizer (Q : Set D) ≤ X := by
    change normalizer ((S : Subgroup L).map e.toMonoidHom : Set D) ≤ X
    rw [← map_normalizer_eq_of_bijective _ e.bijective]
    exact map_mono hSP
  let := hproper Q X hQX hX
  let eP : P ≃* X := e.subgroupMap P
  let ef : generalizedFitting P ≃* generalizedFitting X :=
    ((generalizedFitting P).equivMapOfInjective eP.toMonoidHom eP.injective).trans
      (MulEquiv.subgroupCongr (map_generalizedFitting_equiv eP))
  exact Group.isSolvable_of_isSolvable_injective (f := ef.toMonoidHom) ef.injective
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
