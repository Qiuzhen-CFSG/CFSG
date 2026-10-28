module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Nongeneration

/-!
# The S₄--S₄ local pair is excluded in the actual A₇ carrier

The source triple already supplies a common ambient Sylow subgroup and
ambient generation. The intrinsic seven-point calculation places any two
S₄ subgroups containing that Sylow in a proper point, block or Fano-plane
stabilizer. This contradicts the original generation equation.

Source: Aschbacher--Smith F.6.18, printed p.310, the explicit nongeneration
observation for the A₇ local inspection.
-/

public section
open Subgroup Equiv
namespace CFSG.Quasithin.ChapterF.SourceAssembly

/-- A literal Goldschmidt triple on A₇ cannot have two S₄ vertices. -/
theorem not_alternatingSeven_symmetricFour_pair
    {G₁ G₂ : Subgroup (alternatingGroup (Fin 7))}
    (h : IsGoldschmidtTriple G₁ G₂)
    (e₁ : G₁ ≃* Perm (Fin 4)) (e₂ : G₂ ≃* Perm (Fin 4)) : False := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  exact AlternatingSeven.DihedralLocals.symmetricFour_pair_not_generate T G₁ G₂
    (hT ▸ inf_le_left) (hT ▸ inf_le_right) e₁ e₂ h.generated

/-- Transport the actual supplied A₇ model and both original vertices,
retaining their common ambient Sylow and their generation equation. -/
theorem not_alternatingSeven_model_symmetricFour_pair
    {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) (eG : G ≃* alternatingGroup (Fin 7))
    (e₁ : G₁ ≃* Perm (Fin 4)) (e₂ : G₂ ≃* Perm (Fin 4)) : False := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  let S := T.mapSurjective (f := eG.toMonoidHom) eG.surjective
  have hS₁ : (S : Subgroup (alternatingGroup (Fin 7))) ≤ G₁.map eG.toMonoidHom :=
    map_mono (hT ▸ inf_le_left)
  have hS₂ : (S : Subgroup (alternatingGroup (Fin 7))) ≤ G₂.map eG.toMonoidHom :=
    map_mono (hT ▸ inf_le_right)
  apply AlternatingSeven.DihedralLocals.symmetricFour_pair_not_generate S
    (G₁.map eG.toMonoidHom) (G₂.map eG.toMonoidHom) hS₁ hS₂
    ((eG.subgroupMap G₁).symm.trans e₁) ((eG.subgroupMap G₂).symm.trans e₂)
  rw [← Subgroup.map_sup, h.generated, map_top_of_surjective _ eG.surjective]

/-- The literal central quotient excludes the S₄--S₄ case also for the
triple cover of A₇; the original quotient map remains the projection. -/
theorem not_alternatingSeven_central_quotient_symmetricFour_pair
    {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) (eG : (G ⧸ center G) ≃* alternatingGroup (Fin 7))
    (e₁ : G₁ ≃* Perm (Fin 4)) (e₂ : G₂ ≃* Perm (Fin 4)) : False := by
  let f := eG.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hf : Function.Surjective f :=
    eG.surjective.comp (QuotientGroup.mk'_surjective (center G))
  have hk : f.ker ≤ center G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact eG.injective (hx.trans (map_one eG).symm)
  obtain ⟨T, hT⟩ := h.intersection_sylow
  exact AlternatingSeven.DihedralLocals.central_cover_symmetricFour_pair_not_generate
    f hf hk T G₁ G₂ (hT ▸ inf_le_left) (hT ▸ inf_le_right) e₁ e₂ h.generated

end CFSG.Quasithin.ChapterF.SourceAssembly
