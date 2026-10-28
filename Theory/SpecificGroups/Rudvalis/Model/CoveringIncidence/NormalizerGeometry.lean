module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.ProductSylow
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.LocalSubgroups
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.SylowPlacement
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.MultiplierAction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
public import Theory.GroupTheory.SylowKernelCore

/-!
# Intrinsic incidence for a Rudvalis component Sylow subgroup

The ambient centralizer of the marked eight-group is the intrinsic max4
core, using the checked ambient normalizer bound and the independent
full-image calculation. Consequently an embedded E₄ × Syl₂(Sz(8)) whose
derived eight-group is a conjugate of that mark lies in the same conjugate
of the core. Its derived subgroup and order-seven actor are transported
together, retaining the literal core, center and quotient maps.

Source: GLS3, Table 5.3r, pp.291–292; Aschbacher–Smith I.2.2(7), pp.412–413.
The conjugacy of the derived eight-group and the cubic component-normalizer
extension still require separate model proofs. No covering-group incidence
or splitting conclusion is assumed here.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry
open Subgroup SylowOvergroups CoreQuotients
open SylowOvergroups.RadicalCoverage.LocalCover
open BenderSuzuki.MatrixGroups Theory.GroupTheory

/-- The full ambient centralizer, not only its intersection with max4,
is the intrinsic max4 core. -/
public theorem centralizer_eight_eq_core
    (hfull : Function.Surjective max4EightAction) :
    centralizer (elementary 2 : Set Model) = max4Core := by
  have hle : centralizer (elementary 2 : Set Model) ≤ max4 :=
    (centralizer_le_normalizer _).trans (max4NormalizerBounds 2 (by decide) (by decide))
  have he := congrArg (fun H : Subgroup max4 => H.map max4.subtype)
    (max4_centralizer_eq_pCore_of_full_image hfull)
  rw [map_subgroupOf_eq_of_le hle] at he
  exact he

/-- The intrinsic core of a literal conjugate max4 is the conjugate core. -/
public theorem conjugateMax4_core (g : Model) :
    (conjugateMax4 g).pCoreIn 2 = max4Core.map (MulAut.conj g).toMonoidHom :=
  (map_pCoreIn_of_injective 2 max4 _ (MulAut.conj g).injective).symm

/-- Its embedded intrinsic center uses the same conjugation. -/
public theorem conjugateMax4_core_center (g : Model) :
    (center ((conjugateMax4 g).pCoreIn 2)).map ((conjugateMax4 g).pCoreIn 2).subtype =
      max4CoreCenter.map (MulAut.conj g).toMonoidHom := by
  rw [conjugateMax4_core, ← map_embeddedCenter _ _ (MulAut.conj g).injective]
  rfl

/-- Identifying the derived eight-group gives the required core containment;
no independently prescribed ambient Sylow is moved. -/
public theorem sylowImage_le_conjugate_core
    {E : Type} [Group E] (f : E × SuzukiMatrixGroup 1 →* Model)
    (hfull : Function.Surjective max4EightAction) (g : Model)
    (hmark : derivedImage f = (elementary 2).map (MulAut.conj g).toMonoidHom) :
    sylowImage f ≤ (conjugateMax4 g).pCoreIn 2 := by
  rw [conjugateMax4_core, ← centralizer_eight_eq_core hfull]
  intro x hx
  have hc := sylowImage_centralizes_derived f hx
  rw [hmark] at hc
  refine ⟨(MulAut.conj g).symm x, ?_, (MulAut.conj g).apply_symm_apply x⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  apply (MulAut.conj g).injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using
    mem_centralizer_iff.mp hc ((MulAut.conj g) v) (mem_map_of_mem _ hv)

/-- Once the independent core-center calculation is supplied, the embedded
derived subgroup is exactly the center of the same intrinsic core. -/
public theorem sylowImage_derived_eq_conjugate_core_center
    {E : Type} [Group E] [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) (g : Model)
    (hcenter : max4CoreCenter = elementary 2)
    (hmark : derivedImage f = (elementary 2).map (MulAut.conj g).toMonoidHom) :
    ⁅sylowImage f, sylowImage f⁆ =
      (center ((conjugateMax4 g).pCoreIn 2)).map ((conjugateMax4 g).pCoreIn 2).subtype := by
  rw [sylowImage_derived, conjugateMax4_core_center, hcenter, hmark]

/-- The seven actor acts freely on the literal core center in this incidence. -/
public theorem seven_actor_on_conjugate_core_center
    {E : Type} [Group E] (f : E × SuzukiMatrixGroup 1 →* Model)
    (hf : Function.Injective f) (g : Model)
    (hcenter : max4CoreCenter = elementary 2)
    (hmark : derivedImage f = (elementary 2).map (MulAut.conj g).toMonoidHom) :
    ∃ a : Model, a ∈ f.range ∧ orderOf a = 7 ∧
      a ∈ normalizer (sylowImage f : Set Model) ∧
      ∀ v ∈ (center ((conjugateMax4 g).pCoreIn 2)).map
        ((conjugateMax4 g).pCoreIn 2).subtype, Commute a v → v = 1 := by
  rw [conjugateMax4_core_center, hcenter, ← hmark]
  exact exists_seven_actor f hf

/-- Conditional assembly of the literal normalizer Sylow and max4 incidence.
The odd normalizer index and conjugacy of its derived eight-group are the two
remaining ambient inputs; the centralizer structure alone is not claimed to
prove them. -/
public theorem exists_compatible_normalizer_sylow
    {E : Type} [Group E] [IsElementaryAbelian 2 E]
    (C I : Subgroup Model) (e : C ≃* E × SuzukiMatrixGroup 1)
    (hE : Nat.card E = 4)
    (hCN : C ≤ normalizer (I : Set Model))
    (hodd : ¬ 2 ∣ C.relIndex (normalizer (I : Set Model)))
    (hfull : Function.Surjective max4EightAction)
    (hcenter : max4CoreCenter = elementary 2)
    (hmark : ∃ g : Model, derivedImage (centralizerEmbedding C e) =
      (elementary 2).map (MulAut.conj g).toMonoidHom) :
    ∃ (g : Model) (R : Sylow 2 (normalizer (I : Set Model))),
      let T := (R : Subgroup (normalizer (I : Set Model))).map
        (normalizer (I : Set Model)).subtype
      let P := (conjugateMax4 g).pCoreIn 2
      let V := (center P).map P.subtype
      T = sylowImage (centralizerEmbedding C e) ∧ T ≤ P ∧ ⁅T, T⁆ = V ∧
      Nat.card T = 256 ∧ Nat.card (Abelianization T) = 32 ∧
      IsElementaryAbelian 2 (Abelianization T) ∧
      ∃ a : Model, a ∈ C ∧ orderOf a = 7 ∧ a ∈ normalizer (T : Set Model) ∧
        ∀ v ∈ V, Commute a v → v = 1 := by
  obtain ⟨g, hg⟩ := hmark
  obtain ⟨R, hR⟩ := exists_overgroupSylow C (normalizer (I : Set Model)) e hE hCN hodd
  refine ⟨g, R, ?_⟩
  dsimp only
  rw [hR]
  let f := centralizerEmbedding C e
  have hf := centralizerEmbedding_injective C e
  refine ⟨rfl, sylowImage_le_conjugate_core f hfull g hg,
    sylowImage_derived_eq_conjugate_core_center f g hcenter hg,
    sylowImage_card hE f hf, sylowImage_abelianization_card hE f hf,
    sylowImage_abelianization_elementary f, ?_⟩
  obtain ⟨a, ⟨x, rfl⟩, ha, hn, hv⟩ :=
    seven_actor_on_conjugate_core_center f hf g hcenter hg
  exact ⟨f x, (e.symm x).property, ha, hn, hv⟩

/-- The field comparison controls the parent's exact multiplier homomorphism. -/
public theorem normalizerMultiplierAction_eq_field
    {I : Subgroup Model} [IsQuasisimple I]
    {U : Type} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (e : I ≃* SuzukiMatrixGroup 1) (y : normalizer (I : Set Model))
    (hy : I.normalizerMonoidHom y = MulAut.congr e.symm (suzukiFieldAutomorphism 1)) :
    normalizerMultiplierAction f hf y =
      Covering.multiplierAction f hf (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) := by
  change Covering.multiplierAction f hf (I.normalizerMonoidHom y) = _
  rw [hy]

end Rudvalis.CoveringIncidence.NormalizerGeometry
