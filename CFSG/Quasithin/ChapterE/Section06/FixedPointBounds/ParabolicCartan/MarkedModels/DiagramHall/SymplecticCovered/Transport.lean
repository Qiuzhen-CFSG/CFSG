module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.Reduction

/-!
# The original overlap and the central symplectic cover

The comparison X/O₂(X) → X/J restricts to the component images. E.2.2's
literal `kernel_center` clause puts its kernel in the center. The marked
Borel pulls back to the image of M ∩ K, because J ≤ M. The map from the
original overlap onto that preimage has two-group kernel.

These facts keep the two quotients distinct and supply the actual maps
needed to apply a central-cover Borel calculation to 4.4.13.
Source: Aschbacher--Smith, `refs/quasithin.pdf`, E.2.2(2), pp.215--216,
and 4.4.13, pp.623--624.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
open ChapterB
variable {X : Type*} [Group X]

/-- Restrict the canonical comparison X/O₂(X) → X/J to the component images. -/
noncomputable def actorToSource (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) : actorImage K →* sourceImage (minimalParabolicMax S hP) K :=
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel (minimalParabolicMax S hP))
    (MonoidHom.id X) (twoCore_le_sourceKernel S hP)
  (q.comp (actorImage K).subtype).codRestrict _ (by
    rintro ⟨x, k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩)

/-- Both component images have the same representatives in K. -/
theorem actorToSource_surjective (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) : Function.Surjective (actorToSource S hP K) := by
  rintro ⟨x, k, hk, rfl⟩
  exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k, k, hk, rfl⟩, rfl⟩

/-- The source center equality makes the comparison kernel central. -/
theorem actorToSource_central (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} (hc : SingleClauses (minimalParabolicMax S hP) K S) :
    (actorToSource S hP K).ker ≤ center (actorImage K) := by
  intro a ha
  obtain ⟨k, hk, hka⟩ := a.property
  have hkj : k ∈ sourceKernel (minimalParabolicMax S hP) := by
    apply (QuotientGroup.eq_one_iff k).mp
    have hh := congrArg Subtype.val ha
    change QuotientGroup.map (pCore 2 X) (sourceKernel (minimalParabolicMax S hP))
      (MonoidHom.id X) (twoCore_le_sourceKernel S hP) a.val = 1 at hh
    rw [← hka] at hh
    exact hh
  have hz : a.val ∈ (center (actorImage K)).map (actorImage K).subtype := by
    rw [← hc.kernel_center]
    exact ⟨k, hkj, hka⟩
  obtain ⟨z, hz, hza⟩ := hz
  exact (show z = a from Subtype.ext hza) ▸ hz

/-- Compose the canonical comparison with the supplied derived-model marking. -/
noncomputable def actorToModel (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F) :
    actorImage K →* Sp4Derived F := e.toMonoidHom.comp (actorToSource S hP K)

/-- The model comparison is onto the literal commutator-of-Sp₄ carrier. -/
theorem actorToModel_surjective (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F) :
    Function.Surjective (actorToModel S hP e) :=
  e.surjective.comp (actorToSource_surjective S hP K)

/-- The component in X/O₂(X) is a central cover of the marked model. -/
theorem actorToModel_central (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F) :
    (actorToModel S hP e).ker ≤ center (actorImage K) := by
  intro a ha
  apply actorToSource_central S hP hc
  exact e.injective (ha.trans e.map_one.symm)

private theorem sourceOverlap_iff {M K : Subgroup X} (k : K) :
    QuotientGroup.mk' (sourceKernel M) k.val ∈ sourceImage M (M ⊓ K) ↔ k.val ∈ M := by
  constructor
  · rintro ⟨x, hx, hxk⟩
    have hd : x / k.val ∈ sourceKernel M := QuotientGroup.eq_iff_div_mem.mp hxk
    have hh := M.mul_mem (M.inv_mem (M.normalCore_le hd)) hx.1
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_one] using hh
  · intro hk
    exact ⟨k.val, ⟨hk, k.property⟩, rfl⟩

/-- The marking detects membership in the original maximal subgroup. -/
theorem model_mem_borel_iff (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) (k : K) :
    actorToModel S hP e ⟨QuotientGroup.mk' (pCore 2 X) k.val, k.val, k.property, rfl⟩ ∈
      sp4DerivedBorel F ↔ k.val ∈ minimalParabolicMax S hP := by
  rw [← he]
  change e (actorToSource S hP K _) ∈ _ ↔ _
  exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).trans (sourceOverlap_iff k)

/-- Map the original overlap to the inverse Borel in the central cover. -/
noncomputable def overlapToCover (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) : K.subgroupOf (minimalParabolicMax S hP) →*
        (sp4DerivedBorel F).comap (actorToModel S hP e) :=
  let q : K.subgroupOf (minimalParabolicMax S hP) →* actorImage K :=
    (((QuotientGroup.mk' (pCore 2 X)).comp (minimalParabolicMax S hP).subtype).comp
      (K.subgroupOf (minimalParabolicMax S hP)).subtype).codRestrict _
        (fun b => ⟨b.val.val, b.property, rfl⟩)
  q.codRestrict _ (fun b => (model_mem_borel_iff S hP e he ⟨b.val.val, b.property⟩).mpr
    b.val.property)

/-- Every element of the inverse Borel lifts to the original overlap. -/
theorem overlapToCover_surjective (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) : Function.Surjective (overlapToCover S hP e he) := by
  intro a
  obtain ⟨k, hk, hka⟩ := a.val.property
  have hka' : (⟨QuotientGroup.mk' (pCore 2 X) k, k, hk, rfl⟩ : actorImage K) = a.val :=
    Subtype.ext hka
  have hkM : k ∈ minimalParabolicMax S hP := by
    apply (model_mem_borel_iff S hP e he ⟨k, hk⟩).mp
    rw [hka']
    exact a.property
  exact ⟨⟨⟨k, hkM⟩, hk⟩, Subtype.ext hka'⟩

/-- The remaining kernel embeds in O₂(X). -/
theorem overlapToCover_kernel_two (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {F : Type*} [Field F]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) : IsPGroup 2 (overlapToCover S hP e he).ker := by
  let j : (overlapToCover S hP e he).ker →* pCore 2 X :=
    ((minimalParabolicMax S hP).subtype.comp
      ((K.subgroupOf (minimalParabolicMax S hP)).subtype.comp
        (overlapToCover S hP e he).ker.subtype)).codRestrict _ (by
          intro b
          apply (QuotientGroup.eq_one_iff b.val.val.val).mp
          exact congrArg (fun z => z.val.val) b.property)
  exact pCore_isPGroup.of_injective j (by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 X => z.val) hab))))

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
