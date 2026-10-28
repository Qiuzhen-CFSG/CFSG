module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.Identification
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry.Centralizer
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Cubic geometry from the marked normalizer identification

The inverse of the supplied isomorphism embeds the explicit semidirect
product into G with image exactly N_G(R). Its marked root subgroup maps to
R, so its embedded center maps to E. Transporting the two cubic tori and
the x-axis gives every field of `SourceFrame.CubicGeometry`.

The final centralizer computation uses the image of the full model
centralizer, which is exactly C_G(t) ∩ N_G(R). Thus the order 48 result
requires no assertion about the order or structure of the whole C_G(t).
The only additional input to a returning pair is the marked normalizer
isomorphism; constructing that isomorphism remains with its source owner.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, the proof of 46.14,
and the beginning of 47.1, printed pp.251, 257–260.
-/

@[expose] public section
open Subgroup Matrix.PSL3Four
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
namespace SourceFrame.NormalizerIdentification
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {P : SourceFrame.ReturningPair D}
noncomputable section

def modelMap (I : SourceFrame.NormalizerIdentification P) : RootNormalizerModel.Model →* G :=
  (normalizer (P.R : Set G)).subtype.comp I.equiv.symm.toMonoidHom

theorem modelMap_injective (I : SourceFrame.NormalizerIdentification P) :
    Function.Injective I.modelMap := Subtype.val_injective.comp I.equiv.symm.injective

theorem modelMap_range (I : SourceFrame.NormalizerIdentification P) :
    I.modelMap.range = normalizer (P.R : Set G) := by
  rw [modelMap, MonoidHom.range_comp,
    I.equiv.symm.toMonoidHom.range_eq_top_of_surjective I.equiv.symm.surjective,
    ← MonoidHom.range_eq_map,
    range_subtype]

theorem root_modelMap (I : SourceFrame.NormalizerIdentification P) :
    RootNormalizerModel.root.map I.modelMap = P.R := by
  rw [modelMap, ← map_map, ← I.root_eq]
  have h : ((P.R.subgroupOf (normalizer (P.R : Set G))).map I.equiv.toMonoidHom).map
      I.equiv.symm.toMonoidHom = P.R.subgroupOf (normalizer (P.R : Set G)) := by
    rw [map_map]
    have hc : I.equiv.symm.toMonoidHom.comp I.equiv.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact congrArg Subtype.val (I.equiv.symm_apply_apply x)
    rw [hc, map_id]
  rw [h, map_subgroupOf_eq_of_le le_normalizer]

theorem E_modelMap (I : SourceFrame.NormalizerIdentification P) :
    RootNormalizerModel.Cubic.E.map I.modelMap = P.E := by
  rw [← RootNormalizerModel.Cubic.E_center, map_embeddedCenter _ _ I.modelMap_injective,
    I.root_modelMap]
  exact I.E_center

private theorem map_relative_centralizer {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (R X : Subgroup A) :
    (R ⊓ centralizer (X : Set A)).map f =
      R.map f ⊓ centralizer (X.map f : Set B) := by
  ext y
  constructor
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro z ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg f (hc b hb)
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    intro b hb
    apply hf
    simpa only [map_mul] using hc (f b) ⟨b, hb, rfl⟩

private theorem map_element_centralizer {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (t : A) :
    (centralizer ({t} : Set A)).map f = centralizer ({f t} : Set B) ⊓ f.range := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, ⟨a, rfl⟩⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)
  · rintro ⟨ha, ⟨a, rfl⟩⟩
    refine ⟨a, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply hf
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp ha

private theorem map_transitive {A B : Type*} [Group A] [Group B]
    (f : A →* B) (X V : Subgroup A)
    (h : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ x : X, (x : A) * u * (x : A)⁻¹ = v) :
    ∀ u ∈ V.map f, u ≠ 1 → ∀ v ∈ V.map f, v ≠ 1 →
      ∃ x : X.map f, (x : B) * u * (x : B)⁻¹ = v := by
  rintro u ⟨a, ha, rfl⟩ ha1 v ⟨b, hb, rfl⟩ hb1
  have ha' : a ≠ 1 := fun h => ha1 (by simp [h])
  have hb' : b ≠ 1 := fun h => hb1 (by simp [h])
  obtain ⟨x, hx⟩ := h a ha ha' b hb hb'
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_⟩
  simpa only [map_mul, map_inv] using congrArg f hx

/-- Transport all cubic geometry through the actual full-normalizer isomorphism. -/
theorem cubicGeometry (I : SourceFrame.NormalizerIdentification P) :
    Nonempty (SourceFrame.CubicGeometry P) := by
  let f := I.modelMap
  have hf : Function.Injective f := I.modelMap_injective
  have hr : RootNormalizerModel.root.map f = P.R := I.root_modelMap
  have he : RootNormalizerModel.Cubic.E.map f = P.E := I.E_modelMap
  refine ⟨{
    U := RootNormalizerModel.Cubic.U.map f
    X1 := RootNormalizerModel.Cubic.X1.map f
    X3 := RootNormalizerModel.Cubic.X3.map f
    R_card := ?_
    E_center := I.E_center
    U_card := ?_
    disjoint := ?_
    elementary := ?_
    join_le_R := ?_
    U_eq := ?_
    X1_card := ?_
    X1_normalizes := ?_
    X1_transitive := ?_
    X3_card := ?_
    X3_normalizes := ?_
    X3_centralizes := ?_
    X3_transitive := ?_
    normalizer_intersection_card := ?_ }⟩
  · rw [← hr, card_map_of_injective hf]
    exact RootNormalizerModel.root_card
  · rw [card_map_of_injective hf]
    exact RootNormalizerModel.Cubic.U_card
  · rw [← he]
    exact disjoint_map hf RootNormalizerModel.Cubic.disjoint
  · rw [← he, ← Subgroup.map_sup]
    let _ := RootNormalizerModel.Cubic.elementary
    exact IsElementaryAbelian.map f
  · rw [← he, ← hr, ← Subgroup.map_sup]
    exact map_mono RootNormalizerModel.Cubic.join_le_root
  · rw [← hr, ← map_relative_centralizer f hf, RootNormalizerModel.Cubic.U_eq]
  · rw [card_map_of_injective hf]
    exact RootNormalizerModel.Cubic.X1_card
  · rw [← he]
    exact (map_mono RootNormalizerModel.Cubic.X1_normalizes).trans
      (RootNormalizerModel.Cubic.E.le_normalizer_map f)
  · rw [← he]
    exact map_transitive f _ _ RootNormalizerModel.Cubic.X1_transitive
  · rw [card_map_of_injective hf]
    exact RootNormalizerModel.Cubic.X3_card
  · exact (map_mono RootNormalizerModel.Cubic.X3_normalizes).trans
      (RootNormalizerModel.Cubic.U.le_normalizer_map f)
  · rw [← he]
    rintro g ⟨a, ha, rfl⟩ y (hy | hy)
    · rcases hy with ⟨b, hb, rfl⟩
      simpa only [map_mul] using congrArg f
        (RootNormalizerModel.Cubic.X3_centralizes ha b (Or.inl hb))
    · rcases hy with ⟨b, hb, rfl⟩
      simpa only [map_mul] using congrArg f
        (RootNormalizerModel.Cubic.X3_centralizes ha b (Or.inr hb))
  · exact map_transitive f _ _ RootNormalizerModel.Cubic.X3_transitive
  · rintro t ⟨a, ha, rfl⟩ ht
    have ha1 : a ≠ 1 := fun h => ht (by simp [h])
    rw [← I.modelMap_range, ← map_element_centralizer f hf,
      card_map_of_injective hf]
    exact RootNormalizerModel.Cubic.centralizer_card a ha ha1

end
end SourceFrame.NormalizerIdentification
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
