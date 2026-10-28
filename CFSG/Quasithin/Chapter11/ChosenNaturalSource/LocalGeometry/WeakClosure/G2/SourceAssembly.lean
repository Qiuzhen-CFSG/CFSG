module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Assembly

/-!
# The original plane-component input in the G₂ weak-closure assembly

Conjugation carries a relative noncentral C-component and its unique property
through the actual subgroup embeddings. The solvable residual commutes with
this transport. Hence source 11.1.3 on V₂ supplies the whole PlaneComponents
family, including arbitrary ambient conjugates. The two applications below
retain only that single earlier-source clause rather than a family of new
component assumptions.

The relative transport proofs follow LocalGeometry/Normalizers/PlaneOrbit;
that module keeps them private. B.4.6 root-plane construction and R₁
localization remain separate model obligations, owned by
qt-d-1222-natural-g2-model-geometry. This module does not discharge those
obligations or claim unconditional 11.2.2(5--6).

Source: Aschbacher--Smith, 11.1.3 and 11.2.2, printed pp.765,767--768.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
private theorem map_relative (e : G ≃* G) (H K : Subgroup G) :
    (K.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
  apply map_injective (H.map e.toMonoidHom).subtype_injective
  rw [map_map, subgroupOf_map_subtype]
  have he : (H.map e.toMonoidHom).subtype.comp (e.subgroupMap H).toMonoidHom =
      e.toMonoidHom.comp H.subtype := rfl
  rw [he, ← map_map, subgroupOf_map_subtype, map_inf _ _ _ e.injective]

private theorem component_map (e : G ≃* G) {H K : Subgroup G}
    (h : Source.ComponentIn H K) :
    Source.ComponentIn (H.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨map_mono h.1, ?_⟩
  have hm := h.2.map_equiv (e.subgroupMap H)
  rwa [map_relative] at hm

private theorem noncentral_map (e : G ≃* G) {H U K : Subgroup G}
    (h : Source.NoncentralComponent H U K) :
    Source.NoncentralComponent (H.map e.toMonoidHom)
      (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨component_map e h.1, ?_⟩
  intro hc
  apply h.2
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [map_commutator]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

private theorem unique_map (e : G ≃* G) {H U K : Subgroup G}
    (h : Source.UniqueNoncentralComponent H U K) :
    Source.UniqueNoncentralComponent (H.map e.toMonoidHom)
      (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨noncentral_map e h.1, ?_⟩
  intro J hJ
  have hj := noncentral_map e.symm hJ
  simp only [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from by ext x; exact e.symm_apply_apply x, map_id] at hj
  have he := congrArg (map e.toMonoidHom) (h.2 _ hj)
  simpa only [map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G from by ext x; exact e.apply_symm_apply x, map_id] using he

set_option backward.isDefEq.respectTransparency false in
private theorem residual_map [Finite G] (e : G ≃* G) (H : Subgroup G) :
    ((solvableResidual H).map H.subtype).map e.toMonoidHom =
      (solvableResidual (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype := by
  have he := congrArg (map (H.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq (e.subgroupMap H).toMonoidHom (e.subgroupMap H).surjective)
  rw [map_map] at he ⊢
  have hc : (H.map e.toMonoidHom).subtype.comp (e.subgroupMap H).toMonoidHom =
      e.toMonoidHom.comp H.subtype := rfl
  rw [hc] at he
  exact he

private theorem localResidual_map [Finite G] (e : G ≃* G) (L U : Subgroup G) :
    (localResidual L U).map e.toMonoidHom =
      localResidual (L.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  unfold localResidual
  rw [residual_map, map_inf _ _ _ e.injective, map_equiv_normalizer_eq]

/-- The single literal 11.1.3 assertion supplies all original and conjugate
planes in the root-plane reconstruction. No ambient normality is used. -/
theorem planeComponents_of_unique [Finite G] {L P : Subgroup G}
    (h : Source.UniqueNoncentralComponent (normalizer (P : Set G)) P
      (localResidual L P)) : PlaneComponents L P := by
  intro g U I hI
  obtain ⟨-, l, rfl⟩ := hI
  have hg := unique_map (MulAut.conj g) h
  rw [map_equiv_normalizer_eq, localResidual_map] at hg
  have hl := unique_map (MulAut.conj (l : G)) hg
  have hn : (L.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (l : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom :=
    mem_normalizer_iff_map_conj_eq.mp
      ((L.map (MulAut.conj g).toMonoidHom).le_normalizer l.property)
  rw [map_equiv_normalizer_eq, localResidual_map, hn] at hl
  exact hl

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 marking))
open ChapterE

/-- The actual 11.2.2(5--6) assembly with source 11.1.3 at the original V₂.
The B.4.6 root and localization inputs still require their model proofs. -/
theorem clauses_of_source_component
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hloc : R1FamilyLocalization D S f)
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S marking f g)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) :=
  clauses_of_geometry D S marking f hr hs (planeComponents_of_unique hcomponent)
    hthree hloc hroots

/-- The same single preceding component clause feeds the literal rank-one
R₁ consumer with both derived normalizer and centralizer bounds. -/
theorem rankOne_impossible_of_source_component
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hloc : R1FamilyLocalization D S f)
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S marking f g))
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False :=
  rankOne_impossible_of_root_planes D S marking f hr hs
    (planeComponents_of_unique hcomponent) hthree hloc hroots H₁ P hP hn hout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
