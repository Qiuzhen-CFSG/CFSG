module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Six
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The six-letter parabolics in the actual derived symplectic group

The polar representation carries the duad stabilizer to the stabilizer
of a one-dimensional binary subspace, and the syntheme stabilizer to that
of an isotropic plane. Incidence with the fifteen duads proves the latter
identity on every vector, including zero. The two subspaces are nonzero
and proper and have dimensions one and two.

The same explicit S₆ ≃ Sp₄(2) equivalence restricts to A₆ ≃ Sp₄(2)′.
Conjugation commutes with these embeddings. Mapping the restricted
parabolic therefore gives the literal intersection of the geometric
parabolic with the derived subgroup. Combining this with the index-three
classification retains the supplied component equivalence throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, clause 15.3.49(l), and I.5, printed pp.419–422. The imported polar
representation and symplectic group order carry their original attribution.
-/

@[expose] public section

open Subgroup
open scoped Matrix
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Six
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Binary

noncomputable def polarPoint : Submodule (ZMod 2) NaturalModule :=
  Submodule.span (ZMod 2) {(polarVector 0).val}

theorem point_stabilizer :
    (stabilizer polarPoint).comap symmetricSixEquiv.toMonoidHom = duadStabilizer := by
  ext g
  rw [mem_comap, mem_stabilizer_iff]
  have hv : (polarVector 0).val ∈ polarPoint := Submodule.subset_span (by simp)
  have hfix : symmetricSixEquiv g • (polarVector 0).val = (polarVector 0).val ↔
      g ∈ duadStabilizer := by
    rw [symmetricSixEquiv_apply, smul_eq_mulVec, polarRepresentation_equivariant]
    rw [← Subtype.ext_iff, polarVector_injective.eq_iff]
    exact SetLike.ext_iff.mp duad_stabilizer_zero g
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h _ hv)
    have hb : a = 0 ∨ a = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases hb with rfl | rfl
    · simp only [zero_smul] at ha
      have hz := (toLinear (symmetricSixEquiv g)).injective
        (ha.symm.trans (map_zero _).symm)
      exact ((polarVector 0).property hz).elim
    · exact hfix.mp (by simpa using ha.symm)
  · intro hg v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    change toLinear (symmetricSixEquiv g) (a • (polarVector 0).val) ∈ polarPoint
    rw [map_smul, toLinear_apply, hfix.mpr hg]
    exact polarPoint.smul_mem a (Submodule.subset_span (by simp))

private theorem base_image :
    (synthemeDuads 0).image duadSet = baseSyntheme := by decide

private theorem duad_mem_base (d : Duad) :
    duadSet d ∈ baseSyntheme ↔ incident d 0 := by decide +revert

private theorem syntheme_mem_iff (g : S6) :
    g ∈ synthemeStabilizer ↔ ∀ d : Duad, incident d 0 → incident (g • d) 0 := by
  change baseSyntheme.image (fun t => t.image g) = baseSyntheme ↔ _
  constructor
  · intro hg d hd
    apply (duad_mem_base _).mp
    rw [duadSet_smul, ← hg]
    exact Finset.mem_image_of_mem _ ((duad_mem_base d).mpr hd)
  · intro h
    have hle : baseSyntheme.image (fun t => t.image g) ⊆ baseSyntheme := by
      apply Finset.image_subset_iff.mpr
      intro s hs
      rw [← base_image] at hs
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
      rw [← duadSet_smul]
      exact (duad_mem_base _).mpr (h d hd)
    apply Finset.eq_of_subset_of_card_le hle
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Finset.image_injective g.injective hab

theorem plane_stabilizer :
    (stabilizer (polarLine 0)).comap symmetricSixEquiv.toMonoidHom = synthemeStabilizer := by
  ext g
  rw [mem_comap, mem_stabilizer_iff, syntheme_mem_iff]
  constructor
  · intro h d hd
    apply (incident_iff_mem_polarLine _ _).mpr
    rw [← polarRepresentation_equivariant, ← symmetricSixEquiv_apply, ← smul_eq_mulVec]
    exact h _ ((incident_iff_mem_polarLine _ _).mp hd)
  · intro h v hv
    by_cases hz : v = 0
    · subst v
      change toLinear (symmetricSixEquiv g) 0 ∈ polarLine 0
      rw [map_zero]
      exact Submodule.zero_mem _
    · obtain ⟨d, hd⟩ := polarVector_bijective.surjective ⟨v, hz⟩
      have hdv : (polarVector d).val = v := congrArg Subtype.val hd
      rw [← hdv] at hv ⊢
      change symmetricSixEquiv g • (polarVector d).val ∈ polarLine 0
      rw [symmetricSixEquiv_apply, smul_eq_mulVec, polarRepresentation_equivariant]
      exact (incident_iff_mem_polarLine _ _).mp
        (h d ((incident_iff_mem_polarLine _ _).mpr hv))

noncomputable def markedSpace (i : Bool) : Submodule (ZMod 2) NaturalModule :=
  if i then polarLine 0 else polarPoint

def fullParabolic (i : Bool) : Subgroup S6 :=
  if i then synthemeStabilizer else duadStabilizer

theorem fullParabolic_map (i : Bool) :
    (fullParabolic i).map symmetricSixEquiv.toMonoidHom = stabilizer (markedSpace i) := by
  have he : fullParabolic i =
      (stabilizer (markedSpace i)).comap symmetricSixEquiv.toMonoidHom := by
    cases i
    · exact point_stabilizer.symm
    · exact plane_stabilizer.symm
  rw [he, map_comap_eq_self]
  rw [MonoidHom.range_eq_top.mpr (show Function.Surjective symmetricSixEquiv.toMonoidHom
    from symmetricSixEquiv.surjective)]
  exact le_top

theorem markedSpace_dimension (i : Bool) :
    Module.finrank (ZMod 2) (markedSpace i) = if i then 2 else 1 := by
  cases i
  · exact finrank_span_singleton (polarVector 0).property
  · exact polarLine_finrank 0

theorem markedSpace_proper (i : Bool) : markedSpace i ≠ ⊥ ∧ markedSpace i ≠ ⊤ := by
  constructor
  · intro h
    have hc := markedSpace_dimension i
    rw [h, finrank_bot] at hc
    cases i <;> simp at hc
  · intro h
    have hc := markedSpace_dimension i
    rw [h, finrank_top, naturalModule_finrank] at hc
    cases i <;> simp at hc

theorem markedSpace_isotropic (i : Bool) :
    ∀ v ∈ markedSpace i, ∀ w ∈ markedSpace i, polarForm v w = 0 := by
  cases i
  · intro v hv w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply,
      polarForm_alt, smul_zero, smul_zero]
  · intro v hv w hw
    exact polarLine_isotropic 0 v w hv hw

theorem alternating_image :
    A6.map symmetricSixEquiv.toMonoidHom = commutator (Sp (ZMod 2)) := by
  change (alternatingGroup Letter).map symmetricSixEquiv.toMonoidHom = _
  rw [← alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card Letter)]
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
    (show Function.Surjective symmetricSixEquiv.toMonoidHom from symmetricSixEquiv.surjective)]
  rfl

noncomputable def alternatingEquivDerived : A6 ≃* commutator (Sp (ZMod 2)) :=
  (symmetricSixEquiv.subgroupMap A6).trans (MulEquiv.subgroupCongr alternating_image)

theorem alternatingEquivDerived_apply (g : A6) :
    (alternatingEquivDerived g).val = symmetricSixEquiv g.val := rfl

theorem restricted_conjugate_image (R : Subgroup S6) (g : A6) :
    ((R.subgroupOf A6).map (MulAut.conj g).toMonoidHom).map A6.subtype =
      (R.map (MulAut.conj g.val).toMonoidHom) ⊓ A6 := by
  have hc : A6.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp A6.subtype := by ext x; rfl
  rw [map_map, hc, ← map_map, subgroupOf_map_subtype,
    map_inf _ _ _ (MulAut.conj g.val).injective]
  have ha : A6.map (MulAut.conj g.val).toMonoidHom = A6 :=
    mem_normalizer_iff_map_conj_eq.mp (A6.le_normalizer g.property)
  rw [ha]

theorem polar_restricted_conjugate_image (i : Bool) (g : A6) :
    (((fullParabolic i).subgroupOf A6).map (MulAut.conj g).toMonoidHom).map
      (symmetricSixEquiv.toMonoidHom.comp A6.subtype) =
      ((stabilizer (markedSpace i)).map
        (MulAut.conj (symmetricSixEquiv g.val)).toMonoidHom) ⊓
          commutator (Sp (ZMod 2)) := by
  rw [← map_map, restricted_conjugate_image,
    map_inf _ _ symmetricSixEquiv.toMonoidHom symmetricSixEquiv.injective, alternating_image]
  congr 1
  have hc : symmetricSixEquiv.toMonoidHom.comp (MulAut.conj g.val).toMonoidHom =
      (MulAut.conj (symmetricSixEquiv g.val)).toMonoidHom.comp
        symmetricSixEquiv.toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv]
  rw [map_map, hc, ← map_map, fullParabolic_map]

theorem derived_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* A6) (hs : CFSG.Quasithin.Chapter1.IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ (g : A6) (i : Bool),
      ((P.subgroupOf L).map e.toMonoidHom).map
        (symmetricSixEquiv.toMonoidHom.comp A6.subtype) =
      ((stabilizer (markedSpace i)).map
        (MulAut.conj (symmetricSixEquiv g.val)).toMonoidHom) ⊓
          commutator (Sp (ZMod 2)) := by
  obtain ⟨g, hg | hg⟩ := ambient_position L S P e hs hSP hPL hi
  · refine ⟨g, false, ?_⟩
    rw [hg]
    exact polar_restricted_conjugate_image false g
  · refine ⟨g, true, ?_⟩
    rw [hg]
    exact polar_restricted_conjugate_image true g

theorem derived_position_intrinsic {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* A6) (hs : CFSG.Quasithin.Chapter1.IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ (g : A6) (i : Bool),
      (P.subgroupOf L).map (e.trans alternatingEquivDerived).toMonoidHom =
        ((stabilizer (markedSpace i)).map
          (MulAut.conj (symmetricSixEquiv g.val)).toMonoidHom).subgroupOf
            (commutator (Sp (ZMod 2))) := by
  obtain ⟨g, i, h⟩ := derived_position L S P e hs hSP hPL hi
  refine ⟨g, i, ?_⟩
  apply map_injective (commutator (Sp (ZMod 2))).subtype_injective
  have hc : (commutator (Sp (ZMod 2))).subtype.comp
      (e.trans alternatingEquivDerived).toMonoidHom =
      (symmetricSixEquiv.toMonoidHom.comp A6.subtype).comp e.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hc, ← map_map, subgroupOf_map_subtype]
  exact h

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Six
