module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.Representation.BinaryPermutation
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The binary duad module and its natural submodule

The fifteen duads are the nonzero vectors of the existing binary symplectic
four-space. Evaluation of its nondegenerate alternating form gives the linear
embedding `v ↦ (d ↦ (v, d))` into the permutation module. For a nonzero vector
this is precisely the indicator of the complement of its perpendicular space.
The map is equivariant, and its image has dimension four.

The sum of the three line-complement indicators through a point is its
perpendicular-complement indicator. Thus the embedded natural module lies in
the line-complement span, which lies in the even-weight core. Isometries permute
the isotropic lines, so this middle space is an actual invariant submodule.
Transitivity on nonzero vectors also proves irreducibility of the natural action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3,
printed pp.343–345; the duad coordinates and polar geometry are from I.5.4–9.
The identification of these spaces with radical powers is a separate theorem.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation
namespace BinaryDuadModule

noncomputable def naturalAction : Representation (ZMod 2) S6 NaturalModule where
  toFun := polarLinearMap
  map_one' := by apply LinearMap.ext; intro v; exact polarAction_one v
  map_mul' g h := by apply LinearMap.ext; intro v; exact polarAction_mul g h v

noncomputable def pointAction : Representation (ZMod 2) S6 (Full Duad) :=
  (representation Duad).comp (MulAction.toPermHom S6 Duad)

noncomputable abbrev alternatingNaturalAction := naturalAction.comp A6.subtype
noncomputable abbrev alternatingPointAction := pointAction.comp A6.subtype

def complementMap : NaturalModule →ₗ[ZMod 2] Full Duad where
  toFun v d := polarForm v (polarVector d).val
  map_add' v w := by ext d; simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c v := by ext d; simp

@[simp] theorem complementMap_apply (v : NaturalModule) (d : Duad) :
    complementMap v d = polarForm v (polarVector d).val := rfl

theorem complementMap_injective : Function.Injective complementMap := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  apply polarForm_nondegenerate.1
  intro w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨w, hw⟩
  have he : (polarVector d).val = w := congrArg Subtype.val hd
  rw [← he]
  exact congrFun hv d

theorem complementMap_equivariant (g : S6) (v : NaturalModule) :
    complementMap (naturalAction g v) = pointAction g (complementMap v) := by
  ext d
  change polarForm (polarAction g v) (polarVector d).val =
    polarForm v (polarVector (g⁻¹ • d)).val
  rw [← polarAction_form g v (polarVector (g⁻¹ • d)).val,
    polarAction_vector, smul_inv_smul]

noncomputable def complementSubrepresentation : Subrepresentation alternatingPointAction where
  toSubmodule := complementMap.range
  apply_mem_toSubmodule g v hv := by
    obtain ⟨w, rfl⟩ := hv
    exact ⟨alternatingNaturalAction g w, complementMap_equivariant g.val w⟩

noncomputable def complementEquiv : NaturalModule ≃ₗ[ZMod 2]
    complementSubrepresentation.toSubmodule :=
  LinearEquiv.ofInjective complementMap complementMap_injective

theorem complementEquiv_equivariant (g : A6) (v : NaturalModule) :
    complementEquiv (alternatingNaturalAction g v) =
      complementSubrepresentation.toRepresentation g (complementEquiv v) := by
  apply Subtype.ext
  exact complementMap_equivariant g.val v

theorem complementSubrepresentation_finrank :
    Module.finrank (ZMod 2) complementSubrepresentation.toSubmodule = 4 := by
  rw [← complementEquiv.finrank_eq]
  exact naturalModule_finrank

def pointComplement (d : Duad) : Full Duad := complementMap (polarVector d).val

theorem pointComplement_apply (d e : Duad) :
    pointComplement d e = if d = e ∨ duadCollinear d e then 0 else 1 := by
  change polarForm (polarVector d).val (polarVector e).val = _
  have h := polarVector_orthogonal d e
  split_ifs with hc
  · exact h.mpr hc
  · have hn := mt h.mp hc
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact (hb _).resolve_left hn

theorem mem_complementSubrepresentation (u : Full Duad) :
    u ∈ complementSubrepresentation ↔ u = 0 ∨ ∃ d, u = pointComplement d := by
  constructor
  · rintro ⟨v, rfl⟩
    by_cases hv : v = 0
    · left; simp [hv]
    · obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
      exact Or.inr ⟨d, congrArg complementMap (congrArg Subtype.val hd).symm⟩
  · rintro (rfl | ⟨d, rfl⟩)
    · exact complementMap.range.zero_mem
    · exact ⟨(polarVector d).val, rfl⟩

def lineComplement (s : Syntheme) : Full Duad :=
  fun d => if incident d s then 0 else 1

def lineComplementSpan : Submodule (ZMod 2) (Full Duad) :=
  Submodule.span (ZMod 2) (Set.range lineComplement)

theorem lineComplement_mem_core (s : Syntheme) : lineComplement s ∈ core Duad := by
  change (∑ d : Duad, lineComplement s d) = 0
  fin_cases s <;> decide

theorem lineComplementSpan_le_core : lineComplementSpan ≤ core Duad := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact lineComplement_mem_core s

theorem pointComplement_eq_sum (d : Duad) :
    pointComplement d =
      ∑ s ∈ Finset.univ.filter (fun s => incident d s), lineComplement s := by
  fin_cases d <;> decide

theorem complementSubrepresentation_le_lineComplementSpan :
    complementSubrepresentation.toSubmodule ≤ lineComplementSpan := by
  intro u hu
  rcases (mem_complementSubrepresentation u).mp hu with rfl | ⟨d, rfl⟩
  · exact lineComplementSpan.zero_mem
  rw [pointComplement_eq_sum]
  apply Submodule.sum_mem
  intro s hs
  exact Submodule.subset_span (Set.mem_range_self s)

theorem alternatingNaturalAction_irreducible : Representation.IsIrreducible alternatingNaturalAction := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  by_cases hz : P = ⊥
  · exact Or.inl hz
  right
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.eq_top_iff'.mpr
  have hP : P.toSubmodule ≠ ⊥ := by
    intro h
    exact hz (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  intro w
  by_cases hw : w = 0
  · exact hw ▸ P.toSubmodule.zero_mem
  obtain ⟨g, hg⟩ := a6_polarPoint_transitive ⟨v, hne⟩ ⟨w, hw⟩
  have he : alternatingNaturalAction g v = w := by
    change polarAction g.val v = w
    exact (polarAction_point g.val ⟨v, hne⟩).trans (congrArg Subtype.val hg)
  exact he ▸ P.apply_mem_toSubmodule g hv

end BinaryDuadModule
namespace BinaryDuadModule
open Theory.SpecificGroups.SymmetricSix BinaryPermutation

private theorem permuted_line (g : S6) (s : Syntheme) :
    ∃ t : Syntheme, ∀ d : Duad, incident (g • d) t ↔ incident d s := by
  let W := (polarLine s).map (naturalAction g)
  have hd : Module.finrank (ZMod 2) W = 2 := by
    exact ((LinearMap.GeneralLinearGroup.toLinearEquiv
      (naturalAction.asGroupHom g)).finrank_map_eq (polarLine s)).trans (polarLine_finrank s)
  have hi : ∀ v ∈ W, ∀ w ∈ W, polarForm v w = 0 := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact (polarAction_form g v w).trans (polarLine_isotropic s v w hv hw)
  obtain ⟨t, ht⟩ := synthemePolarLine_surjective ⟨W, hd, hi⟩
  have he : polarLine t = W := congrArg Subtype.val ht
  refine ⟨t, fun d => ?_⟩
  rw [incident_iff_mem_polarLine, incident_iff_mem_polarLine, he,
    ← polarAction_vector]
  change naturalAction g (polarVector d).val ∈ (polarLine s).map (naturalAction g) ↔ _
  constructor
  · rintro ⟨v, hv, hvd⟩
    exact (naturalAction.apply_bijective g).1 hvd ▸ hv
  · exact Submodule.mem_map_of_mem

/-- The literal complements of isotropic lines are permuted by the group. -/
theorem pointAction_lineComplement (g : S6) (s : Syntheme) :
    ∃ t : Syntheme, pointAction g (lineComplement s) = lineComplement t := by
  obtain ⟨t, ht⟩ := permuted_line g s
  refine ⟨t, ?_⟩
  ext d
  have h := ht (g⁻¹ • d)
  rw [smul_inv_smul] at h
  change (if incident (g⁻¹ • d) s then (0 : ZMod 2) else 1) =
    if incident d t then 0 else 1
  simp only [h]

/-- The incidence span is an actual submodule for the full symmetric action. -/
theorem lineComplementSpan_invariant (g : S6) {u : Full Duad}
    (hu : u ∈ lineComplementSpan) : pointAction g u ∈ lineComplementSpan := by
  have h : lineComplementSpan ≤ lineComplementSpan.comap (pointAction g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := pointAction_lineComplement g s
    change pointAction g (lineComplement s) ∈ lineComplementSpan
    rw [ht]
    exact Submodule.subset_span (Set.mem_range_self t)
  exact h hu

/-- The middle space used in G.5.3, with its actual alternating action. -/
noncomputable def lineComplementSubrepresentation : Subrepresentation alternatingPointAction where
  toSubmodule := lineComplementSpan
  apply_mem_toSubmodule g _ hu := lineComplementSpan_invariant g.val hu

end BinaryDuadModule
