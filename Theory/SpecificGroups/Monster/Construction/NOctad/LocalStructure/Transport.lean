module
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Action
public import Theory.SpecificGroups.Monster.Construction.NOctad.Basis

/-!
# Octad block transport and the genuine stabilizer action

The unique Golay monomial lift of the `N1` Leech action supplies its actual
coordinate permutation. The support of an octad shell representative is
unchanged by signs and transported by that permutation. Short reduction
identifies representatives only up to global sign, so it retains precisely
this support information. Spanning then gives equality of the transported
blocks, including the reverse containment by the inverse actor.

The coordinate stabilizer is proved equal to the subspace stabilizer. Its
block representation is the literal restriction, with the Griess inclusion
equation and a relative-kernel criterion on actual `Q1Image` elements.
No extraspecial or alternating quotient assertion is assumed here.

Source: Aschbacher, *Sporadic Groups*, 29.12–29.13, printed pp. 160–161.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer Atlas.Lattices

/-- The actual monomial lift of the `N1` Leech action. -/
def monomialRepresentation : N1 →* GolayMonomialGroup where
  toFun g := (n1Leech_monomial g).choose
  map_one' := by
    apply monomialEmbedding_injective
    rw [(n1Leech_monomial 1).choose_spec, map_one, map_one]
  map_mul' g h := by
    apply monomialEmbedding_injective
    rw [(n1Leech_monomial (g * h)).choose_spec, map_mul, map_mul,
      (n1Leech_monomial g).choose_spec, (n1Leech_monomial h).choose_spec]

@[simp] theorem monomialRepresentation_embedding (g : N1) :
    monomialEmbedding (monomialRepresentation g) = n1LeechRepresentation g :=
  (n1Leech_monomial g).choose_spec

/-- The coordinate permutation supplied by the literal Leech action. -/
def coordinateRepresentation : N1 →* Mathieu24CodeModel :=
  SemidirectProduct.rightHom.comp monomialRepresentation

/-- Transport of the actual weight-eight Golay word. -/
def octadTransport (g : N1) (c : Octad) : Octad :=
  ⟨golayPermutationEquiv (coordinateRepresentation g) c.val,
    (coordinatePermutation_weight _ _).trans c.prop⟩

@[simp] theorem octadTransport_apply (g : N1) (c : Octad) (i : Omega) :
    (octadTransport g c).val.val ((coordinateRepresentation g).val i) = c.val.val i :=
by
  change c.val.val ((coordinateRepresentation g).val.symm ((coordinateRepresentation g).val i)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem octadTransport_one (c : Octad) : octadTransport 1 c = c := by
  apply Subtype.ext
  change golayPermutationEquiv (coordinateRepresentation 1) c.val = c.val
  rw [map_one]
  rfl

@[simp] theorem octadTransport_mul (g h : N1) (c : Octad) :
    octadTransport (g * h) c = octadTransport g (octadTransport h c) := by
  apply Subtype.ext
  change golayPermutationEquiv (coordinateRepresentation (g * h)) c.val = _
  rw [map_mul]
  rfl

theorem parameterOctad_transport (g : N1) (p p' : OctadParameters)
    (h : rOctad p' = cShortLift (n1ToC g) (rOctad p)) :
    parameterOctad p' = octadTransport g (parameterOctad p) := by
  have hc : shortReduction (octadShell p') =
      shortReduction (shellPermutation (n1LeechRepresentation g) 4 (octadShell p)) := by
    rw [← rOctad_class, h, cShortLift_n1_class, rOctad_class, shortReduction_transport]
  have hs := support_eq_of_reduction_eq _ _ hc 2
  change evenMagnitudeSupport (octadRepresentative p'.c p'.J).val 2 =
    evenMagnitudeSupport ((n1LeechRepresentation g).val (octadRepresentative p.c p.J)).val 2 at hs
  rw [← monomialRepresentation_embedding, Atlas.Conway.monomial_magnitude_support,
    octadRepresentative_two_support, octadRepresentative_two_support] at hs
  apply Subtype.ext
  apply Subtype.ext
  apply support_injective
  change support p'.c.1.val = support (coordinatePermutation
    (coordinateRepresentation g).val p.c.1.val)
  rw [coordinatePermutation_support]
  exact hs

theorem representation_vector_transport (g : N1) (p : OctadParameters) :
    ∃ p' : OctadParameters, representation g (vector p) = vector p' ∧
      parameterOctad p' = octadTransport g (parameterOctad p) := by
  obtain ⟨p', hp'⟩ := cShortLift_n1_octad g p
  refine ⟨p', ?_, parameterOctad_transport g p p' hp'⟩
  apply Subtype.ext
  change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOctad p)) = _
  rw [cShort_vector, ← hp']
  rfl

theorem representation_block_le (g : N1) (c : Octad) :
    (block c).map (representation g) ≤ block (octadTransport g c) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨p', hp', hc⟩ := representation_vector_transport g p
  change representation g (vector p) ∈ block (octadTransport g c)
  rw [hp', ← show parameterOctad p = c from Subtype.ext hp, ← hc]
  exact vector_mem_block p'

/-- `N1` permutes the source blocks by its actual coordinate permutation. -/
theorem representation_block (g : N1) (c : Octad) :
    (block c).map (representation g) = block (octadTransport g c) := by
  apply le_antisymm (representation_block_le g c)
  intro v hv
  have hi : representation g⁻¹ v ∈ block c := by
    have hm := representation_block_le g⁻¹ (octadTransport g c)
      (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
    simpa only [← octadTransport_mul, inv_mul_cancel, octadTransport_one] using hm
  refine Submodule.mem_map.mpr ⟨representation g⁻¹ v, hi, ?_⟩
  change (representation g * representation g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The exact block stabilizer in the actual local group. -/
def blockStabilizer (c : Octad) : Subgroup N1 where
  carrier := {g | octadTransport g c = c}
  one_mem' := octadTransport_one c
  mul_mem' := by
    intro g h hg hh
    change octadTransport g c = c at hg
    change octadTransport h c = c at hh
    change octadTransport (g * h) c = c
    rw [octadTransport_mul, hh, hg]
  inv_mem' := by
    intro g hg
    change octadTransport g c = c at hg
    change octadTransport g⁻¹ c = c
    have h := congrArg (octadTransport g⁻¹) hg
    simpa only [← octadTransport_mul, inv_mul_cancel, octadTransport_one] using h.symm

/-- The block action is a restriction of the already constructed local action. -/
def blockRepresentation (c : Octad) : Representation ℝ (blockStabilizer c) (block c) where
  toFun g := (representation g.val).restrict (fun v hv => by
    have h := representation_block_le g.val c (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
    have hg : octadTransport g.val c = c := g.prop
    simpa only [hg] using h)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change representation 1 v.val = v.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change representation (g.val * h.val) v.val = representation g.val (representation h.val v.val)
    rw [map_mul]
    rfl

@[simp] theorem blockRepresentation_val (c : Octad) (g : blockStabilizer c) (v : block c) :
    (blockRepresentation c g v).val = representation g.val v.val := rfl

theorem blockRepresentation_inclusion (c : Octad) (g : blockStabilizer c) (v : block c) :
    blockInclusion c (blockRepresentation c g v) =
      cRepresentation (n1ToC g.val) (blockInclusion c v) :=
  representation_inclusion g.val v.val

/-- Distinct support words give distinct nonzero blocks. -/
theorem block_injective : Function.Injective block := by
  intro c d h
  by_contra hcd
  let p := parameters c 0 0
  have hv : vector p ∈ block c := Submodule.subset_span ⟨p, rfl, rfl⟩
  have hz := block_orthogonal hcd hv (h ▸ hv)
  rw [gamma_vector_self] at hz
  exact one_ne_zero hz

/-- The coordinate stabilizer is exactly the stabilizer of the literal subspace. -/
theorem mem_blockStabilizer_iff (g : N1) (c : Octad) :
    g ∈ blockStabilizer c ↔ (block c).map (representation g) = block c := by
  change octadTransport g c = c ↔ _
  rw [representation_block]
  exact block_injective.eq_iff.symm

/-- Equality of acted signed vectors detects actual conjugation, not just the lattice class. -/
theorem representation_vector_eq_iff (g : N1) (p q : OctadParameters) :
    representation g (vector p) = vector q ↔
      q1ImageConjugation g (rOctad p).val = (rOctad q).val := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOctad p)) =
      shortVector sourceLatticeComparison (rOctad q) at hv
    rw [cShort_vector] at hv
    have hl := (shortLiftSigns sourceLatticeComparison).delta_injective hv
    exact (cShortLift_n1_val g (rOctad p)).symm.trans (congrArg Subtype.val hl)
  · intro h
    apply Subtype.ext
    change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOctad p)) =
      shortVector sourceLatticeComparison (rOctad q)
    rw [cShort_vector]
    congr 1
    apply Subtype.ext
    exact (cShortLift_n1_val g (rOctad p)).trans h

/-- The relative block kernel is detected by the actual octad elements in `Q1Image`. -/
theorem blockRepresentation_kernel_iff (c : Octad) (g : blockStabilizer c) :
    g ∈ (blockRepresentation c).ker ↔ ∀ p : OctadParameters, p.c.1 = c.val →
      q1ImageConjugation g.val (rOctad p).val = (rOctad p).val := by
  change blockRepresentation c g = 1 ↔ _
  constructor
  · intro h p hp
    have hv : vector p ∈ block c := Submodule.subset_span ⟨p, hp, rfl⟩
    apply (representation_vector_eq_iff g.val p p).mp
    exact congrArg (fun f : Module.End ℝ (block c) => (f ⟨vector p, hv⟩).val) h
  · intro h
    have hf : block c ≤ (representation g.val - LinearMap.id).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, hp, rfl⟩
      change representation g.val (vector p) - vector p = 0
      exact sub_eq_zero.mpr ((representation_vector_eq_iff g.val p p).mpr (h p hp))
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact sub_eq_zero.mp (hf v.prop)

end Sporadic.Monster.Construction.NOctad.LocalStructure
