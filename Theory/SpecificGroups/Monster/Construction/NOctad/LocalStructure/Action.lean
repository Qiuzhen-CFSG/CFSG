module

public import Theory.SpecificGroups.Monster.Construction.NOctad.ExtensionInterface
public import Theory.SpecificGroups.Monster.Construction.LocalC.Action
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeInvariance

/-!
# The literal local action on the octad summand

The Leech isometry of every element of `N1` is monomial: its collected
normal form is a sign change followed by a Golay coordinate permutation.
It therefore preserves the weight-eight short-vector family. Equivariance
of the fixed lattice comparison transfers this to actual short lifts,
including their central signs, and hence to their span `octadSpace`.

The resulting representation is the restriction of `LocalC.cShort` through
`n1ToC`. Its inclusion intertwines the actual Griess representation. This
also identifies the local restriction required by `ExtendsLocal`; it does
not construct an extension to all of `N`.

Source: Aschbacher, *Sporadic Groups*, Section 27 and Lemma 29.13,
printed pp. 144–151 and 160–161. Actions use the repository's left
conjugation convention `g * q * g⁻¹`.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer Atlas.Lattices

theorem n1Leech_monomial (g : N1) :
    ∃ m : GolayMonomialGroup, monomialEmbedding m = n1LeechRepresentation g := by
  obtain ⟨⟨d, e, α⟩, rfl⟩ := normalForm_bijective.surjective g
  refine ⟨SemidirectProduct.inr (parkerStandardProjection α) *
    SemidirectProduct.inl (Multiplicative.ofAdd e.1), ?_⟩
  rw [map_mul, n1LeechRepresentation_normalForm]
  exact congrArg₂ (· * ·) (congrArg (fun f : Mathieu24CodeModel →* LeechIsometryGroup => f _) monomial_inr)
    (congrArg (fun f : Multiplicative golay →* LeechIsometryGroup => f _) monomial_inl)

theorem cShortLift_n1_val (g : N1) (q : ShortLift sourceLatticeComparison) :
    (cShortLift (n1ToC g) q).val = q1ImageConjugation g q.val := by
  change cConjugation (pullbackToC (n1Pullback g)) q.val = _
  rw [cConjugation_pullback]
  rfl

theorem cShortLift_n1_class (g : N1) (q : ShortLift sourceLatticeComparison) :
    shortLiftClass sourceLatticeComparison (cShortLift (n1ToC g) q) =
      shortClassRepresentation (n1LeechRepresentation g)
        (shortLiftClass sourceLatticeComparison q) := by
  apply Subtype.ext
  exact (congrArg (latticeClass sourceLatticeComparison) (cShortLift_n1_val g q)).trans
    (latticeClass_equivariant g q.val)

theorem cShortLift_n1_octad (g : N1) (p : OctadParameters) :
    ∃ p' : OctadParameters, rOctad p' = cShortLift (n1ToC g) (rOctad p) := by
  apply octad_exhaustion
  refine ⟨shellPermutation (n1LeechRepresentation g) 4 (octadShell p), ?_, ?_⟩
  · rw [shortReduction_transport, cShortLift_n1_class, rOctad_class]
  · obtain ⟨m, hm⟩ := n1Leech_monomial g
    change ((n1LeechRepresentation g).val (octadRepresentative p.c p.J)).val ∈ _
    rw [← hm]
    exact Atlas.Conway.monomial_twoFour_invariant m _ 8 0 (octadRepresentative_mem p)

theorem octadSpace_stable (g : N1) (v : BShort) (hv : v ∈ octadSpace) :
    cShort (n1ToC g) v ∈ octadSpace := by
  have h : octadSpace ≤ octadSpace.comap (cShort (n1ToC g)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', hp'⟩ := cShortLift_n1_octad g p
    change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOctad p)) ∈ octadSpace
    rw [cShort_vector, ← hp']
    exact Submodule.subset_span ⟨p', rfl⟩
  exact h hv

/-- Restriction of the actual local short action. -/
def representation : Representation ℝ N1 NOctad.Space where
  toFun g := (cShort (n1ToC g)).restrict (octadSpace_stable g)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change cShort (n1ToC 1) v.val = v.val
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change cShort (n1ToC (g * h)) v.val =
      cShort (n1ToC g) (cShort (n1ToC h) v.val)
    rw [map_mul, map_mul]
    rfl

@[simp] theorem representation_val (g : N1) (v : NOctad.Space) :
    (representation g v).val = cShort (n1ToC g) v.val := rfl

theorem representation_inclusion (g : N1) (v : NOctad.Space) :
    inclusion (representation g v) = cRepresentation (n1ToC g) (inclusion v) := by
  rw [cRepresentation_apply]
  change (0, cShort (n1ToC g) v.val, 0) =
    ((n1ToC g).val 0, cShort (n1ToC g) v.val, cSymmetric (n1ToC g) 0)
  simp only [map_zero]

theorem representation_vector (g : N1) (p : OctadParameters) :
    ∃ p' : OctadParameters, representation g (vector p) = vector p' ∧
      q1ImageConjugation g (rOctad p).val = (rOctad p').val := by
  obtain ⟨p', hp'⟩ := cShortLift_n1_octad g p
  refine ⟨p', ?_, ?_⟩
  · apply Subtype.ext
    change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOctad p)) = _
    rw [cShort_vector, ← hp']
    rfl
  · exact (cShortLift_n1_val g (rOctad p)).symm.trans (congrArg Subtype.val hp'.symm)

theorem extendsLocal_iff (ρ : Representation ℝ N NOctad.Space) :
    ExtendsLocal ρ ↔ ∀ g : N1, ρ g.val = representation g := by
  constructor
  · intro h g
    apply LinearMap.ext
    intro v
    apply inclusion_injective
    rw [h g, representation_inclusion]
  · intro h g v
    rw [h g]
    exact representation_inclusion g v

theorem representation_gamma (g : N1) (v w : NOctad.Space) :
    gamma (representation g v) (representation g w) = gamma v w :=
  cShort_form (n1ToC g) v.val w.val

theorem representation_beta (g : N1) (v w u : NOctad.Space) :
    beta (representation g v) (representation g w) (representation g u) = beta v w u := by
  rw [← beta_inclusion, representation_inclusion, representation_inclusion,
    representation_inclusion, ← beta_inclusion]
  exact CInvariance.cRepresentation_beta (n1ToC g) (inclusion v) (inclusion w) (inclusion u)

end Sporadic.Monster.Construction.NOctad.LocalStructure
