module

public import Theory.Representation.BinaryOffender.Homogeneous.Selection
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# Homogeneous Irr⁺ selection and orbit decomposition

The odd simple-copy count and the inertia action select a homogeneous simple
image in V/C_V(X). Its canonical commutator lift inside the original orbit
span is an Irr⁺ member. Full commutator generation also makes equality of
central images detect equality of the original subspaces, giving the inertia
criterion on I itself. The distinct conjugate images are independent and
pairwise nonisomorphic, and sum to the literal image of the orbit span.

These results need only a normalizing two-group; the source additionally
assumes that it is Sylow and that X = O²(X). The faithful perfect-actor
corollary supplies the homogeneous member used by the later FF arguments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Lemma A.1.42, printed p.32 (PDF p.43).
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A two-group orbit of an Irr⁺ seed contains a genuinely homogeneous Irr⁺ member. -/
theorem exists_isIrrPlusWith_le_orbitSpan [FiniteDimensional (ZMod 2) V]
    {X T : Subgroup G} (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    ∃ J : Submodule (ZMod 2) V, J ≤ orbitSpan ρ T I ∧ IsIrrPlusWith ρ X T J := by
  obtain ⟨A, _, hA, hirr, hfull, hhom⟩ := exists_homogeneous_centralImage ρ hT hP
    (quotientImage ρ X I hI.choose) (quotientImage_irreducible ρ hI)
    (quotientImage_full ρ hI)
  have hle : A.toSubmodule ≤ (orbitSpan ρ T I).map (fixedSpace ρ X).mkQ := by
    rwa [orbitSpan_quotientImage ρ X T hT]
  exact ⟨commutatorLift ρ X (orbitSpan ρ T I) A,
    commutatorLift_le ρ (orbitSpan_component_invariant ρ hT hI) A,
    commutatorLift_isIrrPlusWith ρ hT hle hfull hirr hhom⟩

/-- A right conjugate fixes the central image of an Irr⁺ member exactly when it stabilizes the original member. -/
theorem centralRightConjugate_quotientImage_eq_iff {X T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer X) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (t : T) :
    centralRightConjugate ρ X T hT (quotientImage ρ X I hI.choose) t =
      quotientImage ρ X I hI.choose ↔ (t : G) ∈ subspaceStabilizer ρ I := by
  have ht := hI.map_normalizer ρ (hT (T.inv_mem t.property))
  have he : (centralRightConjugate ρ X T hT
      (quotientImage ρ X I hI.choose) t).toSubmodule =
      (I.map (ρ (t : G)⁻¹)).map (fixedSpace ρ X).mkQ := by
    rw [centralRightConjugate_toSubmodule]
    exact (quotientImage_map_normalizer ρ X I ⟨(t : G)⁻¹, hT (T.inv_mem t.property)⟩).symm
  constructor
  · intro h
    have hq : (I.map (ρ (t : G)⁻¹)).map (fixedSpace ρ X).mkQ =
        I.map (fixedSpace ρ X).mkQ := he.symm.trans (congrArg Subrepresentation.toSubmodule h)
    have hm : I.map (ρ (t : G)⁻¹) = I := le_antisymm
      (le_of_quotientImage_le ρ ht.choose_spec.1 hI.choose hq.le)
      (le_of_quotientImage_le ρ hI.choose_spec.1 ht.choose hq.ge)
    exact (subspaceStabilizer ρ I).inv_mem_iff.mp ((subspace_map_eq_iff ρ I _).mp hm)
  · intro h
    apply Subrepresentation.toSubmodule_injective
    rw [he, (subspace_map_eq_iff ρ I _).mpr ((subspaceStabilizer ρ I).inv_mem h)]
    rfl

/-- The actual X-type inertia stabilizes I if and only if I is homogeneous in its orbit span. -/
theorem inertia_stabilizes_iff_isIrrPlusWith {X T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer X) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) :
    (∀ t ∈ centralInertia ρ X T hT (quotientImage ρ X I hI.choose),
      (t : G) ∈ subspaceStabilizer ρ I) ↔ IsIrrPlusWith ρ X T I := by
  have hc := central_homogeneous_iff_inertia_fixes ρ X T hT
    (quotientImage ρ X I hI.choose) (quotientImage_irreducible ρ hI)
  constructor
  · intro h
    refine ⟨hT, hI.choose, hI, ?_⟩
    rw [orbitSpan_quotientImage ρ X T hT]
    exact hc.mpr (fun t ht => (centralRightConjugate_quotientImage_eq_iff ρ hT hI t).mpr (h t ht))
  · intro h t ht
    apply (centralRightConjugate_quotientImage_eq_iff ρ hT hI t).mp
    apply hc.mp _ t ht
    change homogeneousPart (quotientImage ρ X I hI.choose)
      (centralOrbitSpan ρ X T hT (I.map (fixedSpace ρ X).mkQ)) =
        I.map (fixedSpace ρ X).mkQ
    rw [← orbitSpan_quotientImage ρ X T hT]
    exact h.homogeneous

/-- The defining homogeneous equality, expressed using the action on the literal central quotient. -/
theorem IsIrrPlusWith.central_homogeneous {X T : Subgroup G}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ X T I) :
    homogeneousPart (quotientImage ρ X I hI.invariant)
      (centralOrbitSpan ρ X T hI.normalizes (I.map (fixedSpace ρ X).mkQ)) =
        I.map (fixedSpace ρ X).mkQ := by
  rw [← orbitSpan_quotientImage ρ X T hI.normalizes]
  exact hI.homogeneous

/-- All distinct right-conjugate central images form an independent, pairwise nonisomorphic family whose sum is the image of the orbit span. -/
theorem IsIrrPlusWith.orbit_decomposition {X T : Subgroup G}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ X T I) :
    let S := quotientImage ρ X I hI.invariant
    let Ω := centralOrbit ρ X T hI.normalizes S
    iSupIndep (fun A : Ω => A.val.toSubmodule) ∧
      (⨆ A : Ω, A.val.toSubmodule) = (orbitSpan ρ T I).map (fixedSpace ρ X).mkQ ∧
      ∀ A B : Ω, A ≠ B → ¬ SameModule A.val B.val := by
  have hirr := quotientImage_irreducible ρ hI.isIrrPlus
  have hhom := hI.central_homogeneous ρ
  refine ⟨centralOrbit_independent ρ X T hI.normalizes _ hirr hhom, ?_,
    centralOrbit_not_sameModule ρ X T hI.normalizes _ hirr hhom⟩
  rw [centralOrbit_iSup, orbitSpan_quotientImage ρ X T hI.normalizes]
  rfl

/-- A faithful binary action of a nontrivial perfect subgroup supplies a homogeneous Irr⁺ member for every normalizing two-group. -/
theorem exists_isIrrPlusWith_of_faithful [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ) (X T : Subgroup G) [Group.IsPerfect X]
    (hX : X ≠ ⊥) (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T) :
    ∃ I : Submodule (ZMod 2) V, IsIrrPlusWith ρ X T I := by
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful ρ hfaith X hX
  obtain ⟨J, _, hJ⟩ := exists_isIrrPlusWith_le_orbitSpan ρ hT hP hI
  exact ⟨J, hJ⟩

end Representation.BinaryOffender.Homogeneous
