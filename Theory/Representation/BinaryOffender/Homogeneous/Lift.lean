module

public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.IrreducibleQuotientDiagonal

/-!
# Lifting simple central images by commutators

Let q : V → V/C_V(X), let W be X-invariant, and let A ≤ q(W) be a simple
subrepresentation with [A,X] = A. Put E = W ∩ q⁻¹(A) and I = [E,X].
Equivariance gives q(I) = A. Thus E ≤ I + C_V(X), and taking commutators
again proves [I,X] = I. The simple image then makes I/C_I(X) irreducible.
A normalizer preserving W and A preserves this canonical lift as well.

No complement to the fixed space, global augmentation identity, or
semisimplicity of W is assumed. This supplies the quotient-lifting step in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma A.1.42(2),
1 March 2004 manuscript, printed p.32.
-/

@[expose] public section

namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem le_sup_fixedSpace_of_quotientImage_le {X : Subgroup G}
    {I J : Submodule (ZMod 2) V}
    (h : I.map (fixedSpace ρ X).mkQ ≤ J.map (fixedSpace ρ X).mkQ) :
    I ≤ J ⊔ fixedSpace ρ X := by
  intro v hv
  obtain ⟨j, hj, he⟩ := h ⟨v, hv, rfl⟩
  have hz : v - j ∈ fixedSpace ρ X := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ X).mkQ (v - j) = 0
    rw [map_sub, he, sub_self]
  exact Submodule.mem_sup.mpr ⟨j, hj, v - j, hz, by abel⟩

/-- Adding fixed vectors does not enlarge action commutators. -/
theorem commutator_le_of_le_sup_fixed {X : Subgroup G}
    {I J : Submodule (ZMod 2) V} (h : I ≤ J ⊔ fixedSpace ρ X) :
    subspaceCommutator ρ I X ≤ subspaceCommutator ρ J X := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, v, hv, rfl⟩
  obtain ⟨j, hj, z, hz, rfl⟩ := Submodule.mem_sup.mp (h hv)
  rw [map_add, show ρ x z = z from hz ⟨x, hx⟩, add_sub_add_right_eq_sub]
  exact Submodule.subset_span ⟨x, hx, j, hj, rfl⟩

/-- Commutators commute with the literal fixed-space quotient map. -/
theorem commutator_quotientImage (X : Subgroup G) (I : Submodule (ZMod 2) V) :
    (subspaceCommutator ρ I X).map (fixedSpace ρ X).mkQ =
      subspaceCommutator (fixedQuotientRepresentation ρ X)
        (I.map (fixedSpace ρ X).mkQ) ⊤ := by
  symm
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using subspaceCommutator_map_embedding
    (fixedQuotientRepresentation ρ X) ρ X.subtype (fixedSpace ρ X).mkQ
    (fun _ _ => rfl) ⊤ I

/-- A full-commutator subspace with simple central image is in Irr⁺. -/
theorem isIrrPlus_of_irreducible_image {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : X ≤ subspaceStabilizer ρ I) (hfull : subspaceCommutator ρ I X = I)
    (hirr : IsIrreducible (quotientImage ρ X I hI).toRepresentation) :
    IsIrrPlus ρ X I := by
  have hatom := (Subrepresentation.irreducible_iff_isAtom _).mp hirr
  apply isIrrPlus_of_minimal ρ hI hfull
  · intro hfix
    apply hatom.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    rintro _ ⟨v, hv, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hfix hv)
  · intro J hJ hJI
    by_cases hfix : J ≤ fixedSpace ρ X
    · exact Or.inr hfix
    · left
      have hne : quotientImage ρ X J hJ ≠ ⊥ := by
        intro he
        apply hfix
        intro v hv
        have hm : (fixedSpace ρ X).mkQ v ∈ (quotientImage ρ X J hJ).toSubmodule :=
          ⟨v, hv, rfl⟩
        rw [he] at hm
        exact (Submodule.Quotient.mk_eq_zero _).mp hm
      have he := (hatom.le_iff_eq hne).mp (Submodule.map_mono hJI)
      apply le_antisymm hJI
      apply le_of_quotientImage_le ρ hfull hJ
      exact (congrArg Subrepresentation.toSubmodule he).ge

/-- The preimage of a central-image subrepresentation inside a prescribed
invariant ambient subspace. -/
noncomputable def centralPreimage (X : Subgroup G) (W : Submodule (ZMod 2) V)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) : Submodule (ZMod 2) V :=
  W ⊓ A.toSubmodule.comap (fixedSpace ρ X).mkQ

/-- The canonical lift removes the central part by taking commutators. -/
noncomputable def commutatorLift (X : Subgroup G) (W : Submodule (ZMod 2) V)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) : Submodule (ZMod 2) V :=
  subspaceCommutator ρ (centralPreimage ρ X W A) X

theorem centralPreimage_invariant {X : Subgroup G} {W : Submodule (ZMod 2) V}
    (hW : X ≤ subspaceStabilizer ρ W)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    X ≤ subspaceStabilizer ρ (centralPreimage ρ X W A) := by
  apply le_subspaceStabilizer
  intro x hx v hv
  exact ⟨(hW hx v).2 hv.1, A.apply_mem_toSubmodule ⟨x,hx⟩ hv.2⟩

theorem centralPreimage_image {X : Subgroup G} {W : Submodule (ZMod 2) V}
    {A : Subrepresentation (fixedQuotientRepresentation ρ X)}
    (hA : A.toSubmodule ≤ W.map (fixedSpace ρ X).mkQ) :
    (centralPreimage ρ X W A).map (fixedSpace ρ X).mkQ = A.toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hv.2
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hA hv
    exact ⟨w, ⟨hw,hv⟩, rfl⟩

theorem commutatorLift_image {X : Subgroup G} {W : Submodule (ZMod 2) V}
    {A : Subrepresentation (fixedQuotientRepresentation ρ X)}
    (hA : A.toSubmodule ≤ W.map (fixedSpace ρ X).mkQ)
    (hfull : subspaceCommutator (fixedQuotientRepresentation ρ X) A.toSubmodule ⊤ =
      A.toSubmodule) :
    (commutatorLift ρ X W A).map (fixedSpace ρ X).mkQ = A.toSubmodule := by
  rw [commutatorLift, commutator_quotientImage, centralPreimage_image ρ hA, hfull]

theorem commutatorLift_le {X : Subgroup G} {W : Submodule (ZMod 2) V}
    (hW : X ≤ subspaceStabilizer ρ W)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    commutatorLift ρ X W A ≤ W :=
  (subspaceCommutator_le_of_invariant ρ (centralPreimage_invariant ρ hW A)).trans inf_le_left

theorem commutatorLift_full {X : Subgroup G} {W : Submodule (ZMod 2) V}
    {A : Subrepresentation (fixedQuotientRepresentation ρ X)}
    (hA : A.toSubmodule ≤ W.map (fixedSpace ρ X).mkQ)
    (hfull : subspaceCommutator (fixedQuotientRepresentation ρ X) A.toSubmodule ⊤ =
      A.toSubmodule) :
    subspaceCommutator ρ (commutatorLift ρ X W A) X = commutatorLift ρ X W A := by
  apply le_antisymm (subspaceCommutator_le_of_invariant ρ
    (subspaceCommutator_invariant ρ _ _))
  apply commutator_le_of_le_sup_fixed ρ
  apply le_sup_fixedSpace_of_quotientImage_le ρ
  change (centralPreimage ρ X W A).map (fixedSpace ρ X).mkQ ≤
    (commutatorLift ρ X W A).map (fixedSpace ρ X).mkQ
  rw [centralPreimage_image ρ hA, commutatorLift_image ρ hA hfull]

theorem commutatorLift_isIrrPlus {X : Subgroup G} {W : Submodule (ZMod 2) V}
    {A : Subrepresentation (fixedQuotientRepresentation ρ X)}
    (hA : A.toSubmodule ≤ W.map (fixedSpace ρ X).mkQ)
    (hfull : subspaceCommutator (fixedQuotientRepresentation ρ X) A.toSubmodule ⊤ =
      A.toSubmodule) (hirr : IsIrreducible A.toRepresentation) :
    IsIrrPlus ρ X (commutatorLift ρ X W A) := by
  apply isIrrPlus_of_irreducible_image ρ
    (subspaceCommutator_invariant ρ _ _) (commutatorLift_full ρ hA hfull)
  have he : quotientImage ρ X (commutatorLift ρ X W A)
      (subspaceCommutator_invariant ρ _ _) = A :=
    Subrepresentation.toSubmodule_injective (commutatorLift_image ρ hA hfull)
  change IsIrreducible (quotientImage ρ X (commutatorLift ρ X W A)
    (subspaceCommutator_invariant ρ _ _)).toRepresentation
  rwa [he]

/-- A normalizer acting on the prescribed ambient space and selected central
image also acts on its canonical Irr⁺ lift. -/
theorem commutatorLift_invariant_normalizer {X R : Subgroup G}
    {W : Submodule (ZMod 2) V}
    (A : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hR : R ≤ Subgroup.normalizer X) (hW : R ≤ subspaceStabilizer ρ W)
    (hA : ∀ r : R, ∀ v ∈ A.toSubmodule,
      normalizerQuotientRepresentation ρ X ⟨r, hR r.property⟩ v ∈ A.toSubmodule) :
    R ≤ subspaceStabilizer ρ (commutatorLift ρ X W A) := by
  apply subspaceCommutator_invariant_normalizer ρ _ hR
  apply le_subspaceStabilizer
  intro r hr v hv
  exact ⟨(hW hr v).2 hv.1, hA ⟨r,hr⟩ _ hv.2⟩
end Representation.BinaryOffender.Homogeneous
