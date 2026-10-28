module

public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalLayers

/-!
# Literal invariant sections in the external cubic branch

For an ambient binary action with commuting K and S₃ images, generation by
cubic commutators passes to every actual invariant section D/(C ∩ D).
The inverter-fixed space supplies explicit equivariant pair and tensor
coordinates. The two summands are disjoint cubic conjugates. In particular,
such a section cannot be irreducible under K. Applied to I/C_I(K), this
excludes the ambient-invariant alternative F.9.18(4i) for an Irr⁺ constituent.

A classified identification of the multiplicity action constructs the
`NaturalLayers.TensorLayer` coordinates on that literal section, retaining
its component isomorphism. The multiplicity space is not asserted to be the
T-invariant FF constituent: that requires the remaining F.9.18/B.4.2 argument.
No module classification, Borel marking, central-section assertion or
fixed-space equality is assumed to be proved by these constructions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed pp.954–955, and F.9.18(4), printed pp.325–326.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

variable {G K V : Type*} [Group G] [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (f : K →* G) (s : S₃ →* G)
  (hs : ∀ k g, Commute (f k) (s g))
  (C D : Subrepresentation ρ)

/-- The literal invariant section; containment makes this D/C. -/
abbrev SectionSpace := D.toSubmodule ⧸ C.toSubmodule.comap D.toSubmodule.subtype

/-- Restriction of the actual upper space to the specified symmetric-three action. -/
def cubicUpper : Subrepresentation (ρ.comp s) where
  toSubmodule := D.toSubmodule
  apply_mem_toSubmodule g := D.apply_mem_toSubmodule (s g)

/-- The fixed-point-free cubic action passes through the actual quotient map. -/
theorem section_fixedFree
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    ∀ v, (sectionRepresentation ρ C D) (s cubic) v = v → v = 0 := by
  apply fixedFree_of_surjective (D.toRepresentation.comp s)
    ((sectionRepresentation ρ C D).comp s)
    (C.toSubmodule.comap D.toSubmodule.subtype).mkQ
    (Submodule.mkQ_surjective _) (fun _ => rfl)
  exact fixedFree_of_injective (ρ.comp s) (D.toRepresentation.comp s)
    D.toSubmodule.subtype D.toSubmodule.subtype_injective (fun _ => rfl)
    (ambient_fixedFree_of_commutator ρ s hgen)

/-- The multiplicity space of the section is the fixed space of the actual inverter. -/
abbrev SectionMultiplicity := multiplicitySpace ((sectionRepresentation ρ C D).comp s)

/-- K acts on this actual fixed space because it commutes with S₃. -/
def sectionMultiplicityAction : Representation (ZMod 2) K (SectionMultiplicity ρ s C D) :=
  multiplicity ((sectionRepresentation ρ C D).comp s)
    ((sectionRepresentation ρ C D).comp f)
    (ambient_commute (sectionRepresentation ρ C D) f s hs)

/-- Two copies of the same actual K-module give the section, with explicit inverse. -/
def sectionPairEquiv
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    (SectionMultiplicity ρ s C D × SectionMultiplicity ρ s C D) ≃ₗ[ZMod 2]
      SectionSpace ρ C D :=
  pairEquiv _ (section_fixedFree ρ s C D hgen)

/-- The pair decomposition respects the specified component embedding. -/
theorem sectionPairEquiv_equivariant
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (k : K) (a b : SectionMultiplicity ρ s C D) :
    sectionPairEquiv ρ s C D hgen
        (sectionMultiplicityAction ρ f s hs C D k a,
          sectionMultiplicityAction ρ f s hs C D k b) =
      sectionRepresentation ρ C D (f k) (sectionPairEquiv ρ s C D hgen (a,b)) :=
  pairEquiv_equivariant _ _ (ambient_commute (sectionRepresentation ρ C D) f s hs)
    _ k (a,b)

/-- The section is the direct sum of the inverter-fixed space and its cubic conjugate. -/
theorem section_two_conjugates
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    Disjoint (SectionMultiplicity ρ s C D)
        ((SectionMultiplicity ρ s C D).map (sectionRepresentation ρ C D (s cubic))) ∧
      SectionMultiplicity ρ s C D ⊔
        (SectionMultiplicity ρ s C D).map (sectionRepresentation ρ C D (s cubic)) = ⊤ := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro v ⟨hv, w, hw, he⟩
    let a : SectionMultiplicity ρ s C D := ⟨v, hv⟩
    let b : SectionMultiplicity ρ s C D := ⟨w, hw⟩
    have heq : sectionPairEquiv ρ s C D hgen (a,0) =
        sectionPairEquiv ρ s C D hgen (0,b) := by
      change pairEquiv _ _ (a,0) = pairEquiv _ _ (0,b)
      rw [pairEquiv_apply, pairEquiv_apply]
      simpa only [Submodule.coe_zero, map_zero, add_zero, zero_add, a, b,
        MonoidHom.comp_apply] using he.symm
    have ha := congrArg Prod.fst ((sectionPairEquiv ρ s C D hgen).injective heq)
    exact congrArg Subtype.val ha
  · apply top_unique
    intro v _
    obtain ⟨⟨a,b⟩, rfl⟩ := (sectionPairEquiv ρ s C D hgen).surjective v
    change pairEquiv _ _ (a,b) ∈ _
    rw [pairEquiv_apply]
    exact Submodule.mem_sup.mpr ⟨a, a.property, _, ⟨b, b.property, rfl⟩, rfl⟩

/-- Actual tensor coordinates for an arbitrary invariant section. -/
def sectionTensorEquiv
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    SectionMultiplicity ρ s C D ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
      SectionSpace ρ C D :=
  tensorEquiv _ (section_fixedFree ρ s C D hgen)

/-- The tensor coordinates intertwine both the component and the cubic actor. -/
theorem sectionTensorEquiv_equivariant
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (k : K) (g : S₃)
    (z : SectionMultiplicity ρ s C D ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :
    sectionTensorEquiv ρ s C D hgen
        (Representation.HigherFieldBorelFixedSpaces.externalTensor
          (sectionMultiplicityAction ρ f s hs C D)
          (BinaryPermutation.coreRepresentation (Fin 3)) (k,g) z) =
      sectionRepresentation ρ C D (f k * s g) (sectionTensorEquiv ρ s C D hgen z) :=
  ambient_tensorEquiv_equivariant (sectionRepresentation ρ C D) f s hs
    (section_fixedFree ρ s C D hgen) k g z

include hs in
/-- An inverted fixed-point-free cubic action commuting with K prevents K-irreducibility. -/
theorem not_irreducible_of_commuting_cubic
    (h : ∀ v, ρ (s cubic) v = v → v = 0) : ¬ IsIrreducible (ρ.comp f) := by
  intro hi
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  let I : Subrepresentation (ρ.comp f) :=
    { toSubmodule := multiplicitySpace (ρ.comp s)
      apply_mem_toSubmodule k v hv := by
        rw [mem_multiplicitySpace] at hv ⊢
        rw [← ambient_commute ρ f s hs, hv] }
  have hz : ∀ a : multiplicitySpace (ρ.comp s), a = 0 := by
    rcases eq_bot_or_eq_top I with hb | ht
    · intro a
      apply Subtype.ext
      have ha : a.val ∈ I.toSubmodule := a.property
      rw [hb] at ha
      exact ha
    · intro a
      have ha : (ρ.comp s) cubic a.val ∈ I.toSubmodule := by rw [ht]; trivial
      let b : multiplicitySpace (ρ.comp s) := ⟨_, ha⟩
      have he : pairEquiv (ρ.comp s) h (b,0) = pairEquiv (ρ.comp s) h (0,a) := by
        simp only [pairEquiv_apply, Submodule.coe_zero, map_zero, zero_add, add_zero]
        rfl
      exact (congrArg Prod.snd ((pairEquiv (ρ.comp s) h).injective he)).symm
  have hv : ∀ v : V, v = 0 := by
    intro v
    obtain ⟨⟨a,b⟩, rfl⟩ := (pairEquiv (ρ.comp s) h).surjective v
    rw [hz a, hz b]
    exact map_zero (pairEquiv (ρ.comp s) h)
  obtain ⟨v, hvne⟩ := exists_ne (0 : V)
  exact hvne (hv v)

include hs in
/-- This applies in particular to every H-chief section, before any classification. -/
theorem section_not_irreducible
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    ¬ IsIrreducible ((sectionRepresentation ρ C D).comp f) :=
  not_irreducible_of_commuting_cubic (sectionRepresentation ρ C D) f s hs
    (section_fixedFree ρ s C D hgen)

/-- The ambient-invariant alternative F.9.18(4i) is impossible for a member of Irr⁺.
Normality is required only in the group acting on this module. -/
theorem irrPlus_not_invariant (L : Subgroup G) [L.Normal]
    (hsL : ∀ (k : L) g, Commute (k : G) (s g))
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    ¬ (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I := by
  intro hstable
  let C : Subrepresentation ρ :=
    { toSubmodule := fixedSpace ρ L
      apply_mem_toSubmodule g v hv :=
        (fixedSpace_stable_of_normal ρ L (Subgroup.mem_top g) v).mpr hv }
  let D : Subrepresentation ρ :=
    { toSubmodule := I
      apply_mem_toSubmodule g v hv := (hstable (Subgroup.mem_top g) v).mpr hv }
  obtain ⟨hIL, _, hirr⟩ := hI
  have he : (sectionRepresentation ρ C D).comp L.subtype =
      centralQuotientRepresentation ρ L I hIL := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v => rfl
  apply section_not_irreducible ρ L.subtype s hsL C D hgen
  rw [he]
  exact hirr

variable {L N : Type*} [Group L] [AddCommGroup N] [Module (ZMod 2) N]
  (σ : Representation (ZMod 2) L N) (e : K ≃* L)
  (a : SectionMultiplicity ρ s C D ≃ₗ[ZMod 2] N)

/-- A classified multiplicity module gives tensor coordinates on the literal section. -/
def modelCoordinates
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    SectionSpace ρ C D ≃ₗ[ZMod 2] N ⊗[ZMod 2] BinaryPermutation.core (Fin 3) :=
  (sectionTensorEquiv ρ s C D hgen).symm.trans
    (TensorProduct.congr a (LinearEquiv.refl _ _))

/-- The component marking is retained by the constructed tensor coordinates. -/
theorem modelCoordinates_equivariant
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (ha : ∀ k v, a (sectionMultiplicityAction ρ f s hs C D k v) = σ (e k) (a v))
    (k : K) (v : SectionSpace ρ C D) :
    modelCoordinates ρ s C D a hgen (sectionRepresentation ρ C D (f k) v) =
      NaturalLayers.naturalTensor σ (e k) (modelCoordinates ρ s C D a hgen v) := by
  obtain ⟨z, rfl⟩ := (sectionTensorEquiv ρ s C D hgen).surjective v
  have heq := sectionTensorEquiv_equivariant ρ f s hs C D hgen k 1 z
  simp only [map_one, mul_one] at heq
  rw [← heq]
  simp only [modelCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change TensorProduct.congr a (LinearEquiv.refl _ _)
      (Representation.HigherFieldBorelFixedSpaces.externalTensor
        (sectionMultiplicityAction ρ f s hs C D)
        (BinaryPermutation.coreRepresentation (Fin 3)) (k,1) z) =
    NaturalLayers.naturalTensor σ (e k)
      (TensorProduct.congr a (LinearEquiv.refl _ _) z)
  clear heq
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul i n =>
    simp only [Representation.HigherFieldBorelFixedSpaces.externalTensor,
      NaturalLayers.naturalTensor, Representation.tprod_apply,
      MonoidHom.comp_apply, TensorProduct.map_tmul, TensorProduct.congr_tmul,
      MonoidHom.inl_apply, LinearEquiv.refl_apply, ha]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Construct the existing natural-layer API, rather than assuming its coordinates. -/
def tensorLayer
    (hCD : C ≤ D)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (ha : ∀ k v, a (sectionMultiplicityAction ρ f s hs C D k v) = σ (e k) (a v)) :
    NaturalLayers.TensorLayer (ρ.comp f) σ e C.toSubmodule D.toSubmodule where
  lower_le := hCD
  stable k d := D.apply_mem_toSubmodule (f k) d.property
  coordinates := modelCoordinates ρ s C D a hgen
  equivariant k d := modelCoordinates_equivariant ρ f s hs C D σ e a hgen ha k
    (Submodule.Quotient.mk d)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
