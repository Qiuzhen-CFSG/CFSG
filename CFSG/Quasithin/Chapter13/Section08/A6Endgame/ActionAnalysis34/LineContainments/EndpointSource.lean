module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.Sections
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.MarkedQuotient

/-!
# The marked source modules at the genuine endpoint

Inverse conjugation by the chosen `c.gb` identifies the endpoint star group
with H/O₂(H). Both the symmetric and alternating markings use precisely this
identification. Conjugation transports the original flag, its index, the
relative normalizer and noncentrality, and the specified plane parabolic.
Applying the source permutation-surjection theorem to these conjugated data
then gives a noncentral marked syntheme quotient on the literal Vγ/Uγ.

The actual section equivalences intertwine this star identification. In
particular the original natural or augmentation-cover comparison transports
to Uγ/A₁ without changing the marking. No transvection actor or line
containment is assumed or proved here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.4(5)
and the final paragraph of 13.8.34(1), printed pp.947,968 (PDF pp.964,985).
The original plane marking and original module comparison are inputs from
earlier source results; all endpoint transport is proved here.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments.EndpointSource
open CriticalGeometry CriticalGeometry.SectionActions
variable {G : Type*} [Group G] {L T H V : Subgroup G}
variable (c : CriticalPair L T H V)

abbrev conjugate (X : Subgroup G) : Subgroup G :=
  X.map (MulAut.conj (c.gb : G)).toMonoidHom

/-- Return an endpoint element to H by inverse conjugation by `c.gb`. -/
def actorEquiv : vertexGroup L T H c.gamma ≃* H :=
  (MulEquiv.subgroupCongr c.vertexGroup_gamma).trans
    ((MulAut.conj (c.gb : G)).subgroupMap H).symm

/-- The underlying map is the specified inverse ambient conjugation. -/
theorem actorEquiv_apply (j : vertexGroup L T H c.gamma) :
    (actorEquiv c j : G) = (MulAut.conj (c.gb : G)).symm (j : G) := rfl

theorem actorEquiv_eq_returnActor (j : vertexGroup L T H c.gamma) :
    actorEquiv c j = SectionActions.CriticalPair.returnActor c _ le_rfl j := rfl

theorem actorEquiv_conj (j : vertexGroup L T H c.gamma) :
    MulAut.conj (c.gb : G) (actorEquiv c j : G) = (j : G) :=
  SectionActions.CriticalPair.returnActor_conj c _ le_rfl j

/-- Inverse endpoint conjugation descends through the characteristic two-cores. -/
def starEquiv : Source.Hstar (vertexGroup L T H c.gamma) ≃* Source.Hstar H :=
  QuotientGroup.congr _ _ (actorEquiv c) (pCore_map_iso 2 (actorEquiv c))

/-- Formula for the endpoint star equivalence on actual group representatives. -/
theorem starEquiv_mk (j : vertexGroup L T H c.gamma) :
    starEquiv c (QuotientGroup.mk' (pCore 2 (vertexGroup L T H c.gamma)) j) =
      QuotientGroup.mk' (pCore 2 H) (actorEquiv c j) :=
  QuotientGroup.congr_mk' _ _ _ _ j

/-- The common endpoint marking, used for both S₆ and A₆. -/
def marking {A : Type*} [Group A] (e : Source.Hstar H ≃* A) :
    Source.Hstar (vertexGroup L T H c.gamma) ≃* A := (starEquiv c).trans e

/-- The model marking uses the very same returned endpoint representative. -/
theorem marking_mk {A : Type*} [Group A] (e : Source.Hstar H ≃* A)
    (j : vertexGroup L T H c.gamma) :
    marking c e (QuotientGroup.mk' (pCore 2 (vertexGroup L T H c.gamma)) j) =
      e (QuotientGroup.mk' (pCore 2 H) (actorEquiv c j)) := by
  change e (starEquiv c _) = _
  rw [starEquiv_mk]

/-- Star images of conjugated ambient subgroups return to the original images. -/
theorem starImage_conjugate (X : Subgroup G) :
    (Source.starImage (vertexGroup L T H c.gamma) (conjugate c X)).map
      (starEquiv c).toMonoidHom = Source.starImage H X := by
  ext a
  constructor
  · rintro ⟨b, ⟨j, hj, rfl⟩, rfl⟩
    change starEquiv c (QuotientGroup.mk' _ j) ∈ _
    rw [starEquiv_mk]
    refine ⟨actorEquiv c j, ?_, rfl⟩
    change (actorEquiv c j : G) ∈ X
    change (j : G) ∈ conjugate c X at hj
    have he := actorEquiv_conj c j
    rw [← he] at hj
    simpa only [MulEquiv.symm_apply_apply] using (mem_map_equiv.mp hj)
  · rintro ⟨h, hh, rfl⟩
    refine ⟨QuotientGroup.mk' (pCore 2 (vertexGroup L T H c.gamma))
      ((actorEquiv c).symm h), ?_, ?_⟩
    · refine ⟨(actorEquiv c).symm h, ?_, rfl⟩
      change ((actorEquiv c).symm h : G) ∈ conjugate c X
      rw [← actorEquiv_conj, (actorEquiv c).apply_symm_apply]
      exact mem_map_of_mem _ hh
    · change starEquiv c (QuotientGroup.mk' _ ((actorEquiv c).symm h)) = _
      rw [starEquiv_mk, (actorEquiv c).apply_symm_apply]

/-- Transport the original plane-parabolic marking, including the actual intersection. -/
theorem plane_marking {A : Type*} [Group A] (M : Subgroup G)
    (e : Source.Hstar H ≃* A) (K : Subgroup A)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = K) :
    (Source.starImage (vertexGroup L T H c.gamma)
      (vertexGroup L T H c.gamma ⊓ conjugate c M)).map
      (marking c e).toMonoidHom = K := by
  have hi : vertexGroup L T H c.gamma ⊓ conjugate c M = conjugate c (H ⊓ M) := by
    dsimp only [conjugate]
    rw [c.vertexGroup_gamma, map_inf _ _ _ (MulAut.conj (c.gb : G)).injective]
  rw [hi]
  change (Source.starImage _ _).map (e.toMonoidHom.comp (starEquiv c).toMonoidHom) = _
  rw [← map_map, starImage_conjugate, hmark]

theorem conjugate_flag (V₃ : Subgroup G) (h : V₃ ≤ V) :
    conjugate c V₃ ≤ conjugate c V := map_mono h

theorem conjugate_index (V₃ : Subgroup G) (h : V₃.relIndex V = 2) :
    (conjugate c V₃).relIndex (conjugate c V) = 2 := by
  rwa [relIndex_map_map_of_injective _ _ (MulAut.conj (c.gb : G)).injective]

theorem conjugate_normalizer (M : Subgroup G)
    (h : H ⊓ M ≤ normalizer (V : Set G)) :
    vertexGroup L T H c.gamma ⊓ conjugate c M ≤ normalizer (conjugate c V : Set G) := by
  rw [c.vertexGroup_gamma, ← map_inf _ _ _ (MulAut.conj (c.gb : G)).injective,
    ← map_equiv_normalizer_eq]
  exact map_mono h

theorem conjugate_VH :
    Source.VH (vertexGroup L T H c.gamma) (conjugate c V) = c.Vgamma := by
  rw [c.vertexGroup_gamma]
  exact (map_conjugateSpan V H _).symm

theorem conjugate_UH (V₃ : Subgroup G) :
    Source.UH (vertexGroup L T H c.gamma) (conjugate c V₃) = c.Ugamma V₃ := by
  rw [c.vertexGroup_gamma]
  exact (map_conjugateSpan V₃ H _).symm

theorem conjugate_noncentral (V₃ : Subgroup G)
    (h : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃) :
    ¬ ⁅Source.VH (vertexGroup L T H c.gamma) (conjugate c V),
      vertexGroup L T H c.gamma⁆ ≤ Source.UH (vertexGroup L T H c.gamma) (conjugate c V₃) := by
  rw [conjugate_VH, conjugate_UH, c.vertexGroup_gamma,
    CriticalGeometry.CriticalPair.Vgamma, CriticalGeometry.CriticalPair.Ugamma, ← map_commutator]
  exact fun hh => h ((map_le_map_iff_of_injective (MulAut.conj (c.gb : G)).injective).mp hh)


/-- Endpoint elementary abelianness is inherited from the original U_H. -/
theorem elementary_Ugamma (V₃ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)] :
    IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _

/-- Endpoint elementary abelianness is inherited from the original V_H. -/
theorem elementary_Vgamma [IsElementaryAbelian 2 (Source.VH H V)] :
    IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _

variable (V₃ : Subgroup G) [IsElementaryAbelian 2 c.Vgamma]

local instance conjugateVH_elementary :
    IsElementaryAbelian 2 (Source.VH (vertexGroup L T H c.gamma) (conjugate c V)) := by
  rw [conjugate_VH]
  infer_instance

/-- The conjugated source section is the literal endpoint section. This map
only identifies equal ambient subgroups; it introduces no model isomorphism. -/
def sourceSectionEquiv :
    Source.Vsection (vertexGroup L T H c.gamma) (conjugate c V) (conjugate c V₃) ≃*
      (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (conjugate_VH c)) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : G) ∈ c.Ugamma V₃
      rw [← conjugate_UH c V₃]
      exact hy
    · intro hx
      refine ⟨(MulEquiv.subgroupCongr (conjugate_VH c)).symm x, ?_, ?_⟩
      · change (x : G) ∈ Source.UH _ _
        rw [conjugate_UH]
        exact hx
      · exact (MulEquiv.subgroupCongr (conjugate_VH c)).apply_symm_apply x)

theorem sourceSectionEquiv_mk
    (x : Source.VH (vertexGroup L T H c.gamma) (conjugate c V)) :
    sourceSectionEquiv c V₃ (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' ((c.Ugamma V₃).subgroupOf c.Vgamma)
        ((MulEquiv.subgroupCongr (conjugate_VH c)) x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

def sourceLinearEquiv :
    Additive (Source.Vsection (vertexGroup L T H c.gamma) (conjugate c V) (conjugate c V₃)) ≃ₗ[ZMod 2]
      Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma) :=
  binaryEquiv (sourceSectionEquiv c V₃)

variable {V₃} (Z : Subgroup G) [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (hz : H ≤ normalizer (Z : Set G)) (E : EndpointActions c V₃ Z hz)

/-- The given endpoint action on the literal conjugated source section. -/
noncomputable def sourceRepresentation :
    Representation (ZMod 2) (Source.Hstar (vertexGroup L T H c.gamma))
      (Additive (Source.Vsection (vertexGroup L T H c.gamma) (conjugate c V) (conjugate c V₃))) :=
  ((sourceLinearEquiv c V₃).symm.conjRingEquiv.toMonoidHom).comp E.onV

theorem sourceRepresentation_equivariant (a : Source.Hstar (vertexGroup L T H c.gamma))
    (v : Additive (Source.Vsection (vertexGroup L T H c.gamma) (conjugate c V) (conjugate c V₃))) :
    sourceLinearEquiv c V₃ (sourceRepresentation c Z hz E a v) =
      E.onV a (sourceLinearEquiv c V₃ v) := by
  change (sourceLinearEquiv c V₃) ((sourceLinearEquiv c V₃).symm _) = _
  exact (sourceLinearEquiv c V₃).apply_symm_apply _

/-- The transported representation still acts by actual ambient conjugation. -/
theorem sourceRepresentation_conjugation :
    SectionConjugation (vertexGroup L T H c.gamma) (conjugate c V) (conjugate c V₃)
      (sourceRepresentation c Z hz E) := by
  intro j x
  apply (sourceLinearEquiv c V₃).injective
  rw [sourceRepresentation_equivariant, E.onV_mk]
  change quotientAction _ _ _ _ _ j (sourceSectionEquiv c V₃ (QuotientGroup.mk' _ x)) =
    sourceSectionEquiv c V₃ (QuotientGroup.mk' _ _)
  rw [sourceSectionEquiv_mk, sourceSectionEquiv_mk]
  exact quotientAction_apply _ _ _ _ _ j _



section Finite
variable [Finite G]
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-- The S₆-marked endpoint quotient, derived from the original source flag,
noncentrality, relative normalizer and plane marking. -/
theorem symmetric_source (M : Subgroup G)
    (e : Source.Hstar H ≃* S)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G)) :
    ∃ f : P →ₗ[ZMod 2] Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma),
      Function.Surjective f ∧
      (∀ a v, f (rho (marking c e a) v) = E.onV a (f v)) ∧
      (∃ a v, E.onV a v ≠ v) ∧ Function.Injective E.onV := by
  classical
  let := Fintype.ofFinite (Source.Hstar (vertexGroup L T H c.gamma) ⧸
    Source.starImage (vertexGroup L T H c.gamma)
      (vertexGroup L T H c.gamma ⊓ conjugate c M))
  obtain ⟨f, hf, he, hmove, hfaith⟩ := MarkedQuotient.symmetric_source
    (vertexGroup L T H c.gamma) (conjugate c M) (conjugate c V) (conjugate c V₃)
    (marking c e) (plane_marking c M e H2 hmark)
    (conjugate_flag c V₃ hflag) (conjugate_index c V₃ hindex)
    (conjugate_noncentral c V₃ hnc) (conjugate_normalizer c M hnorm)
    (sourceRepresentation c Z hz E) (sourceRepresentation_conjugation c Z hz E)
  let q := sourceLinearEquiv c V₃
  refine ⟨q.toLinearMap.comp f, q.surjective.comp hf, ?_, ?_, ?_⟩
  · intro a v
    change q (f (rho (marking c e a) v)) = E.onV a (q (f v))
    rw [he]
    exact sourceRepresentation_equivariant c Z hz E a (f v)
  · obtain ⟨a, v, hv⟩ := hmove
    refine ⟨a, q v, fun h => hv (q.injective ?_)⟩
    exact (sourceRepresentation_equivariant c Z hz E a v).trans h
  · intro a b hab
    apply hfaith
    ext v
    apply q.injective
    exact (sourceRepresentation_equivariant c Z hz E a v).trans
      ((LinearMap.congr_fun hab (q v)).trans
        (sourceRepresentation_equivariant c Z hz E b v).symm)

/-- The A₆-marked endpoint quotient uses the same endpoint equivalence. -/
theorem alternating_source (M : Subgroup G)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G)) :
    ∃ f : P →ₗ[ZMod 2] Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma),
      Function.Surjective f ∧
      (∀ a v, f (rhoA (marking c e a) v) = E.onV a (f v)) ∧
      (∃ a v, E.onV a v ≠ v) ∧ Function.Injective E.onV := by
  classical
  let := Fintype.ofFinite (Source.Hstar (vertexGroup L T H c.gamma) ⧸
    Source.starImage (vertexGroup L T H c.gamma)
      (vertexGroup L T H c.gamma ⊓ conjugate c M))
  obtain ⟨f, hf, he, hmove, hfaith⟩ := MarkedQuotient.alternating_source
    (vertexGroup L T H c.gamma) (conjugate c M) (conjugate c V) (conjugate c V₃)
    (marking c e) (plane_marking c M e _ hmark)
    (conjugate_flag c V₃ hflag) (conjugate_index c V₃ hindex)
    (conjugate_noncentral c V₃ hnc) (conjugate_normalizer c M hnorm)
    (sourceRepresentation c Z hz E) (sourceRepresentation_conjugation c Z hz E)
  let q := sourceLinearEquiv c V₃
  refine ⟨q.toLinearMap.comp f, q.surjective.comp hf, ?_, ?_, ?_⟩
  · intro a v
    change q (f (rhoA (marking c e a) v)) = E.onV a (q (f v))
    rw [he]
    exact sourceRepresentation_equivariant c Z hz E a (f v)
  · obtain ⟨a, v, hv⟩ := hmove
    refine ⟨a, q v, fun h => hv (q.injective ?_)⟩
    exact (sourceRepresentation_equivariant c Z hz E a v).trans h
  · intro a b hab
    apply hfaith
    ext v
    apply q.injective
    exact (sourceRepresentation_equivariant c Z hz E a v).trans
      ((LinearMap.congr_fun hab (q v)).trans
        (sourceRepresentation_equivariant c Z hz E b v).symm)
end Finite

section OriginalSections
variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The endpoint quotient and the original quotient have the same actor,
identified by inverse conjugation by the specified endpoint conjugator. -/
theorem uLinearEquiv_intertwines
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hτ : ∀ h : H, τ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (a : Source.Hstar (vertexGroup L T H c.gamma))
    (v : Additive (c.Ugamma V₃ ⧸ (c.Aone Z).subgroupOf (c.Ugamma V₃))) :
    SectionActions.CriticalPair.uLinearEquiv c V₃ Z (E.onU a v) =
      τ (starEquiv c a) (SectionActions.CriticalPair.uLinearEquiv c V₃ Z v) := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (vertexGroup L T H c.gamma)) a
  rw [starEquiv_mk, E.onU_mk, hτ]
  exact SectionActions.CriticalPair.uSectionEquiv_intertwines c V₃ Z
    (vertexGroup L T H c.gamma) hz le_rfl j v.toMul

open ComponentSieve.SixAndG2.NaturalSix

/-- Transport both of the genuine earlier S₆ module alternatives. The cover
is retained and the actor marking is the same as in the syntheme quotient. -/
theorem symmetric_natural_or_cover
    (e : Source.Hstar H ≃* Symmetric)
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hτ : ∀ h : H, τ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (model : (∃ q : Additive (Source.Utilde H V₃ Z) ≃ₗ[ZMod 2] Natural,
        ∀ a v, q (τ a v) = symmetricAction (e a) (q v)) ∨
      (∃ q : Additive (Source.Utilde H V₃ Z) ≃ₗ[ZMod 2] Augmentation,
        ∀ a v, q (τ a v) = BinaryPermutation.coreRepresentation (Fin 6) (e a) (q v))) :
    (∃ q : Additive (c.Ugamma V₃ ⧸ (c.Aone Z).subgroupOf (c.Ugamma V₃)) ≃ₗ[ZMod 2] Natural,
        ∀ a v, q (E.onU a v) = symmetricAction (marking c e a) (q v)) ∨
      (∃ q : Additive (c.Ugamma V₃ ⧸ (c.Aone Z).subgroupOf (c.Ugamma V₃)) ≃ₗ[ZMod 2] Augmentation,
        ∀ a v, q (E.onU a v) =
          BinaryPermutation.coreRepresentation (Fin 6) (marking c e a) (q v)) := by
  rcases model with ⟨q, hq⟩ | ⟨q, hq⟩
  · refine Or.inl ⟨(SectionActions.CriticalPair.uLinearEquiv c V₃ Z).trans q, ?_⟩
    intro a v
    change q (SectionActions.CriticalPair.uLinearEquiv c V₃ Z (E.onU a v)) = _
    rw [uLinearEquiv_intertwines c Z hz E τ hτ, hq]
    rfl
  · refine Or.inr ⟨(SectionActions.CriticalPair.uLinearEquiv c V₃ Z).trans q, ?_⟩
    intro a v
    change q (SectionActions.CriticalPair.uLinearEquiv c V₃ Z (E.onU a v)) = _
    rw [uLinearEquiv_intertwines c Z hz E τ hτ, hq]
    rfl
end OriginalSections

section OriginalVSection
variable [IsElementaryAbelian 2 (Source.VH H V)]

/-- Compatibility of the actual Vγ/Uγ ≃ V_H/U_H section equivalence with
the same endpoint star equivalence used for Uγ/A₁. -/
theorem vLinearEquiv_intertwines
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ)
    (a : Source.Hstar (vertexGroup L T H c.gamma))
    (v : Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma)) :
    SectionActions.CriticalPair.vLinearEquiv c V₃ (E.onV a v) =
      σ (starEquiv c a) (SectionActions.CriticalPair.vLinearEquiv c V₃ v) := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (vertexGroup L T H c.gamma)) a
  rw [starEquiv_mk, E.onV_mk]
  have hi := SectionActions.CriticalPair.vSectionEquiv_intertwines c V₃
    (vertexGroup L T H c.gamma) le_rfl j v.toMul
  change SectionActions.CriticalPair.vLinearEquiv c V₃
    ((binaryLinear (quotientAction _ _ _ _ _ j)).toLinearMap v) = _
  refine hi.trans ?_
  change vAction H V V₃ (actorEquiv c j)
    (SectionActions.CriticalPair.vSectionEquiv c V₃ v.toMul) =
      (σ (QuotientGroup.mk' (pCore 2 H) (actorEquiv c j))
        (Additive.ofMul (SectionActions.CriticalPair.vSectionEquiv c V₃ v.toMul))).toMul
  generalize SectionActions.CriticalPair.vSectionEquiv c V₃ v.toMul = w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((Source.UH H V₃).subgroupOf (Source.VH H V)) w
  exact (quotientAction_apply _ _ _ _ _ (actorEquiv c j) x).trans
    (congrArg Additive.toMul (hσ (actorEquiv c j) x)).symm
end OriginalVSection
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments.EndpointSource

end
