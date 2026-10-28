module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Seed
public import Theory.Representation.MathieuCodeRestriction.M22

/-!
# Comparing the source component action with the M₂₂ code

Code recognition supplies its own group marking. We change the model in the
standing placement setup to that marking and run the proved placement argument
there. Thus no agreement between independently chosen M₂₂ equivalences is
assumed. The original component quotient and its canonical star comparison are
retained. Faithfulness of the design action proves that every element of the
actual radical acts through exactly the native hexad-kernel element assigned
by placement, even when the element itself is outside K.

The intertwining equivalence then transports the fixed line from the genuine
M₂₂ hyperplane in the M₂₄ code. Together with the proved containment of actual
two-cores, the literal rank-two seed gives a contradiction. This is conditional
on recognition of the moved component module, which still needs the precise
F.9.18 and B.4 deductions; it does not assume a local action comparison or an
M₂₂ fixed-space dimension.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), H.13.1
and H.16.2(1), combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G}

/-- Change the arbitrary native model while preserving every standing source input. -/
noncomputable def Placement.Setup.withModel (s : Placement.Setup H K L₁ T G₁ M)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    Placement.Setup H K L₁ T G₁ M := { s with model := e }

omit [Finite G] in
/-- The change of marking is the specified native automorphism, retaining
the initially supplied quotient equivalence on every element. -/
theorem Placement.Setup.withModel_comparison (s : Placement.Setup H K L₁ T G₁ M)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) (q : K ⧸ pCore 2 K) :
    (s.withModel e).model q = (s.model.symm.trans e) (s.model q) := by
  simp [Placement.Setup.withModel]

/-- The radical element has this actual component image in H/O₂(H).
It need not itself be an element of K. -/
theorem Placement.Witness.radical_star
    {s : Placement.Setup H K L₁ T G₁ M} (w : Placement.Witness s)
    (q : (s.hexadOvergroup w.hexad).pCoreIn 2) :
    QuotientGroup.mk' (pCore 2 H) q.val =
      (Components.componentStarEquiv H K s.component_le s.component
        (s.model.symm (w.radicalMap q)) : Source.Hstar H) := by
  apply s.designHom_injective
  rw [s.designHom_component, s.model.apply_symm_apply]
  exact (w.radical_design q).symm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Placement compares the fixed spaces of the actual two-cores in H. -/
theorem Placement.Witness.fixed_core_compare
    {s : Placement.Setup H K L₁ T G₁ M} (w : Placement.Witness s)
    (ρ : Representation (ZMod 2) H V) :
    fixedSpace ρ (((L₁ ⊔ T).subgroupOf H).pCoreIn 2) ≤
      fixedSpace ρ ((s.hexadOvergroup w.hexad).pCoreIn 2) :=
  Mathieu.fixed_core_compare ρ _ _
    (subgroupOf_mono H (sup_le_sup w.seed_le_lift le_rfl)) w.radical_le

/-- Pull the actual invariant component space back along H → H/O₂(H). -/
def inflatedSubrepresentation (ρ : Representation (ZMod 2) (Source.Hstar H) V)
    (I : Subrepresentation ρ) :
    Subrepresentation (ρ.comp (QuotientGroup.mk' (pCore 2 H))) :=
  ⟨I.toSubmodule, fun _ _ hv => I.apply_mem_toSubmodule _ hv⟩

/-- The code intertwiner on K* also intertwines the literal local radical. -/
theorem Placement.Witness.radical_intertwines
    {s : Placement.Setup H K L₁ T G₁ M} (w : Placement.Witness s)
    (ρ : Representation (ZMod 2) (Source.Hstar H) V) (I : Subrepresentation ρ)
    (E : I.toSubmodule ≃ₗ[ZMod 2] MathieuCode.M22Code)
    (he : ∀ (k : Source.starImage H K) v,
      E (I.toRepresentation k.val v) = MathieuCode.m22CodeRepresentation
        (Placement.starCoordinates H K s.component_le s.component s.model k) (E v))
    (q : (s.hexadOvergroup w.hexad).pCoreIn 2) (v : I.toSubmodule) :
    E ((inflatedSubrepresentation ρ I).toRepresentation q.val v) =
      MathieuCode.m22CodeRepresentation (w.radicalMap q) (E v) := by
  change E (I.toRepresentation (QuotientGroup.mk' (pCore 2 H) q.val) v) = _
  rw [w.radical_star, he]
  simp [Placement.starCoordinates]

/-- Transfer the M₂₄ fixed line through its proved M₂₂ restriction and
the actual radical map. -/
theorem Placement.Witness.code_fixed_line
    {s : Placement.Setup H K L₁ T G₁ M} (w : Placement.Witness s)
    (ρ : Representation (ZMod 2) (Source.Hstar H) V) (I : Subrepresentation ρ)
    (E : I.toSubmodule ≃ₗ[ZMod 2] MathieuCode.M22Code)
    (he : ∀ (k : Source.starImage H K) v,
      E (I.toRepresentation k.val v) = MathieuCode.m22CodeRepresentation
        (Placement.starCoordinates H K s.component_le s.component s.model k) (E v))
    (hline : MathieuCode.M24OctadFixedLine) :
    Module.finrank (ZMod 2) (fixedSpace (inflatedSubrepresentation ρ I).toRepresentation
      ((s.hexadOvergroup w.hexad).pCoreIn 2)) = 1 := by
  exact fixed_line_of_radical_model _ _ MathieuCode.m22CodeRepresentation w.radicalMap E
    (w.radical_intertwines ρ I E he) _ w.radical_range
    (MathieuCode.m22Hexad_fixedSpace_finrank_of_M24 hline w.hexad_mem)

/-- Taking displacements commutes with inflation along the source quotient. -/
theorem commutator_inflation {A D : Type*} [Group A] [Group D]
    (ρ : Representation (ZMod 2) D V) (f : A →* D)
    (S : Submodule (ZMod 2) V) (X : Subgroup A) :
    subspaceCommutator (ρ.comp f) S X = subspaceCommutator ρ S (X.map f) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, u, hu, rfl⟩
    exact ⟨f x, mem_map_of_mem f hx, u, hu, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, u, hu, rfl⟩
    exact ⟨x, hx, u, hu, rfl⟩

variable (H K L₁ T G₁ M V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The source seed contradicts recognition of its entire moved component
space as the code. Recognition and the moved-space identity remain obligations;
placement, the radical action comparison, and the fixed line are derived here. -/
theorem source_code_contradiction (s : Placement.Setup H K L₁ T G₁ M)
    (d : SourceAction H V₃ V₁) (hne : V₃ ≠ ⊥) (hgen : ⁅V₃, L₁⁆ = V₃)
    (hn : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (I : Subrepresentation d.representation)
    [Representation.IsIrreducible
      (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
        (source_seed_stable d (L₁ ⊔ T) hn)).toRepresentation]
    (hI : I.toSubmodule = subspaceCommutator d.representation ⊤ (Source.starImage H K))
    (hcode : MathieuCode.IsM22Code (I.toRepresentation.comp (Source.starImage H K).subtype))
    (hS : seedSpace H V₃ V₁ =
      subspaceCommutator d.onH (seedSpace H V₃ V₁) (L₁.subgroupOf H))
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hline : MathieuCode.M24OctadFixedLine) : False := by
  obtain ⟨eK, E, he⟩ := hcode
  let e := (Components.componentStarEquiv H K s.component_le s.component).trans eK
  let s' := s.withModel e
  obtain ⟨w⟩ := s'.source_placement V₃ hne hgen
  have he' : ∀ (k : Source.starImage H K) v,
      E (I.toRepresentation k.val v) = MathieuCode.m22CodeRepresentation
        (Placement.starCoordinates H K s'.component_le s'.component s'.model k) (E v) := by
    intro k v
    simpa [Placement.starCoordinates, s', Placement.Setup.withModel, e] using he k v
  let I' := inflatedSubrepresentation d.representation I
  have hI' : I'.toSubmodule = subspaceCommutator d.onH ⊤ (K.subgroupOf H) := by
    rw [SourceAction.onH, commutator_inflation]
    exact hI
  exact no_rank_two_seed_in_parabolic_fixed_line I'.toRepresentation
    ((L₁ ⊔ T).subgroupOf H) (s'.hexadOvergroup w.hexad)
    (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
      (source_seed_stable d (L₁ ⊔ T) hn)).toRepresentation
    (seedEmbedding d.onH (K.subgroupOf H) (L₁.subgroupOf H) I'
      (seedSpace H V₃ V₁) (subgroupOf_mono H s.seed_le_component) hI' hS)
    (seedEmbedding_injective d.onH (K.subgroupOf H) (L₁.subgroupOf H) I'
      (seedSpace H V₃ V₁) (subgroupOf_mono H s.seed_le_component) hI' hS)
    (seedEmbedding_equivariant d.onH (K.subgroupOf H) (L₁.subgroupOf H) I'
      ((L₁ ⊔ T).subgroupOf H)
      (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
        (source_seed_stable d (L₁ ⊔ T) hn))
      (subgroupOf_mono H s.seed_le_component) hI' hS)
    hseed (w.fixed_core_compare I'.toRepresentation)
    (w.code_fixed_line d.representation I E he' hline)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
