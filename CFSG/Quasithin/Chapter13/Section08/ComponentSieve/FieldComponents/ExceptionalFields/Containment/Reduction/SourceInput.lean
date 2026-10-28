module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.Models
public import Theory.GroupTheory.CComponent.Basic

/-!
# Source boundary for the exceptional noncontainment reduction

These are the local standing hypotheses and earlier conclusions used on
printed pp.954–955 in the proof of Aschbacher–Smith 13.8.20. In particular,
the theta identity is the actual 13.7.3(9) identity on H ∩ M. Its restriction
to BL₁ will be proved, rather than included as another input.

The Borel is marked by the source Sylow subgroup through H/O₂(H). Both
centralizer identities, the index-three identity, and the same element of
T ∩ L are retained. Normality of K is relative to H. The actual model
alternatives, failure of external X, and separate projective L₃(4)
exclusion are supplied at assembly; no noncontainment conclusion is a
field of this structure. This local boundary does not assert a proof of
the preceding chapter theorems or of the ambient QTKE hypotheses.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
open HigherFieldReduction Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The source local data before the claim L₁ ≤ K. The special unitary
and projective unitary carriers are kept separate by `ExceptionalModels`. -/
structure SourceBorelInput
    (H K L L₁ L₀ X L₁plus G₁ M V : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (S : Sylow 2 K) (t : H) : Prop where
  mem_Hz : H ∈ Source.Hz L₁ T G₁ M
  generated : H = K ⊔ L₁ ⊔ (T : Subgroup G)
  component : (K.subgroupOf H).IsCComponent
  component_normal : (K.subgroupOf H).Normal
  local_normalizer : M = normalizer (L : Set G)
  sylow_le_M : (T : Subgroup G) ≤ M
  component_sylow_le : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G)
  earlier : EarlierSeedModels L L₁ X L₁plus
  zero_le : L₀ ≤ L₁
  chosen_seed_le : X ≤ L₁
  seed_twoPerfect : IsPPerfect 2 L₁
  theta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  overlap_normalizer : H ⊓ M = H ⊓ normalizer (V : Set G)
  borel_le_M : borelResidual (componentBorel H K hKH S) ≤ M
  seed_normalizes_borel :
    L₁ ≤ normalizer (borelResidual (componentBorel H K hKH S) : Set G)
  product : borelResidual (componentBorel H K hKH S) ⊔ L₁ =
    centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L ⊔ L₁
  ordinary_centralizer :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
    centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
      residualIn 3 (borelResidual (componentBorel H K hKH S))
  covered_centralizer :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
      residualIn 3 (borelResidual (componentBorel H K hKH S)) ⊔ L₀
  centralizes_V :
    centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L ≤
      M ⊓ centralizer (V : Set G)
  index_subgroup_le :
    centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L ⊔
      (borelResidual (componentBorel H K hKH S)).pCoreIn 2 ≤
        borelResidual (componentBorel H K hKH S) ⊔ X
  index_three :
    (centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L ⊔
      (borelResidual (componentBorel H K hKH S)).pCoreIn 2).relIndex
        (borelResidual (componentBorel H K hKH S) ⊔ X) = 3
  actor_mem : (t : G) ∈ (T : Subgroup G) ⊓ L
  actor_inverts : ∀ x ∈ X,
    (t : G) * x * (t : G)⁻¹ * x ∈ X.pCoreIn 2
  actor_centralizes :
    ⁅centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L,
      zpowers (t : G)⁆ ≤
        (centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L).pCoreIn 2

variable {H K L L₁ L₀ X L₁plus G₁ M V : Subgroup G} {T : Sylow 2 G}
  {hKH : K ≤ H} {S : Sylow 2 K} {t : H}

/-- Restrict the exact earlier theta identity to BL₁ using B ≤ M.
This derives the local normality input used in the three-part proof. -/
theorem SourceBorelInput.theta_borel
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t) :
    L₁ = closure {x : G |
      x ∈ borelResidual (componentBorel H K hKH S) ⊔ L₁ ∧ orderOf x = 3} := by
  have hL : L₁ ≤ H ⊓ M := by
    rw [s.theta]
    exact (closure_le _).mpr fun _ hx => hx.1
  have hB : borelResidual (componentBorel H K hKH S) ≤ H ⊓ M :=
    le_inf ((map_subtype_le _).trans ((borelLift_le H K hKH _).trans hKH))
      s.borel_le_M
  apply le_antisymm
  · conv_lhs => rw [s.theta]
    apply (closure_le _).mpr
    intro x hx
    have hxL : x ∈ L₁ := s.theta.symm ▸ subset_closure hx
    exact Subgroup.subset_closure
      ⟨(le_sup_right : L₁ ≤ borelResidual (componentBorel H K hKH S) ⊔ L₁) hxL, hx.2⟩
  · conv_rhs => rw [s.theta]
    exact Subgroup.closure_mono fun _ hx => ⟨sup_le hB hL hx.1, hx.2⟩

/-- The source normalizer makes the commutator-preimage definition of B_C
centralize the actual section L/O₂(L). No ambient normality is imposed. -/
theorem SourceBorelInput.centralizer_commutator
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t) :
    ⁅centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L, L⁆ ≤
      L.pCoreIn 2 := by
  have hL : L₁ ≤ M := by
    rw [s.theta]
    exact (closure_le _).mpr fun _ hx => hx.1.2
  apply centralizingResidual_commutator_le
  apply (sup_le s.borel_le_M hL).trans
  rw [s.local_normalizer]
  exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)

/-- All inputs to the parent's five-point Borel marking are constructed,
including a Sylow subgroup of B₀ whose ambient image lies in T. -/
theorem SourceBorelInput.borel_marking
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t) :
    componentBorel H K hKH S ≤ H ∧
    Source.starImage H (componentBorel H K hKH S) =
      (normalizer (componentStarSylow H K hKH S : Set (Source.starImage H K))).map
        (Source.starImage H K).subtype ∧
    ∃ U : Sylow 2 (componentBorel H K hKH S),
      (U : Subgroup (componentBorel H K hKH S)).map
        (componentBorel H K hKH S).subtype ≤ (T : Subgroup G) :=
  componentBorel_marking H K T hKH S s.component_sylow_le

/-- The prescribed Borel Sylow image is exactly T* ∩ K*. -/
theorem SourceBorelInput.star_sylow
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t) :
    (componentStarSylow H K hKH S : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype = Source.starImage H T ⊓ Source.starImage H K :=
  componentStarSylow_source_intersection H K hKH S T s.component_sylow_le

omit [Finite G] in
/-- Remove just the independently excluded projective L₃(4) carrier.
Every surviving alternative still contains its actual model equivalence. -/
theorem exceptionalModels_of_carrier
    (h : ExceptionalCarrier.{_,0} (Source.starImage H K))
    (hnot : ¬ ClassicalGroup.IsPSL (Source.starImage H K) 3 4) :
    ExceptionalModels (Source.starImage H K) := by
  cases h with
  | linearTwo F hF e => exact Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  | specialLinearThree F hF e =>
    exact Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩)
  | projectiveLinearThree F hF e =>
    exact (hnot ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩).elim
  | specialUnitaryThree F J hF hconj e =>
    exact Or.inr (Or.inr (Or.inr
      ⟨F, inferInstance, inferInstance, J, hF, hconj, ⟨e⟩⟩))
  | projectiveUnitaryThree F J hF hconj e =>
    exact Or.inr (Or.inr (Or.inl
      ⟨F, inferInstance, inferInstance, J, hF, hconj, ⟨e⟩⟩))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
