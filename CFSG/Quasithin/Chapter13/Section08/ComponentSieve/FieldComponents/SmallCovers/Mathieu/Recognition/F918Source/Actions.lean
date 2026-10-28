module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import Theory.Mathieu.M22.ValueBoundParabolics.Transport
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Quasithin.Rank

/-!
# Faithful M₂₂ section actions for F.9.18

The source placement gives H = KT. Its normal M₂₂ image has two-group
quotient and trivial centralizer in H/O₂(H). Every noncentral action is
therefore faithful. We identify the entire generalized Fitting subgroup
and its image under the actual action map, then apply the two published
classification contracts to these actors.

For an invariant Irr⁺ space the central quotient is noncentral, by full
commutator generation. The actual quadratic offender on Ũ_H descends to
this quotient with no increase in fixed codimension. Thus recognition
applies to the literal I/C_I(K), without a splitting assumption.

Source: Aschbacher–Smith, F.9.18(2–4),(7), pp.325–326, and 13.8.21(2),
p.956 (1 March 2004 manuscript). Invariance and the source alternatives
are assembled separately; they are not asserted by this module.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {H K L₁ T G₁ M : Subgroup G} (s : Placement.Setup H K L₁ T G₁ M)

include s
theorem component_nonabelian : ¬ IsMulCommutative (Source.starImage H K) := by
  let e := Placement.starCoordinates H K s.component_le s.component s.model
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  intro hc
  let : IsMulCommutative (Source.starImage H K) := hc
  have hcomm : IsMulCommutative M22 := ⟨⟨fun x y => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact (e.map_mul a b).symm.trans ((congrArg e (mul_comm' a b)).trans (e.map_mul b a))⟩⟩
  have hz : (⊤ : Subgroup M22) = ⊥ :=
    (center_eq_top (G := M22)).symm.trans m22_center_eq_bot
  exact top_ne_bot hz

theorem source_structure :
    generalizedFitting (Source.Hstar H) = Source.starImage H K ∧
    ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ → Source.starImage H K ≤ N := by
  let : (Source.starImage H K).Normal := s.star_component_normal
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup (Source.starImage H K) :=
    (Placement.starCoordinates H K s.component_le s.component s.model).isSimpleGroup
  have hq : IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K) := by
    apply isPGroup_quotient_of_sup_eq_top _ (Source.starImage H T) _ s.star_component_join_sylow
    change IsPGroup 2 ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    rw [← s.sylow_eq]
    exact s.sylow.isPGroup'.map _
  obtain ⟨hfit, _, hnormal⟩ := simple_two_quotient_structure
    (Source.starImage H K) (component_nonabelian s) hq (pCore_quotient_pCore_eq_bot 2)
  exact ⟨hfit, hnormal⟩

def fittingCoordinates : generalizedFitting (Source.Hstar H) ≃* M22 :=
  (MulEquiv.subgroupCongr (source_structure s).1).trans
    (Placement.starCoordinates H K s.component_le s.component s.model)

omit s in
theorem source_sqtk {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H) :
    IsSQTK 𝒦 (Source.Hstar H) := by
  refine ⟨?_, hH.isKGroup.quotient (pCore 2 H)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

theorem faithful_of_noncentral {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (Source.Hstar H) V)
    (hn : ¬ Source.starImage H K ≤ (actionHom σ).ker) : Function.Injective σ := by
  have hk : (actionHom σ).ker = ⊥ := by
    by_contra h
    exact hn ((source_structure s).2 _ inferInstance h)
  have hf := (MonoidHom.ker_eq_bot_iff _).mp hk
  intro x y hxy
  apply hf
  apply imageRepresentation_injective σ
  exact hxy

def faithfulImageEquiv {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (Source.Hstar H) V) (hf : Function.Injective σ) :
    Source.Hstar H ≃* actionImage σ :=
  MulEquiv.ofBijective (actionHom σ)
    ⟨fun _ _ h => hf (congrArg (imageRepresentation σ) h), σ.asGroupHom.rangeRestrict_surjective⟩

theorem image_fitting {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (Source.Hstar H) V) (hf : Function.Injective σ) :
    generalizedFitting (actionImage σ) = actionSubgroup σ (Source.starImage H K) := by
  rw [← M22ValueBound.map_generalizedFitting (faithfulImageEquiv σ hf),
    (source_structure s).1]
  rfl

theorem no_ff_source {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H)
    (hno : NoFaithfulFF 𝒦) (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) (Source.Hstar H) V) (hf : Function.Injective σ) :
    ¬ IsFFModule σ :=
  hno _ _ σ (source_sqtk hH) hf ⟨fittingCoordinates s⟩

theorem no_ff_image {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H)
    (hno : NoFaithfulFF 𝒦) (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) (Source.Hstar H) V) (hf : Function.Injective σ) :
    ¬ IsFFModule (imageRepresentation σ) := by
  let e := faithfulImageEquiv σ hf
  exact hno _ _ (imageRepresentation σ) ((IsSQTK.equiv e).mp (source_sqtk hH))
    (imageRepresentation_injective σ)
    ⟨(M22ValueBound.generalizedFittingEquiv e).symm.trans (fittingCoordinates s)⟩

variable {V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (d : SourceAction H V₃ V₁)

theorem central_faithful (I : Subrepresentation d.representation)
    (hI : IsIrrPlus d.representation (Source.starImage H K) I.toSubmodule) :
    Function.Injective (sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I) := by
  let σ := sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I
  apply faithful_of_noncentral s σ
  intro hk
  apply hI.not_le_fixedSpace d.representation
  rw [← hI.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hkK, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff σ k).mp (hk hkK)
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace d.representation
    (Source.starImage H K)).comap I.toSubmodule.subtype)).mp hfix

theorem central_quadratic_bound (I : Subrepresentation d.representation)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hq : IsQuadratic d.representation A)
    (hc : fixedCodim d.representation A ≤ 2 * rank A) :
    quadraticRatio (sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I) ≤ 2 := by
  let := s.star_component_normal
  let C := normalCentralSubrepresentation d.representation (Source.starImage H K) I
  let σ := sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I
  apply (quadraticRatio_le_two_iff σ).mpr
  refine ⟨A, hA, ?_, ?_⟩
  · exact quadratic_of_equivariant_surjection I.toRepresentation σ C.toSubmodule.mkQ
      C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation d.representation I hq)
  · exact (fixedCodim_le_of_equivariant_surjection I.toRepresentation σ C.toSubmodule.mkQ
      C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
      ((fixedCodim_subrepresentation_le d.representation I A).trans hc)

theorem central_code {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H)
    (hcode : SmallQuadraticCode 𝒦)
    (I : Subrepresentation d.representation)
    (hI : IsIrrPlus d.representation (Source.starImage H K) I.toSubmodule)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hq : IsQuadratic d.representation A)
    (hc : fixedCodim d.representation A ≤ 2 * rank A) :
    MathieuCode.IsM22Code ((sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I).comp
      (Source.starImage H K).subtype) := by
  let σ := sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I
  let : Finite (centralQuotient d.representation (Source.starImage H K) I.toSubmodule) :=
    Finite.of_surjective _ ((fixedSpace d.representation (Source.starImage H K)).comap
      I.toSubmodule.subtype).mkQ_surjective
  have hsimple : IsSimpleGroup (Source.starImage H K) := by
    let : IsSimpleGroup M22 := m22_isSimpleGroup
    exact (Placement.starCoordinates H K s.component_le s.component s.model).isSimpleGroup
  let : IsSimpleGroup (Source.starImage H K) := hsimple
  let : Group.IsPerfect (Source.starImage H K) := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator (Source.starImage H K))
      inferInstance).resolve_left (fun h => component_nonabelian s
        ((commutator_eq_bot_iff _).mp h))⟩
  have hz : center (Source.starImage H K) = ⊥ := by
    rcases (inferInstance : (center (Source.starImage H K)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (component_nonabelian s (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple (Source.starImage H K) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hquasi : IsQuasisimple (generalizedFitting (Source.Hstar H)) := by
    rw [(source_structure s).1]
    infer_instance
  have hirr : IsIrreducible (σ.comp (generalizedFitting (Source.Hstar H)).subtype) := by
    rw [(source_structure s).1]
    exact hI.choose_spec.2
  have hb : B4Hypotheses 𝒦 σ :=
    ⟨source_sqtk hH, central_faithful s d I hI, hquasi, hirr⟩
  have h := hcode _ _ σ hb (central_quadratic_bound s d I A hA hq hc)
    ⟨fittingCoordinates s⟩
  rwa [(source_structure s).1] at h
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
