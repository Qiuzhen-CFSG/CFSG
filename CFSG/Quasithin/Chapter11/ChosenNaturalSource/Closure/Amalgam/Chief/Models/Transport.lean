module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Detection
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image
public import Theory.Representation.BinaryOffender.QuasisimpleImage

/-!
# The literal exceptional component on a chief section

Conjugation embeds K in (KT)^g. On an irreducible binary section its
intrinsic two-core acts trivially, since K is relatively normal. We descend
the action through the actual K/O₂(K), retaining the image of F*(K/O₂(K)).
A surviving image is a normal C-component, even though the original action
need not be faithful and its whole kernel need not be solvable.

Source: Aschbacher--Smith, 11.5.8, printed p.784. This is transport for the
model comparison, not the exclusion of the G.6.4 alternatives.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

/-- The conjugation isomorphism on the whole actor. -/
def actorEquiv : KT E ≃* actor E g :=
  (KT E).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

/-- K acts by its actual conjugated embedding, with no quotient suppressed. -/
def componentEmbedding : E.K →* actor E g :=
  (actorEquiv E g).toMonoidHom.comp (inclusion (show E.K ≤ KT E from le_sup_left))

@[simp] theorem componentEmbedding_coe (k : E.K) :
    (componentEmbedding E g k : G) = g * k * g⁻¹ := rfl

theorem componentEmbedding_normal (h : LocalInputs E) :
    (componentEmbedding E g).range.Normal := by
  have hn : (E.K.subgroupOf (KT E)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      ((KT_le_G₁ E h).trans E.G₁_normalizes_K)
  rw [componentEmbedding, MonoidHom.range_comp, inclusion_range]
  exact hn.map _ (actorEquiv E g).surjective

theorem componentEmbedding_twoCore (h : LocalInputs E) :
    (pCore 2 E.K).map (componentEmbedding E g) ≤ pCore 2 (actor E g) := by
  have hle := pCoreIn_mono_of_normalizes (p := 2)
    (show E.K ≤ KT E from le_sup_left)
    ((KT_le_G₁ E h).trans E.G₁_normalizes_K)
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨z, hz, he⟩ := hle (mem_map_of_mem E.K.subtype hk)
  have he' : inclusion (show E.K ≤ KT E from le_sup_left) k = z := Subtype.ext he.symm
  change actorEquiv E g (inclusion _ k) ∈ pCore 2 (actor E g)
  rw [he', ← pCore_map_iso 2 (actorEquiv E g)]
  exact mem_map_of_mem _ hz

/-- Intrinsic C-component status, without asserting ambient normality in G. -/
theorem component_top (hK : Source.NormalComponentIn E.G₁ E.K) :
    (⊤ : Subgroup E.K).IsCComponent := by
  have hc : (⊤ : Subgroup (E.K.subgroupOf E.G₁)).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf (le_refl _)
  simpa using hc.map_equiv (subgroupOfEquivOfLe hK.1.1)

theorem quotient_component_top (hK : Source.NormalComponentIn E.G₁ E.K) :
    (⊤ : Subgroup (E.K ⧸ pCore 2 E.K)).IsCComponent := by
  let : Group.IsNilpotent (pCore 2 E.K) := pCore_isPGroup.isNilpotent
  simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    using (component_top E hK).map_quotient (pCore 2 E.K)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (actor E g) W)

/-- The literal action of K on the chosen section. -/
def componentAction : E.K →* actionImage σ := (actionHom σ).comp (componentEmbedding E g)

theorem componentAction_normal (h : LocalInputs E) : (componentAction E g σ).range.Normal := by
  rw [componentAction, MonoidHom.range_comp]
  exact (componentEmbedding_normal E g h).map _ σ.asGroupHom.rangeRestrict_surjective

theorem componentAction_kills_twoCore (h : LocalInputs E)
    (hcore : pCore 2 (actionImage σ) = ⊥) : pCore 2 E.K ≤ (componentAction E g σ).ker := by
  have hm : (pCore 2 (actor E g)).map (actionHom σ) ≤ pCore 2 (actionImage σ) :=
    le_sSup ⟨(inferInstance : (pCore 2 (actor E g)).Normal).map _
      σ.asGroupHom.rangeRestrict_surjective, pCore_isPGroup.map _⟩
  intro k hk
  have hz := hm (mem_map_of_mem (actionHom σ) (componentEmbedding_twoCore E g h
    (mem_map_of_mem (componentEmbedding E g) hk)))
  exact mem_bot.mp (hcore ▸ hz)

/-- Descend through O₂(K), rather than through an unmarked simple quotient. -/
def quotientAction (hk : pCore 2 E.K ≤ (componentAction E g σ).ker) :
    (E.K ⧸ pCore 2 E.K) →* actionImage σ :=
  QuotientGroup.lift (pCore 2 E.K) (componentAction E g σ) hk

@[simp] theorem quotientAction_mk (hk : pCore 2 E.K ≤ (componentAction E g σ).ker)
    (k : E.K) : quotientAction E g σ hk (QuotientGroup.mk' _ k) =
      actionHom σ (componentEmbedding E g k) := rfl

theorem quotientAction_range (hk : pCore 2 E.K ≤ (componentAction E g σ).ker) :
    (quotientAction E g σ hk).range = (componentAction E g σ).range := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) z
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨QuotientGroup.mk' _ k, rfl⟩

/-- The marked lift agrees with the pullback along the actual action of K. -/
theorem markedFitting_killed_iff
    (hk : pCore 2 E.K ≤ (componentAction E g σ).ker) :
    markedFitting E g ≤ σ.ker ↔
      generalizedFitting (E.K ⧸ pCore 2 E.K) ≤ (quotientAction E g σ hk).ker := by
  constructor
  · intro hm z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) z
    have hkF : componentEmbedding E g k ∈ markedFitting E g := by
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom
        (mem_map_of_mem E.K.subtype hz)
    apply (actionHom_eq_one_iff σ _).mpr
    intro w
    exact LinearMap.congr_fun (hm hkF) w
  · intro hm a ha
    obtain ⟨x, hx, he⟩ := ha
    obtain ⟨k, hkF, rfl⟩ := hx
    have he' : componentEmbedding E g k = a := Subtype.ext he
    have hz : actionHom σ (componentEmbedding E g k) = 1 := hm hkF
    rw [he'] at hz
    exact LinearMap.ext ((actionHom_eq_one_iff σ a).mp hz)

private theorem range_component {C H : Type*} [Group C] [Group H] [Finite C]
    (hC : (⊤ : Subgroup C).IsCComponent) (f : C →* H) (hn : f.range.Normal)
    (hne : f.range ≠ ⊥) : f.range.IsCComponent := by
  have hk : f.ker ≠ ⊤ := by
    intro he
    exact hne (MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp he))
  have hker := kernel_le_solvableRadical_of_top_isCComponent hC f hk
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := inclusion hker) (inclusion_injective hker)
  have hkr : Group.IsSolvable f.rangeRestrict.ker := by
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show f.rangeRestrict.ker ≤ f.ker from fun x hx => congrArg Subtype.val hx))
      (inclusion_injective _)
  let := hkr
  have hc := cComponent_map_of_solvable_ker hC f.rangeRestrict f.rangeRestrict_surjective
  have ht : (⊤ : Subgroup f.range).IsCComponent := by
    simpa only [map_top_of_surjective _ f.rangeRestrict_surjective] using hc
  simpa only [← MonoidHom.range_eq_map, range_subtype] using ht.map_subtype hn.isSubnormal

/-- Survival of the literal F* lift makes the normal image a genuine C-component. -/
theorem quotientAction_component (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K)
    (hk : pCore 2 E.K ≤ (componentAction E g σ).ker)
    (hF : ¬ markedFitting E g ≤ σ.ker) : (quotientAction E g σ hk).range.IsCComponent := by
  have hn : (quotientAction E g σ hk).range.Normal := by
    rw [quotientAction_range]
    exact componentAction_normal E g σ h
  apply range_component (quotient_component_top E hK) _ hn
  intro he
  apply hF
  apply (markedFitting_killed_iff E g σ hk).mpr
  intro z _
  exact mem_bot.mp (he ▸ (show quotientAction E g σ hk z ∈ (quotientAction E g σ hk).range from ⟨z, rfl⟩))

/-- A genuine chief section supplies the exact map needed by the model
comparison, with relative normality and the generalized-Fitting image retained.
The section itself and its marked survival are the independent inputs. -/
theorem chief_quotient_data [IsElementaryAbelian 2 (localClosure E)]
    (h : LocalInputs E) (hK : Source.NormalComponentIn E.G₁ E.K)
    (A B : Subrepresentation (action E g)) (hAB : A ⋖ B)
    (hF : ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker) :
      ∃ f : (E.K ⧸ pCore 2 E.K) →*
          actionImage (sectionRepresentation (action E g) A B),
        (∀ k : E.K, f (QuotientGroup.mk' _ k) =
          actionHom (sectionRepresentation (action E g) A B) (componentEmbedding E g k)) ∧
        f.range.Normal ∧ f.range.IsCComponent ∧
        ¬ generalizedFitting (E.K ⧸ pCore 2 E.K) ≤ f.ker := by
  let σ := sectionRepresentation (action E g) A B
  let : Finite (B.toSubmodule ⧸ (sectionLower (action E g) A B).toSubmodule) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hi := MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy hAB
  let := imageRepresentation_irreducible σ hi
  have hcore := QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible
    (imageRepresentation σ) (imageRepresentation_injective σ)
  have hk := componentAction_kills_twoCore E g σ h hcore
  refine ⟨quotientAction E g σ hk, quotientAction_mk E g σ hk, ?_,
    quotientAction_component E g σ h hK hk hF, ?_⟩
  · rw [quotientAction_range]
    exact componentAction_normal E g σ h
  · exact fun hf => hF ((markedFitting_killed_iff E g σ hk).mpr hf)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
