module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Recognition
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedModel

public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicTypes

/-!
# The actual initial FF action in the exceptional MS pair

Put M = LR, K = L inside M, Q = O₂(M), and X = Ω₁Z(Q). The action
on X is taken through its literal kernel C_M(X), which is Q or the retained
cubic extension E. The component in this faithful actor is respectively the
triple A₆ cover or A₆. The complete B.5.1 theorem applies in both cases:
Theorems A and C supply its genuine SQTK and classification inputs.

The full initial moved space is Irr+ in either case. In the first it is a
six-dimensional direct complement to the component-fixed space; in the
second its central quotient is the binary natural A₆ module. Irr+ and
commutator idempotence identify [X,K] with [Z,K], where Z is the normal
closure of Ω₁Z(R). This does not identify X with Z. In the second case the
natural-module normalizer also proves preservation of both source parabolic
types, independently of the chosen A₆ marking.

These are initial-layer results. Exhausting the entire [Q,K], and the
parabolic-type argument for the faithful triple-cover action, remain with
this exceptional reconstruction owner. No whole-core hypothesis, Sylow
assumption on R, or discarded cubic kernel enters the proofs below.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and B.5.1;
Meierfrankenfeld--Stellmacher (1993), (3.2), printed pp.863--864.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X" => centralOmega L R

/-- The full centralizer used by the actual initial conjugation action. -/
abbrev layerKernel (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  centralizer (centralOmega L R : Set (L ⊔ R : Subgroup G))

/-- The faithful actor, retaining whichever initial kernel actually occurs. -/
abbrev LayerActor (L R : Subgroup G) := (L ⊔ R : Subgroup G) ⧸ layerKernel L R

/-- The component under the original centralizer-quotient map. -/
abbrev layerComponent (L R : Subgroup G) : Subgroup (LayerActor L R) :=
  (L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (layerKernel L R))

/-- The original conjugation action on X, through its exact kernel. -/
@[expose] def layerAction (L R : Subgroup G) : Representation (ZMod 2) (LayerActor L R) (Additive (centralOmega L R)) :=
  NormalElementaryQuotient.representation (centralOmega L R)
    (QuotientGroup.mk' (layerKernel L R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)

omit [Finite G] in
/-- The quotient by the full centralizer acts faithfully. -/
theorem layerAction_faithful : Function.Injective (layerAction L R) :=
  NormalElementaryQuotient.representation_injective _ _ _ _

/-- MS3 supplies FF for the actual initial action in either kernel case. -/
theorem layerAction_isFFModule (h : SmallMSPair κ L R) (e : CentralMarking L) :
    IsFFModule (layerAction L R) := h.relative_centralOmega_isFFModule e

/-- Component normality is relative to the actual action quotient. -/
theorem layerComponent_normal (h : SmallMSPair κ L R) : (layerComponent L R).Normal := by
  let := h.relative_normal
  exact (inferInstance : (K).Normal).map _ (QuotientGroup.mk'_surjective _)

private def quotientImageEquiv {A : Type*} [Group A]
    (B N N' : Subgroup A) [N.Normal] [N'.Normal] (h : N = N') :
    B.map (QuotientGroup.mk' N) ≃* B.map (QuotientGroup.mk' N') := by
  subst N'
  exact MulEquiv.refl _

private theorem twoCore_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) (h : pCore 2 B = ⊥) : pCore 2 A = ⊥ := by
  apply (map_eq_bot_iff_of_injective (f := f.toMonoidHom) _ f.injective).mp
  rw [pCore_map_iso, h]

/-- The two possible kernels leave the triple cover or its simple quotient. -/
theorem layerComponent_quasisimple (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) : IsQuasisimple (layerComponent L R) := by
  let := h.relative_core_quasisimple e
  rcases centralOmega_centralizer_cases h e hz with hc | hc
  · exact IsQuasisimple.of_mulEquiv
      ((cComponentTwoCoreQuotientEquiv h.component).trans
        (quotientImageEquiv K _ _ hc).symm)
  · let : IsQuasisimple (alternatingGroup (Fin 6)) :=
      GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1
    exact IsQuasisimple.of_mulEquiv
      ((extensionKernel_component_equiv h e).symm.trans
        (quotientImageEquiv K _ _ hc).symm)

/-- Both actual initial actors have trivial two-core. -/
theorem layerActor_twoCore (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) : pCore 2 (LayerActor L R) = ⊥ := by
  rcases centralOmega_centralizer_cases h e hz with hc | hc
  · exact twoCore_eq_bot_of_equiv (QuotientGroup.quotientMulEquivOfEq hc)
      (pCore_quotient_pCore_eq_bot 2)
  · exact twoCore_eq_bot_of_equiv (QuotientGroup.quotientMulEquivOfEq hc)
      (extensionQuotient_twoCore h e)

/-- The original radical still gives a two-group supplement after taking the action quotient. -/
theorem layerActor_component_quotient_two (h : SmallMSPair κ L R) :
    let := layerComponent_normal h
    IsPGroup 2 ((LayerActor L R) ⧸ layerComponent L R) := by
  let := layerComponent_normal h
  let q := QuotientGroup.mk' (layerKernel L R)
  have hg : layerComponent L R ⊔ (R.subgroupOf (L ⊔ R)).map q = ⊤ := by
    rw [← Subgroup.map_sup, (codisjoint_subgroupOf_sup L R).eq_top]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  exact isPGroup_quotient_of_sup_eq_top _ _ (h.relative_radical.isPGroup.map q) hg

/-- The semisimple-section consequence of Theorem A supplies SQTK on the actual component. -/
theorem layerComponent_sqtk (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : CentralMarking L) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    IsSQTK KnownSimple.IsKnownSimple (layerComponent L R) := by
  let := layerComponent_quasisimple h e hz
  have hs : ChapterA.Section02.IsSectionOf (layerComponent L R) M :=
    (ChapterA.Section02.IsSectionOf.subgroup (layerComponent L R)).trans
      (ChapterA.Section02.IsSectionOf.of_surjective (QuotientGroup.mk' (layerKernel L R))
        (QuotientGroup.mk'_surjective _))
  have hm : ChapterA.Section02.IsSemisimple (layerComponent L R) := by
    apply top_unique
    exact le_sSup (show IsComponent (layerComponent L R) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  exact ⟨ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    h.sqtk.stronglyQuasithin h.sqtk.isKGroup hs hm, hs.isKGroup h.sqtk.isKGroup⟩

/-- Apply the full known-simple B.5.1 classifier to the genuine offender-generated actor. -/
theorem layer_source_conclusion (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : CentralMarking L) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    layerComponent L R ≤ offenderSubgroup (layerAction L R) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((layerAction L R).comp (offenderSubgroup (layerAction L R)).subtype)
        ((layerComponent L R).subgroupOf (offenderSubgroup (layerAction L R)))) := by
  let := layerComponent_normal h
  let := layerComponent_quasisimple h e hz
  exact SourceCompletion.ff_quasisimple_source_conclusion (layerAction L R) (layerComponent L R)
    (layerActor_component_quotient_two h) (layerActor_twoCore h e hz)
    (layerComponent_sqtk h e hz) layerAction_faithful (layerAction_isFFModule h e)


/-- The canonical moved/fixed section of the actual initial action. -/
@[expose] def layerSection (h : SmallMSPair κ L R) :
    MovedSection (layerAction L R) (layerComponent L R) := by
  let := layerComponent_normal h
  exact MovedSection.ofNormal _ _

/-- When the kernel is Q, the component is the actual even hexacode group. -/
theorem layerComponent_equiv_hexEven
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M) :
    Nonempty (layerComponent L R ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  obtain ⟨a, _⟩ := exists_quotient_hexacode_equiv h e hz
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  exact ⟨(quotientImageEquiv K _ _ hc).trans
    ((cComponentTwoCoreQuotientEquiv h.component).symm.trans
      ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans a))⟩

/-- When the kernel is E, the component is the actual alternating-six group. -/
theorem layerComponent_equiv_alternating
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hc : layerKernel L R = extensionKernel h) :
    Nonempty (layerComponent L R ≃* alternatingGroup (Fin 6)) := by
  exact ⟨(quotientImageEquiv K _ _ hc).trans (extensionKernel_component_equiv h e)⟩

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels

/-- The faithful-cover case has an irreducible six-dimensional moved space and a fixed complement. -/
theorem layer_moved_hexEven
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M) :
    IsIrrPlus (layerAction L R) (layerComponent L R)
        (moved (layerAction L R) (layerComponent L R)) ∧
      Module.finrank (ZMod 2) (moved (layerAction L R) (layerComponent L R)) = 6 ∧
      IsCompl (moved (layerAction L R) (layerComponent L R))
        (fixedSpace (layerAction L R) (layerComponent L R)) := by
  obtain ⟨hCJ, ⟨c⟩⟩ := layer_source_conclusion h e hz
  obtain ⟨a⟩ := layerComponent_equiv_hexEven h e hz hc
  let b := (subgroupOfEquivOfLe hCJ).trans a
  have hs : c.sectionData.space.toSubmodule =
      moved (layerAction L R) (layerComponent L R) := by
    rw [c.sectionData.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hCJ]
  have hi := (IsIrrPlus.subgroupOf_iff (layerAction L R) (layerComponent L R)
    (offenderSubgroup (layerAction L R)) hCJ _).mp (source_tripleSix _ c b).1
  rw [hs] at hi
  have hc' := source_split _ c b
  rw [hs, fixedSpace_subgroupOf _ _ _ hCJ] at hc'
  exact ⟨hi, ((LinearEquiv.ofEq _ _ hs).finrank_eq).symm.trans
    (source_moved_finrank _ c b), hc'⟩

private theorem natural_of_layer_source
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    (hCJ : C ≤ offenderSubgroup ρ)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (C.subgroupOf (offenderSubgroup ρ)))
    (a : C ≃* alternatingGroup (Fin 6)) (s : MovedSection ρ C) :
    IsIrrPlus ρ C (moved ρ C) ∧
      IsAlternatingNatural (s.action.comp C.subtype) 6 := by
  obtain ⟨hi, ⟨E⟩⟩ := C27Source.AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans a)
  have hs : c.sectionData.space.toSubmodule =
      moved ρ C := by
    rw [c.sectionData.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hCJ]
  have hi' := (IsIrrPlus.subgroupOf_iff ρ C
    (offenderSubgroup ρ) hCJ _).mp hi
  rw [hs] at hi'
  let φ := (subgroupOfEquivOfLe hCJ).symm
  have hm : (moved ρ C).map
      (LinearMap.id : V →ₗ[ZMod 2] V) =
      moved (ρ.comp (offenderSubgroup ρ).subtype)
        (C.subgroupOf (offenderSubgroup ρ)) := by
    rw [Submodule.map_id, moved_comp_map, map_subgroupOf_eq_of_le hCJ]
  let T := c.sectionData.componentEmbeddingEquiv s φ
    (LinearMap.id : V →ₗ[ZMod 2] V)
    (fun _ _ hh => hh) (fun _ _ => rfl) hm
  refine ⟨hi', ⟨{ groupEquiv := T.groupEquiv.trans E.groupEquiv
                  linearEquiv := T.linearEquiv.trans E.linearEquiv
                  intertwines := ?_ }⟩⟩
  intro g v
  change E.linearEquiv (T.linearEquiv (_)) = _
  rw [T.intertwines, E.intertwines]
  rfl

attribute [local irreducible] layerSection

/-- The cubic-kernel case has the actual natural A₆ central quotient; no natural subgroup is assumed. -/
theorem layer_moved_alternating
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = extensionKernel h) :
    IsIrrPlus (layerAction L R) (layerComponent L R)
        (moved (layerAction L R) (layerComponent L R)) ∧
      IsAlternatingNatural ((layerSection h).action.comp (layerComponent L R).subtype) 6 :=
  (layerComponent_equiv_alternating h e hc).elim fun a =>
    natural_of_layer_source (layerAction L R) (layerComponent L R)
      (layer_source_conclusion h e hz).1
      (Classical.choice (layer_source_conclusion h e hz).2) a (layerSection h)

/-- The two initial-action alternatives follow from the original exceptional MS hypotheses. -/
theorem initial_layer_alternatives
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    (layerKernel L R = pCore 2 M ∧
      IsIrrPlus (layerAction L R) (layerComponent L R)
        (moved (layerAction L R) (layerComponent L R)) ∧
      Module.finrank (ZMod 2) (moved (layerAction L R) (layerComponent L R)) = 6 ∧
      IsCompl (moved (layerAction L R) (layerComponent L R))
        (fixedSpace (layerAction L R) (layerComponent L R))) ∨
    (layerKernel L R = extensionKernel h ∧
      IsIrrPlus (layerAction L R) (layerComponent L R)
        (moved (layerAction L R) (layerComponent L R)) ∧
      IsAlternatingNatural ((layerSection h).action.comp (layerComponent L R).subtype) 6) :=
  (centralOmega_centralizer_cases h e hz).elim
    (fun hc => Or.inl ⟨hc, layer_moved_hexEven h e hz hc⟩)
    (fun hc => Or.inr ⟨hc, layer_moved_alternating h e hz hc⟩)

private theorem moved_commutator_eq_of_irrPlus
    {A D : Type*} [Group A] [Finite A] [Group D]
    (U Z B : Subgroup A) [U.Normal] [Z.Normal] [B.Normal]
    [IsElementaryAbelian 2 U]
    (q : A →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set A))
    (hZX : Z ≤ U) (hK : IsPPerfect 2 B) (hne : ¬ B ≤ centralizer (Z : Set A))
    (hi : IsIrrPlus (NormalElementaryQuotient.representation U q hq hker) (B.map q)
      (moved (NormalElementaryQuotient.representation U q hq hker) (B.map q))) :
    ⁅Z, B⁆ = ⁅U, B⁆ := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let Y := ⁅Z, B⁆
  have hYX : Y ≤ U := (commutator_le_left Z B).trans hZX
  let W : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (Y.subgroupOf U).toAddSubgroup
  have hW : B.map q ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    rintro _ ⟨k, hk, rfl⟩ v hv
    change ((ρ (q k) v).toMul : A) ∈ Y
    rw [NormalElementaryQuotient.representation_apply]
    exact (inferInstance : Y.Normal).conj_mem _ hv k
  have hWI : W ≤ moved ρ (B.map q) := by
    change W ≤ subspaceCommutator (NormalElementaryQuotient.representation U q hq hker) ⊤ (B.map q)
    rw [← NormalElementaryQuotient.commutatorSpace_eq U q hq hker B]
    intro v hv
    exact commutator_mono hZX le_rfl hv
  rcases hi.eq_or_le_fixedSpace ρ hW hWI with heq | hfix
  · apply le_antisymm (commutator_mono hZX le_rfl)
    intro y hy
    have hv : Additive.ofMul (⟨y, (commutator_le_left U B) hy⟩ : U) ∈
        moved ρ (B.map q) := by
      change _ ∈ subspaceCommutator (NormalElementaryQuotient.representation U q hq hker) ⊤ (B.map q)
      rw [← NormalElementaryQuotient.commutatorSpace_eq U q hq hker B]
      exact hy
    rw [← heq] at hv
    exact hv
  · have hcent : Y ≤ centralizer (B : Set A) := by
      intro y hy k hk
      have hf := hfix (show Additive.ofMul (⟨y, hYX hy⟩ : U) ∈ W from hy)
        (q.subgroupMap B ⟨k, hk⟩)
      have he := congrArg (fun v : Additive U => (v.toMul : A)) hf
      change ((ρ (q k) (Additive.ofMul ⟨y, hYX hy⟩)).toMul : A) = y at he
      rw [NormalElementaryQuotient.representation_apply] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hid : ⁅Y, B⁆ = Y := commutator_isPPerfect_idempotent B Z hK
      ((IsElementaryAbelian.isPGroup 2 U).to_le hZX) le_normalizer_of_normal
    have hb : ⁅Z, B⁆ = ⊥ := hid.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hcent)
    exact (hne (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))).elim

/-- The full initial moved space is Irr+ regardless of the covering kernel. -/
theorem layer_moved_irrPlus
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    IsIrrPlus (layerAction L R) (layerComponent L R)
      (moved (layerAction L R) (layerComponent L R)) :=
  (centralOmega_centralizer_cases h e hz).elim
    (fun hc => (layer_moved_hexEven h e hz hc).1)
    (fun hc => (layer_moved_alternating h e hz hc).1)

/-- MS93 (3.2): the central-omega orbit and X have the same moved subgroup. Their underlying subgroups remain distinct. -/
theorem omegaOrbit_moved_eq
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ⁅MSCentralOrbit.omegaOrbit (R.subgroupOf (L ⊔ R)), K⁆ = ⁅X, K⁆ := by
  let := h.relative_normal
  exact moved_commutator_eq_of_irrPlus X
    (MSCentralOrbit.omegaOrbit (R.subgroupOf (L ⊔ R))) K
    (QuotientGroup.mk' (layerKernel L R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
    (MSCentralOrbit.omegaOrbit_le_centralOmega _ h.relative_radical.twoCore_le
      h.relative_self_centralizing) h.relative_twoPerfect
    (MSCentralOrbit.component_not_centralizes_omegaOrbit K (R.subgroupOf (L ⊔ R))
      h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_product
      h.relative_characteristic) (layer_moved_irrPlus h e hz)

private theorem normal_action_natural
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [C.Normal]
    (hn : IsAlternatingNatural (ρ.comp C.subtype) 6)
    (a : C ≃* alternatingGroup (Fin 6)) (g : D) :
    MulAut.congr a (MulAut.conjNormal g) ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  obtain ⟨b⟩ := hn
  apply Representation.BinaryAlternatingSixNaturalNormalizer.natural_of_coordinates
    (ρ.comp C.subtype)
    ⟨b.groupEquiv, Or.inl ⟨b.linearEquiv, b.intertwines⟩⟩ a
    (MulAut.conjNormal g) (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g))
  intro c v
  change ρ g (ρ c v) = ρ (g * c * g⁻¹) (ρ g v)
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun x : D => ρ x v)
      (show g * (c : D) = (g * c * g⁻¹) * g by group)

/-- Every ambient action preserves the natural A₆ automorphism subgroup when the cubic kernel acts trivially on X. -/
theorem layer_action_natural_of_cubic_kernel
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = extensionKernel h) :
    letI := layerComponent_normal h
    ∀ (a : layerComponent L R ≃* alternatingGroup (Fin 6)) (g : LayerActor L R),
      MulAut.congr a (MulAut.conjNormal g) ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  let := layerComponent_normal h
  exact normal_action_natural (layerSection h).action (layerComponent L R)
    (layer_moved_alternating h e hz hc).2

open Theory.SpecificGroups.SymmetricSix in
/-- Both literal source parabolic types are preserved in the cubic-kernel case, in any component marking. -/
theorem layer_parabolic_types_of_cubic_kernel
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = extensionKernel h) :
    letI := layerComponent_normal h
    ∀ (a : layerComponent L R ≃* alternatingGroup (Fin 6)) (g : LayerActor L R),
      (∃ c : alternatingGroup (Fin 6),
        a6DuadStabilizer.map (MulAut.congr a (MulAut.conjNormal g)).toMonoidHom =
          a6DuadStabilizer.map (MulAut.conj c).toMonoidHom) ∧
      (∃ c : alternatingGroup (Fin 6),
        a6SynthemeStabilizer.map (MulAut.congr a (MulAut.conjNormal g)).toMonoidHom =
          a6SynthemeStabilizer.map (MulAut.conj c).toMonoidHom) := by
  let := layerComponent_normal h
  intro a g
  exact (_root_.AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics.natural_iff_preserves_source_parabolic_types _).mp
    (layer_action_natural_of_cubic_kernel h e hz hc a g)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
