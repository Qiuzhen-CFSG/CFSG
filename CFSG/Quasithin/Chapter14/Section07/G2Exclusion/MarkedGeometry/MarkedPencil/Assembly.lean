module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly.ActorCases

/-!
# The marked-pencil deductions of 14.7.55

The earlier local orders and actual Sylow action mark V/V₁ as a doubly
singular line and V₂/V₁ as one of its points. In the Weyl case the earlier
identity [V,L₁]V₁ = V removes the nonsingular invariant planes. These derived
markings feed the three-line pencil, actor calculations and residual action
on the same literal quotient U/(V₁.subgroupOf U).

The two assembled theorems prove clauses (1)–(6),(8), conditional on the
actual natural/Weyl identification and earlier source identities, together
with the precise earlier B.4.6 offender premises. No marking, centralizer,
fixed-space, family, residual quotient or transitivity conclusion is an
input. The output records below only organize proved conclusions.

Here H denotes the local source group; normality of U is relative to H.
The faithful actor D is covered by π and embedded by i in the actual G₂(2)
model, compatibly with conjugation on U/V₁. The full and derived possibilities
are constructed respecting i. The elementary eight and clause (8) also have
an explicit full-actor realization when D is only the derived group; that
realization is not asserted to be a subgroup of D.

The parent qt-14-07-g2-exclusion supplies the identification and earlier
local identities. The B.4.6 premises are owned by qt-b-04-g2; their source
instantiation remains with the parent source assembly. The separate marked
geometry owner supplies clause (7) and integrates all eight clauses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.55,
printed p.1066, PDF p.1083; B.4.6, printed pp.88–90. Existing model imports
use the attributed ATLAS port (LICENSES/ATLAS.txt).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Representation Representation.BinaryOffender Subgroup
open Actors SourceActions SourceActions.ResidualAction

variable {H D W : Type*} [Group H] [Finite H] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- All the marked-pencil conclusions on the same source quotient. The
actor alternatives retain the embedding, and the extended full actor is
explicit in the derived case. This record is an output, never a hypothesis
used to establish the source assertions. -/
structure SourceConclusions
    (U V₁ V₂ V : Subgroup H) [(V₁.subgroupOf U).Normal]
    [MulDistribMulAction D (U ⧸ V₁.subgroupOf U)]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (f : SingularMap W)
    (e : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (π : H →* D) (i : D →* Model (ZMod 2)) (T : Sylow 2 H)
    (p : SingularPoints (ZMod 2)) : Prop where
  line : ∃ L : ZeroProductLine (ZMod 2),
    (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry e).line L ∧ pointOnLine p L
  point : (transportGeometry f.geometry e).point p =
    (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))
  pencil_card : Nat.card (quotientPencil (transportGeometry f.geometry e)
    ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 3
  span_card : Nat.card (quotientPencilSpan (transportGeometry f.geometry e)
    ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 8
  actors :
    (∃ j : commutator (Model (ZMod 2)) ≃* D, (∀ g, i (j g) = g.val) ∧
      DerivedPencilConclusions (H := D) (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
        ((perpendicular f p).toAddSubgroup.toSubgroup.map e.toMonoidHom)) ∨
    (∃ j : Model (ZMod 2) ≃* D, (∀ g, i (j g) = g) ∧
      FullPencilConclusions (H := D) (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
        ((perpendicular f p).toAddSubgroup.toSubgroup.map e.toMonoidHom))
  full_extension :
    letI := modelQuotientAction σ e
    FullPencilConclusions (H := Model (ZMod 2)) (transportGeometry f.geometry e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
      ((perpendicular f p).toAddSubgroup.toSubgroup.map e.toMonoidHom)
  extension_restrict : ∀ (d : D) (q : U ⧸ V₁.subgroupOf U),
    (modelQuotientAction σ e).smul (i d) q = d • q
  source_families :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let span := quotientPencilSpan (transportGeometry f.geometry e) ((V₂.subgroupOf U).map q)
    let B := _root_.fixingSubgroup D (span : Set (U ⧸ V₁.subgroupOf U)) ⊓
      (commutator (Model (ZMod 2))).comap i
    let family := {S | ∃ b ∈ B, S = commutatorAction (Subgroup.zpowers b) (U ⧸ V₁.subgroupOf U)}
    letI := modelQuotientAction σ e
    let A := _root_.fixingSubgroup (Model (ZMod 2)) (span : Set (U ⧸ V₁.subgroupOf U))
    family = {S | ∃ w ∈ (perpendicular f p).toAddSubgroup.toSubgroup.map e.toMonoidHom,
      S = commutatorSubgroup A (U ⧸ V₁.subgroupOf U) (Subgroup.zpowers w)}
  offenders : IsFFModule (σ.comp i) →
    (∃ j : D ≃* Model (ZMod 2), ∀ d, j d = i d) ∧
      {B : Subgroup D | IsBestOffender (σ.comp i) B} =
        Set.range (fun h : H =>
          (_root_.fixingSubgroup D
            (quotientPencilSpan (transportGeometry f.geometry e)
              ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
                Set (U ⧸ V₁.subgroupOf U))).map (MulAut.conj (π h)).toMonoidHom)
  residual_quotient : Nonempty
    ((sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
      pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃* Equiv.Perm (Fin 3))
  residual_commutator :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let span := quotientPencilSpan (transportGeometry f.geometry e) ((V₂.subgroupOf U).map q)
    let preimage := (span.comap q).map U.subtype
    (⁅preimage,sourceResidual V₂⁆.subgroupOf U).map q = span
  residual_transitive :
    ∀ B ∈ quotientPencil (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))),
      ∀ C ∈ quotientPencil (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))),
      ∃ y ∈ sourceResidual V₂, B.map (quotientActor σ e (i (π y))) = C

omit [Finite H] in
private theorem derived_le_cover_range (π : H →* D) (hπ : Function.Surjective π)
    (i : D →* Model (ZMod 2)) (hJ : commutator (Model (ZMod 2)) ≤ i.range) :
    commutator (Model (ZMod 2)) ≤ (i.comp π).range := by
  intro g hg
  obtain ⟨d,hd⟩ := hJ hg
  obtain ⟨h,rfl⟩ := hπ d
  exact ⟨h,hd⟩

omit [Finite H] in
private theorem source_family_comparison
    {Q : Type*} [Group Q] [MulDistribMulAction D Q]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2))
    (hJ : commutator (Model (ZMod 2)) ≤ i.range)
    (e : Multiplicative W ≃* Q)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (σ (i d) w)))
    (geom : QuotientGeometry Q) (P R : Subgroup Q)
    (hcalc : letI := modelQuotientAction σ e
      FullPencilConclusions (H := Model (ZMod 2)) geom P R) :
    let span := quotientPencilSpan geom P
    let B := _root_.fixingSubgroup D (span : Set Q) ⊓
      (commutator (Model (ZMod 2))).comap i
    let family := {S | ∃ b ∈ B, S = commutatorAction (Subgroup.zpowers b) Q}
    letI := modelQuotientAction σ e
    let A := _root_.fixingSubgroup (Model (ZMod 2)) (span : Set Q)
    family = {S | ∃ w ∈ R, S = commutatorSubgroup A Q (Subgroup.zpowers w)} := by
  let := modelQuotientAction σ e
  let span := quotientPencilSpan geom P
  let A := _root_.fixingSubgroup (Model (ZMod 2)) (span : Set Q)
  let B := A ⊓ commutator (Model (ZMod 2))
  let C := _root_.fixingSubgroup D (span : Set Q) ⊓
    (commutator (Model (ZMod 2))).comap i
  have hC (d : D) : d ∈ C ↔ i d ∈ B := by
    change (d ∈ _root_.fixingSubgroup D (span : Set Q) ∧
      i d ∈ commutator (Model (ZMod 2))) ↔
      (i d ∈ _root_.fixingSubgroup (Model (ZMod 2)) (span : Set Q) ∧
        i d ∈ commutator (Model (ZMod 2)))
    rw [mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
    have hsm (q : Q) : i d • q = d • q := modelQuotientAction_restrict σ i e he d q
    simp only [hsm]
  have hmove (d : D) : commutatorAction (Subgroup.zpowers d) Q =
      commutatorAction (Subgroup.zpowers (i d)) Q := by
    unfold commutatorAction commutatorSubgroup
    congr 1
    ext q
    constructor
    · rintro ⟨⟨a,ha⟩,v,hv,hq⟩
      have ha' : i a ∈ Subgroup.zpowers (i d) := by
        rw [← MonoidHom.map_zpowers]
        exact Subgroup.mem_map_of_mem i ha
      refine ⟨⟨i a,ha'⟩,v,hv,?_⟩
      change q = v⁻¹ * (i a • v)
      change q = v⁻¹ * (a • v) at hq
      exact hq.trans (congrArg (fun w => v⁻¹ * w)
        (modelQuotientAction_restrict σ i e he a v).symm)
    · rintro ⟨⟨a,ha⟩,v,hv,hq⟩
      rw [← MonoidHom.map_zpowers] at ha
      obtain ⟨d',hd',rfl⟩ := ha
      refine ⟨⟨d',hd'⟩,v,hv,?_⟩
      change q = v⁻¹ * (d' • v)
      change q = v⁻¹ * (i d' • v) at hq
      exact hq.trans (congrArg (fun w => v⁻¹ * w)
        (modelQuotientAction_restrict σ i e he d' v))
  have hfamily : {S | ∃ d ∈ C, S = commutatorAction (Subgroup.zpowers d) Q} =
      {S | ∃ b ∈ B, S = commutatorAction (Subgroup.zpowers b) Q} := by
    ext S
    constructor
    · rintro ⟨d,hd,rfl⟩
      exact ⟨i d,(hC d).mp hd,hmove d⟩
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨d,rfl⟩ := hJ hb.2
      exact ⟨d,(hC d).mpr hb,(hmove d).symm⟩
  have hfamilies := hcalc.2.families
  rw [hcalc.1.fixedSpan] at hfamilies
  exact hfamily.trans hfamilies

/-- Clauses (1)–(6),(8) in the natural case. The local marking and both
actor branches are proved; only the specified earlier B.4.6 inputs remain. -/
theorem natural_source_conclusions
    (U V₁ V₂ V : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] [MulDistribMulAction D (U ⧸ V₁.subgroupOf U)]
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* D) (hπ : Function.Surjective π)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Model (ZMod 2)) ≤ i.range) (hk : IsPGroup 2 (i.comp π).ker)
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) =
      e (Multiplicative.ofAdd (action (ZMod 2) (i d) w)))
    (hact : ∀ (h : H) (u : U), action (ZMod 2) (i (π h))
        (e.symm (QuotientGroup.mk' (V₁.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (T : Sylow 2 H) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hT₂ : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim (action (ZMod 2)) A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim (action (ZMod 2)) A)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender (action (ZMod 2)) B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    ∃ p : SingularPoints (ZMod 2),
      SourceConclusions U V₁ V₂ V (action (ZMod 2)) naturalMap e π i T p := by
  obtain ⟨L,p,hL,hp,hpL,hc,hs,hquot,hcomm,htrans⟩ :=
    natural_source_actions U V₁ V₂ V h12 h2V hVU hcentral (i.comp π)
      (derived_le_cover_range π hπ i hJ) hk e hact hcardV hcardV₂ T hTV hT₂
  have hext : letI := modelQuotientAction (action (ZMod 2)) e
      FullPencilConclusions (H := Model (ZMod 2)) (transportGeometry naturalMap.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
        ((perpendicular naturalMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
    let := modelQuotientAction (action (ZMod 2)) e
    apply natural_source_full U V₁ V₂ e (MulEquiv.refl _) _ p hp.symm
    intro g w
    change e (Multiplicative.ofAdd (action (ZMod 2) g
      (e.symm (e (Multiplicative.ofAdd w))).toAdd)) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨p, {
    line := ⟨L,hL,hpL⟩
    point := hp
    pencil_card := hc
    span_card := hs
    actors := ?_
    full_extension := hext
    extension_restrict := modelQuotientAction_restrict _ i e he
    source_families := source_family_comparison _ i hJ e he _ _ _ hext
    offenders := ?_
    residual_quotient := hquot
    residual_commutator := hcomm
    residual_transitive := htrans }⟩
  · rcases actor_equivalences i hi hJ with ⟨j,hj⟩ | ⟨j,hj⟩
    · refine Or.inl ⟨j,hj,?_⟩
      apply natural_source_derived U V₁ V₂ e j _ p hp.symm
      intro g w
      rw [he,hj]
    · refine Or.inr ⟨j,hj,?_⟩
      apply natural_source_full U V₁ V₂ e j _ p hp.symm
      intro g w
      rw [he,hj]
  · exact quotient_ff_bestOffenders π hπ U V₁ V₂ (action (ZMod 2)) i hi e he hJ
      hRank hOne hTwo hB46 naturalMap naturalMap_equivariant p hp.symm

/-- Clauses (1)–(6),(8) in the weyl case. The local marking and both
actor branches are proved; only the specified earlier B.4.6 inputs remain. -/
theorem weyl_source_conclusions
    (U V₁ V₂ V L₁ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] [MulDistribMulAction D (U ⧸ V₁.subgroupOf U)]
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hlocal : ⁅V,L₁⁆ ⊔ V₁ = V)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* D) (hπ : Function.Surjective π)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Model (ZMod 2)) ≤ i.range) (hk : IsPGroup 2 (i.comp π).ker)
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) =
      e (Multiplicative.ofAdd (traceZeroAction (ZMod 2) (i d) w)))
    (hact : ∀ (h : H) (u : U), traceZeroAction (ZMod 2) (i (π h))
        (e.symm (QuotientGroup.mk' (V₁.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (T : Sylow 2 H) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hT₂ : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim (traceZeroAction (ZMod 2)) A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim (traceZeroAction (ZMod 2)) A)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender (traceZeroAction (ZMod 2)) B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    ∃ p : SingularPoints (ZMod 2),
      SourceConclusions U V₁ V₂ V (traceZeroAction (ZMod 2)) weylMap e π i T p := by
  obtain ⟨L,p,hL,hp,hpL,hc,hs,hquot,hcomm,htrans⟩ :=
    weyl_source_actions U V₁ V₂ V L₁ h12 h2V hVU hlocal hcentral (i.comp π)
      (derived_le_cover_range π hπ i hJ) hk e hact hcardV hcardV₂ T hTV hT₂
  have hext : letI := modelQuotientAction (traceZeroAction (ZMod 2)) e
      FullPencilConclusions (H := Model (ZMod 2)) (transportGeometry weylMap.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))
        ((perpendicular weylMap p).toAddSubgroup.toSubgroup.map e.toMonoidHom) := by
    let := modelQuotientAction (traceZeroAction (ZMod 2)) e
    apply weyl_source_full U V₁ V₂ e (MulEquiv.refl _) _ p hp.symm
    intro g w
    change e (Multiplicative.ofAdd (traceZeroAction (ZMod 2) g
      (e.symm (e (Multiplicative.ofAdd w))).toAdd)) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨p, {
    line := ⟨L,hL,hpL⟩
    point := hp
    pencil_card := hc
    span_card := hs
    actors := ?_
    full_extension := hext
    extension_restrict := modelQuotientAction_restrict _ i e he
    source_families := source_family_comparison _ i hJ e he _ _ _ hext
    offenders := ?_
    residual_quotient := hquot
    residual_commutator := hcomm
    residual_transitive := htrans }⟩
  · rcases actor_equivalences i hi hJ with ⟨j,hj⟩ | ⟨j,hj⟩
    · refine Or.inl ⟨j,hj,?_⟩
      apply weyl_source_derived U V₁ V₂ e j _ p hp.symm
      intro g w
      rw [he,hj]
    · refine Or.inr ⟨j,hj,?_⟩
      apply weyl_source_full U V₁ V₂ e j _ p hp.symm
      intro g w
      rw [he,hj]
  · exact quotient_ff_bestOffenders π hπ U V₁ V₂ (traceZeroAction (ZMod 2)) i hi e he hJ
      hRank hOne hTwo hB46 weylMap weylMap_equivariant p hp.symm

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
