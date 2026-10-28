module
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Assembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.AmbientTransport

/-!
# Ambient assembly of the marked local action

The source marking is proved inside H, then transported through H ↪ G.
Its pencil calculations discharge every 14.7.55 premise in the local
14.7.56 consumer. Earlier local identities remain explicit, as permitted
by the conditional source contract. In particular L acts in G, not in H.

Source: Aschbacher–Smith, 14.7.55–56, printed p.1066.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalAssembly
open Atlas.G2 Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise
open MarkedPencil MarkedPencil.Assembly MarkedPencil.SourceActions.ResidualAction
open LocalParabolics LocalParabolics.ThreeOffenderOrbit AmbientTransport Assembly
variable {G : Type*} [Group G] [Finite G]

/-- Every clause of 14.7.56, with pointwise fixation of family members,
the actual action image and the literal quotient by its centralizer. -/
def LocalConclusions
    (U Z V V₂ L₂ Y T : Subgroup G) [(Z.subgroupOf U).Normal]
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U)) (p : SingularPoints (ZMod 2)) : Prop :=
    let W := pencilSpanPreimage U Z geom p
    let N := normalizer (V₂ : Set G)
    let C := centralizer (W : Set G)
    pencilPreimages U Z geom p = conjugateLineFamily V Y ∧
    pencilPreimages U Z geom p = ambientConjugatesThrough V V₂ ∧
    W = generatedLineFamily V Y ∧
    N = L₂ ⊔ Y ⊔ T ∧
    ⁅W,L₂⁆ = V₂ ∧
    (∀ P ∈ pencilPreimages U Z geom p, L₂ ≤ normalizer P) ∧
    (∃ hYL : Y ≤ normalizer L₂, coreQuotientAction L₂ Y hYL = 1) ∧
    (∃ hspan : N ≤ normalizer (W : Set G),
      (ambientAction N W hspan).ker = C.subgroupOf N ∧
      (ambientAction N W hspan).ker.map N.subtype = C ∧
      (ambientAction N W hspan).range = MulAction.stabilizer (MulAut W) (V₂.subgroupOf W)) ∧
    C ≤ N ∧ ∃ hnormal : (C.subgroupOf N).Normal,
      let := hnormal
      Nonempty ((N ⧸ C.subgroupOf N) ≃*
        MulAction.stabilizer (MulAut W) (V₂.subgroupOf W))

private theorem local_of_pencil
    (H U V V₁ V₂ L L₂ Y T : Subgroup G) [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 U]
    (hY : Y = localResidual H V₂)
    (hVU : V ≤ U) (hV₁ : V₁ ≤ V₂) (hV₂ : V₂ ≤ V)
    (hHU : H ≤ normalizer U) (hTH : T ≤ H) (hLV : L ≤ normalizer V)
    (htransV : ∀ W : Subgroup G, W ≤ V → Nat.card W = Nat.card V₂ →
      ∃ l : L, conjugate V₂ l = W)
    (hcomm : ⁅V,L₂⁆ = V₂)
    (hcommY : ⁅L₂,Y⁆ ≤ L₂ ⊓ centralizer (V₂ : Set G))
    (hcore : L₂ ⊓ centralizer (V₂ : Set G) = L₂.pCoreIn 2)
    (hLT : L₂ ⊔ T ≤ normalizer (V₂ : Set G))
    (hC : centralizer (V₂ : Set G) = Y ⊔ (T ⊓ centralizer (V₂ : Set G)))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT))
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y)
    (action : Y →* MulAut (U ⧸ V₁.subgroupOf U))
    (hact : ∀ y : Y, ∀ u : U,
      ∃ hu : (y : G) * (u : G) * (y : G)⁻¹ ∈ U,
      action y (QuotientGroup.mk' (V₁.subgroupOf U) u) =
        QuotientGroup.mk' (V₁.subgroupOf U) ⟨(y : G) * (u : G) * (y : G)⁻¹,hu⟩)
    (m : ThreeOffenderOrbit.BinaryG2Module)
    (E : Multiplicative m.Space ≃* (U ⧸ V₁.subgroupOf U))
    (p : SingularPoints (ZMod 2))
    (s : AmbientPencilConclusions U V₁ V V₂ Y T m E action p)
    (hD : Nat.card V₂ = 4) (hZ : Nat.card V₁ = 2)
    (hcommH : ⁅V₂,H.pCoreIn 2⁆ = V₁)
    (hstar : ∀ q : H.pCoreIn 2, ∀ u : U,
      QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨(q : G) * (u : G) * (q : G)⁻¹,
          (mem_normalizer_iff.mp (hHU (pCoreIn_le 2 H q.property)) u).mp u.property⟩ =
        QuotientGroup.mk' (V₁.subgroupOf U) u) :
    LocalConclusions U V₁ V V₂ L₂ Y T (transportGeometry m.singularMap.geometry E) p := by
  obtain ⟨line,hmark,horbit,htrans⟩ := s.line
  obtain ⟨eYT⟩ := s.residual_quotient
  exact source_pencil_full_local_deductions H U V V₁ V₂ L L₂ Y T hY hVU hV₁ hV₂
    hHU hTH hLV htransV hcomm hcommY hcore hLT hC hfull hTV hTY
    action hact m E p line hmark horbit htrans s.span_card hD hZ hcommH hstar s.commutator eYT

/-- Conditional 14.7.55–56 in the actual ambient group. All marked-pencil
inputs of the local-action theorem are discharged by the natural/Weyl
calculations. The listed local actions and commutator formulas are earlier
Section 14.7 identities; the module identification is the 14.7.54 input. -/
theorem source_marked_local_geometry
    {D : Type*} [Group D] (H : Subgroup G)
    (m : BinaryG2Module)
    (U V₁ V₂ V L₁ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] [MulDistribMulAction D (U ⧸ V₁.subgroupOf U)]
    [IsElementaryAbelian 2 (U.map H.subtype)]
    [((V₁.map H.subtype).subgroupOf (U.map H.subtype)).Normal]
    (hZ : Nat.card V₁ = 2)
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hlocal : ⁅V,L₁⁆ ⊔ V₁ = V)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* D) (hπ : Function.Surjective π)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Model (ZMod 2)) ≤ i.range) (hk : IsPGroup 2 (i.comp π).ker)
    (e : Multiplicative (m.Space) ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) =
      e (Multiplicative.ofAdd (m.action (i d) w)))
    (hact : ∀ (h : H) (u : U), m.action (i (π h))
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
      rank A = 1 → 2 ≤ fixedCodim m.action A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim m.action A)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender m.action B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    let Ua := U.map H.subtype
    let Za := V₁.map H.subtype
    let Va := V.map H.subtype
    let Da := V₂.map H.subtype
    let Ya := (sourceResidual V₂).map H.subtype
    let Ta := (T : Subgroup H).map H.subtype
    let E := e.trans (quotientEmbedding H.subtype H.subtype_injective U V₁)
    ∀ (L L₂ : Subgroup G)
    (_hLV : L ≤ normalizer Va)
    (_htransV : ∀ W : Subgroup G, W ≤ Va → Nat.card W = Nat.card Da →
      ∃ l : L, conjugate Da l = W)
    (_hcomm : ⁅Va,L₂⁆ = Da)
    (_hcommY : ⁅L₂,Ya⁆ ≤ L₂ ⊓ centralizer (Da : Set G))
    (_hcore : L₂ ⊓ centralizer (Da : Set G) = L₂.pCoreIn 2)
    (hLT : L₂ ⊔ Ta ≤ normalizer (Da : Set G))
    (_hC : centralizer (Da : Set G) = Ya ⊔ (Ta ⊓ centralizer (Da : Set G)))
    (_hfull : Function.Surjective (ambientAction (L₂ ⊔ Ta) Da hLT))
    (_hcommH : ⁅Da,H.pCoreIn 2⁆ = Za)
    (τ : H →* MulAut (Ua ⧸ Za.subgroupOf Ua))
    (_hactual : ∀ (h : H) (u : Ua),
      ∃ hu : (h : G) * (u : G) * (h : G)⁻¹ ∈ Ua,
      τ h (QuotientGroup.mk' (Za.subgroupOf Ua) u) =
        QuotientGroup.mk' (Za.subgroupOf Ua) ⟨(h : G) * (u : G) * (h : G)⁻¹,hu⟩)
    (_hstar : ∀ h ∈ pCore 2 H, τ h = 1),
    ∃ p : SingularPoints (ZMod 2),
      SourceConclusions U V₁ V₂ V m.action m.singularMap e π i T p ∧
      HexagonConclusions (transportGeometry m.singularMap.geometry E) ∧
      AmbientPencilConclusions Ua Za Va Da Ya Ta m E (residualAction H V₂ τ) p ∧
      LocalConclusions Ua Za Va Da L₂ Ya Ta (transportGeometry m.singularMap.geometry E) p := by
  dsimp only
  intro L L₂ hLV htransV hcomm hcommY hcore hLT hC hfull hcommH τ hactual hstar
  obtain ⟨p,s,_⟩ := source_marked_geometry m U V₁ V₂ V L₁ h12 h2V hVU hlocal hcentral
    π hπ i hi hJ hk e he hact hcardV hcardV₂ T hTV hT₂ hRank hOne hTwo hB46
  let θ := quotientEmbedding H.subtype H.subtype_injective U V₁
  have hτ : ∀ h q, τ h (θ q) = θ (quotientActor m.action e (i (π h)) q) := by
    intro h q
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) q
    have hh := quotientActor_source_apply U V₁ m.action (i.comp π) e hact h u
    simp only [MonoidHom.comp_apply] at hh
    rw [hh]
    obtain ⟨hu,hh⟩ := hactual h (U.equivMapOfInjective H.subtype H.subtype_injective u)
    exact hh
  have a := source_ambient_pencil H U V₁ V₂ V (h12.trans (h2V.trans hVU)) hZ
    m e π i T p s hact τ hτ
  have hHU : H ≤ normalizer (U.map H.subtype : Set G) := by
    have hn := U.le_normalizer_map H.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  have hTaV := (map_mono hTV).trans (V.le_normalizer_map H.subtype)
  have hTaY := (map_mono (sourceResidual_normalized V₂ T hT₂)).trans
    ((sourceResidual V₂).le_normalizer_map H.subtype)
  have hD : Nat.card V₂ = 4 := by
    have hc := (lift_support_basic U V₁ (h12.trans (h2V.trans hVU))
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))).2.2.1
    change Nat.card (linePreimage U V₁ _) = _ at hc
    rw [linePreimage_image U V₁ V₂ (h2V.trans hVU) h12, hcardV₂, hZ] at hc
    exact hc
  have hyact : ∀ y : (sourceResidual V₂).map H.subtype, ∀ u : U.map H.subtype,
      ∃ hu : (y : G) * (u : G) * (y : G)⁻¹ ∈ U.map H.subtype,
      residualAction H V₂ τ y (QuotientGroup.mk' ((V₁.map H.subtype).subgroupOf (U.map H.subtype)) u) =
        QuotientGroup.mk' ((V₁.map H.subtype).subgroupOf (U.map H.subtype))
          ⟨(y : G) * (u : G) * (y : G)⁻¹,hu⟩ := by
    intro y u
    let ey := (sourceResidual V₂).equivMapOfInjective H.subtype H.subtype_injective
    obtain ⟨v,rfl⟩ := ey.surjective y
    have hh : residualAction H V₂ τ (ey v) = τ v := by
      change τ (ey.symm (ey v)) = τ v
      rw [ey.symm_apply_apply]
    rw [hh]
    exact hactual v u
  have hstar' : ∀ q : H.pCoreIn 2, ∀ u : U.map H.subtype,
      QuotientGroup.mk' ((V₁.map H.subtype).subgroupOf (U.map H.subtype))
        ⟨(q : G) * (u : G) * (q : G)⁻¹,
          (mem_normalizer_iff.mp (hHU (pCoreIn_le 2 H q.property)) u).mp u.property⟩ =
        QuotientGroup.mk' ((V₁.map H.subtype).subgroupOf (U.map H.subtype)) u := by
    intro q u
    obtain ⟨h,hh,heq⟩ := q.property
    obtain ⟨hu,hq⟩ := hactual h u
    rw [hstar h hh] at hq
    change (h : G) = (q : G) at heq
    simpa only [heq, MulAut.one_apply] using hq.symm
  refine ⟨p,s,⟨realizedIncidence_girth _,realizedIncidence_diameter _,
    realizedCollinearity_no_four_cycle _⟩,a,?_⟩
  exact local_of_pencil H (U.map H.subtype) (V.map H.subtype) (V₁.map H.subtype)
    (V₂.map H.subtype) L L₂ ((sourceResidual V₂).map H.subtype) ((T : Subgroup H).map H.subtype)
    (residual_map H V₂) (map_mono hVU) (map_mono h12) (map_mono h2V) hHU
    (map_subtype_le _) hLV htransV hcomm hcommY hcore hLT hC hfull hTaV hTaY
    (residualAction H V₂ τ) hyact m (e.trans θ) p a
    (by rw [card_map_of_injective H.subtype_injective,hD])
    (by rw [card_map_of_injective H.subtype_injective,hZ]) hcommH hstar'

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalAssembly
