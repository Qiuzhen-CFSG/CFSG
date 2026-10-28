module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNinePlaneAction
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedCubicResidual
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.SpecificGroups.BinaryComponentResidual

/-!
# The fixed plane moves the original Case-I component

The original cubic residual moves V₂, and a Sylow element outside S
exchanges V₂ with V₁. Its conjugate therefore normalizes and moves V₁.
If the selected C-component centralized V₁, it would persist in N_G(V₁).
The actual local three-rank bound and the centerless, outer-two quotient
facts identify the component with that normalizer's prime-to-three residual,
which contains the moving conjugate. This is a contradiction.

The Nine-row consumer constructs the component and both planes from one
marker. The concrete A₆, G₂(2)′, PSL₄(2), and PSL₅(2) quotient facts are
supplied internally. The earlier 15.1.14 residual centralization and the
component catalogue remain source obligations.

Source: Aschbacher--Smith 15.1.25(3), printed p.1102, using A.3.18.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- An exchanged moved plane supplies the noncentrality in original 15.1.25(3).
The ambient rank bound is derived in its literal two-local normalizer. -/
theorem CaseIComponentData.fixed_plane_not_centralizes
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (V1 V2 Y : Subgroup G) (hZ : d.Z1 ≤ V1)
    (hV1 : IsPGroup 2 V1) (hV2 : V2 ≠ ⊥)
    (hY : (primeToResidual 3 Y).map Y.subtype = Y)
    (hmove : ⁅V2,Y⁆ = V2) (t : G)
    (ht : V2.map (MulAut.conj t).toMonoidHom = V1) :
    ¬ V1 ≤ centralizer (d.L : Set G) := by
  let e := (MulAut.conj t).toMonoidHom
  let A := Y.map e
  have hV1ne : V1 ≠ ⊥ := by
    intro he
    exact hV2 ((map_eq_bot_iff_of_injective V2 (MulAut.conj t).injective).mp (ht.trans he))
  have hAn : A ≤ normalizer (V1 : Set G) := by
    have hn : Y ≤ normalizer (V2 : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr hmove.le
    have hh := map_mono (f := e) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective,ht] at hh
    exact hh
  have hAid : (primeToResidual 3 A).map A.subtype = A := by
    rw [← map_embedded_primeToResidual_of_hom 3 Y e,hY]
  have hAmove : ⁅V1,A⁆ ≠ ⊥ := by
    have he := congrArg (map e) hmove
    rw [map_commutator,ht] at he
    exact fun hz => hV1ne (he.symm.trans hz)
  have hN : primeRank 3 (normalizer (V1 : Set G)) ≤ 2 :=
    (hG.twoLocal_sqtk ⟨V1,hV1ne,hV1,rfl⟩).stronglyQuasithin 3 Nat.prime_three (by decide)
  intro hc
  exact d.L_isCComponent_in_G1.not_centralizes_of_cubic_movement
    (centralizer_le hZ) hf.1 hf.2.1 hf.2.2 hN hAn hAid hAmove
    (le_centralizer_iff.mp hc)

/-- Discharge the concrete quotient facts for the four indicated binary rows.
The four source rows are A₆, G₂(2)′, SL₄(2), and SL₅(2). -/
theorem CaseIComponentData.fixed_plane_not_centralizes_of_model
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (he : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* SL(4, ZMod 2)) ∨
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* SL(5, ZMod 2)))
    (V1 V2 Y : Subgroup G) (hZ : d.Z1 ≤ V1)
    (hV1 : IsPGroup 2 V1) (hV2 : V2 ≠ ⊥)
    (hY : (primeToResidual 3 Y).map Y.subtype = Y)
    (hmove : ⁅V2,Y⁆ = V2) (t : G)
    (ht : V2.map (MulAut.conj t).toMonoidHom = V1) :
    ¬ V1 ≤ centralizer (d.L : Set G) := by
  rcases he with ha | hg | h4 | h5
  · obtain ⟨e⟩ := ha
    exact d.fixed_plane_not_centralizes hG
      (Facts.of_equiv e Theory.SpecificGroups.BinaryComponentResidual.alternatingSix)
      V1 V2 Y hZ hV1 hV2 hY hmove t ht
  · obtain ⟨e⟩ := hg
    exact d.fixed_plane_not_centralizes hG
      (Facts.of_equiv e Theory.SpecificGroups.BinaryComponentResidual.g2)
      V1 V2 Y hZ hV1 hV2 hY hmove t ht
  · obtain ⟨e⟩ := h4
    exact d.fixed_plane_not_centralizes hG
      (Facts.of_equiv e (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inl rfl)))
      V1 V2 Y hZ hV1 hV2 hY hmove t ht
  · obtain ⟨e⟩ := h5
    exact d.fixed_plane_not_centralizes hG
      (Facts.of_equiv e (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl)))
      V1 V2 Y hZ hV1 hV2 hY hmove t ht

/-- The same marked Nine choice supplies the component and proves fixed-plane
movement in every centerless rank-two, outer-two quotient row. No new action,
normalizer, rank or plane-exchange premise is assumed. -/
theorem PreparedChosenModule.source_caseI_nine_fixed_plane_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 ∧ d.S.relIndex (T : Subgroup G) = 2 ∧
      (Facts (d.L ⧸ pCore 2 d.L) → ¬ V1 ≤ centralizer (d.L : Set G)) := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  let V2 := ⁅V,R⁆
  let Y := (primeToResidual 3 C).map C.subtype
  have hC : C = M ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
    change M ⊓ centralizer (d.Z1 : Set G) = _
    rw [hdZ]
  have hplanes : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧
      V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
    let P (Z : Subgroup G) : Prop :=
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 4 ∧ Nat.card (⁅V,R⁆ : Subgroup G) = 4 ∧
        (V ⊓ centralizer (R : Set G)) ⊔ ⁅V,R⁆ = V ∧
        (V ⊓ centralizer (R : Set G)) ⊓ ⁅V,R⁆ = ⊥ ∧
        Z ≤ V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
  have haction : d.S.relIndex (T : Subgroup G) = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ d.S →
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
    let P (Z : Subgroup G) : Prop :=
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      S.relIndex (T : Subgroup G) = 2 ∧
        ∀ t ∈ (T : Subgroup G), t ∉ S →
          ⁅V,R⁆.map (MulAut.conj t).toMonoidHom = V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := by
      obtain ⟨hi,_,_,_,he⟩ := source_nine_plane_action T hM.1.2 h.normalized h9 v K hv hK hcard hSyl
      exact ⟨hi,fun t ht hs => (he t ht hs).2⟩
    exact (congrArg P hdZ).mpr hp
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,hplanes.1,hplanes.2.1,hplanes.2.2.1,
    hplanes.2.2.2.1,hplanes.2.2.2.2,haction.1,?_⟩
  intro hf
  let := hq
  have hV2ne : V2 ≠ ⊥ := by
    intro he
    have hc := hplanes.2.1
    rw [he,card_bot] at hc
    omega
  have hYid : (primeToResidual 3 Y).map Y.subtype = Y := by
    rw [←map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 C) le_rfl]
  have he : ⁅V,Y⁆ = V2 := by
    dsimp only [Y,V2,R]
    rw [hC]
    exact marked_primeToResidual_commutator M V h.normalized v K hK hcard
  have hYp : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hYV : Y ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have hV2Y : ⁅V2,Y⁆ = V2 := by
    rw [←he]
    exact commutator_isPPerfect_idempotent Y V hYp (IsElementaryAbelian.isPGroup 2 V) hYV
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ d.S := by
    by_contra! hh
    have he := relIndex_eq_one.mpr hh
    rw [haction.1] at he
    contradiction
  exact d.fixed_plane_not_centralizes hG hf V1 V2 Y hplanes.2.2.2.2
    ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2ne hYid hV2Y t
    (haction.2 t ht htS)
end CFSG.Quasithin.Chapter15.Section01
