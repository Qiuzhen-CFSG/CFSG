module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.RadicalAction

/-!
# The literal common-pair radical action and quotient

The completed flag geometry gives R₂ = C_T(V₂). The elementary pair P lies
in T and contains V₂, hence lies in the original R₂. Its faithful Bʰ factor
has order q². The two-parameter shear description bounds the R₂ action image
by q², giving equality of the literal normalizer-action images. Equality of
these images transfers the original radical commutator to [V,P] = V₂.

On PV the action kernel is exactly V. The first and second isomorphism
theorems identify the actual quotient PV/V with its conjugation image and
prove that it is elementary of order q². The original-counterexample
application constructs the pair and discharges every local comparison premise.
Only the permitted preceding 11.3.7 inputs remain with final assembly owner
qt-d-1222-shadow-common-core. No compatibility of the fields on P and V is
used, and q=4 is retained.

This does not yet place PV/V inside the required covering group. Construction
of V_K and the original SL₃ block, that placement and the invariant-complement
application, and the final local cores remain with
qt-d-1222-shadow-common-identification.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
printed p.774, second and third paragraphs of refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

private theorem flag_plane_eq
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) : f.Vi 1 = (SL3.flag D S a).Vi 1 := by
  have he := SL3.flag_unique D S a 1 (f.space 1) (f.dimension 1) (f.invariant 1)
  exact congrArg (Coordinates.sl3 a).preimage he

theorem pairCore_le_plane_radical
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hB : axis V H = f.Vi 1) : pairCore V H h ≤ f.Ri 1 := by
  have he := flag_plane_eq a f
  have hR : f.Ri 1 = (SL3.flag D S a).Ri 1 := congrArg (localRadical T L) he
  rw [hR,←SL3.RadicalAction.sylow_centralizer_plane D S a]
  let := pairCore_elementary s hh hz
  have hBT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow H (T.subtype s.outside.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hc
    rwa [map_subgroupOf_eq_of_le s.outside.1.1.2] at hc
  refine le_inf ((pairCore_le_core (V := V) hh).trans hBT) ?_
  have hBP : (SL3.flag D S a).Vi 1 ≤ pairCore V H h :=
    (he.symm.trans hB.symm).le.trans le_sup_left
  exact (pairCore V H h).le_centralizer.trans (centralizer_le hBP)

private theorem radical_action_coordinates
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (r : (SL3.flag D S a).Ri 1) (v : V) :
    (SL3.RadicalAction.vectorEquiv D S a
      (V.normalizerMonoidHom (inclusion ((localRadical_le_sylow _).trans S.sylow_normalizes) r) v)).toAdd =
      SL3.RadicalAction.radicalOperator D S a r
        (SL3.RadicalAction.vectorEquiv D S a v).toAdd :=
  SL3.RadicalAction.alignedAction_projection D S a
    (SL3.RadicalAction.radicalInclusion D S a r) v

theorem plane_radical_action_card_le
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) :
    Nat.card (V.normalizerMonoidHom.comp
      (inclusion ((localRadical_le_sylow (L := L) (f.Vi 1)).trans S.sylow_normalizes))).range ≤
        (2 ^ S.field.degree) ^ 2 := by
  have he : f.Ri 1 = (SL3.flag D S a).Ri 1 :=
    congrArg (localRadical T L) (flag_plane_eq a f)
  have hgeneral (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
      (hR : R = (SL3.flag D S a).Ri 1) :
      Nat.card (V.normalizerMonoidHom.comp (inclusion (hRT.trans S.sylow_normalizes))).range ≤
        (2 ^ S.field.degree) ^ 2 := by
    subst R
    let e := SL3.RadicalAction.vectorEquiv D S a
    let ρ := V.normalizerMonoidHom.comp (inclusion (hRT.trans S.sylow_normalizes))
    let w : V := e.symm (Multiplicative.ofAdd ![0,0,1])
    let j : ρ.range → S.field.Carrier × S.field.Carrier := fun u =>
      ((e (u.val w)).toAdd 0,(e (u.val w)).toAdd 1)
    have hj : Function.Injective j := by
      rintro ⟨u,r,hr⟩ ⟨v,t,ht⟩ hsame
      subst u
      subst v
      obtain ⟨r₀,r₁,hr⟩ := SL3.RadicalAction.radicalOperator_shear D S a r
      obtain ⟨t₀,t₁,ht⟩ := SL3.RadicalAction.radicalOperator_shear D S a t
      have hcoords (r : (SL3.flag D S a).Ri 1) (v : V) :
          (e (ρ r v)).toAdd = SL3.RadicalAction.radicalOperator D S a r (e v).toAdd :=
        radical_action_coordinates a r v
      have hc : r₀ = t₀ ∧ r₁ = t₁ := by
        change ((e (ρ r w)).toAdd 0,(e (ρ r w)).toAdd 1) =
          ((e (ρ t w)).toAdd 0,(e (ρ t w)).toAdd 1) at hsame
        simpa [hcoords,hr,ht,w] using hsame
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hcoords,hcoords,hr,ht,hc.1,hc.2]
    have hb := Nat.card_le_card_of_injective j hj
    simpa only [Nat.card_prod,S.field.card_eq,pow_two] using hb
  exact hgeneral _ (localRadical_le_sylow _) he

theorem pairCore_action_eq_radical
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (c : PairNaturalMarking V H h S.field) (hm : c.multiplicity = 2)
    (hB : axis V H = f.Vi 1) :
    (V.normalizerMonoidHom.comp
      (inclusion ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)))).range =
    (V.normalizerMonoidHom.comp
      (inclusion ((localRadical_le_sylow (L := L) (f.Vi 1)).trans S.sylow_normalizes))).range := by
  let P := pairCore V H h
  let A := (axis V H).map (MulAut.conj h).toMonoidHom
  let hPV := (pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)
  let hRV := (localRadical_le_sylow (L := L) (f.Vi 1)).trans S.sylow_normalizes
  let ρ := V.normalizerMonoidHom.comp (inclusion hPV)
  let τ := V.normalizerMonoidHom.comp (inclusion hRV)
  have hz := pair_intersection_eq_bot s hf hk
  have hPR := pairCore_le_plane_radical a f s hh hz hB
  have hle : ρ.range ≤ τ.range := by
    rintro _ ⟨p,rfl⟩
    exact ⟨inclusion hPR p,rfl⟩
  let j : A →* ρ.range :=
    ρ.rangeRestrict.comp (inclusion (show A ≤ P from le_sup_right))
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply bot_unique
    intro x hx
    have he : inclusion hPV (inclusion (show A ≤ P from le_sup_right) x) ∈
        V.normalizerMonoidHom.ker := congrArg Subtype.val hx
    rw [normalizerMonoidHom_ker] at he
    apply Subtype.ext
    exact (conjugate_axis_faithful s hf hh hk).le ⟨x.property,he⟩
  have hA : Nat.card A = (2 ^ S.field.degree) ^ 2 := by
    rw [card_map_of_injective (MulAut.conj h).injective,c.axis_card s hh hz,hm]
  have hlo := Nat.card_le_card_of_injective j hj
  rw [hA] at hlo
  exact eq_of_le_of_card_ge hle ((plane_radical_action_card_le a f).trans hlo)

omit [Finite G] in
private theorem commutator_le_of_action_range_le
    {A B : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (hB : B ≤ normalizer (V : Set G))
    (he : (V.normalizerMonoidHom.comp (inclusion hA)).range ≤
      (V.normalizerMonoidHom.comp (inclusion hB)).range) : ⁅V,A⁆ ≤ ⁅V,B⁆ := by
  rw [commutator_comm V A,commutator_comm V B]
  apply commutator_le.mpr
  intro a ha v hv
  obtain ⟨b,hb⟩ := he (show V.normalizerMonoidHom (inclusion hA ⟨a,ha⟩) ∈
    (V.normalizerMonoidHom.comp (inclusion hA)).range from ⟨⟨a,ha⟩,rfl⟩)
  have hx := congrArg (fun z : MulAut V => (z ⟨v,hv⟩ : G)) hb
  have hh : ⁅(b : G),v⁆ = ⁅a,v⁆ := congrArg (fun z : G => z * v⁻¹) hx
  exact hh ▸ commutator_mem_commutator b.property hv

theorem pairCore_seed_commutator_eq_plane
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (c : PairNaturalMarking V H h S.field) (hm : c.multiplicity = 2)
    (hB : axis V H = f.Vi 1) : ⁅V,pairCore V H h⁆ = f.Vi 1 := by
  have he := pairCore_action_eq_radical a f s hh hf hk c hm hB
  have hc := le_antisymm (commutator_le_of_action_range_le _ _ he.le)
    (commutator_le_of_action_range_le _ _ he.ge)
  rw [hc]
  have hp := flag_plane_eq a f
  rw [hp]
  exact SL3.RadicalAction.commutator_eq_plane D S a

/-- The action kernel on the product PV is exactly V. -/
theorem pairJoin_seed_centralizer
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h) :
    (pairCore V H h ⊔ V) ⊓ centralizer (V : Set G) = V := by
  let := D.elementary
  have hn := (pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    have hx' : x ∈ (pairCore V H h : Set G) * (V : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hx
    obtain ⟨p,hp,v,hv,rfl⟩ := hx'
    have hpc : p ∈ centralizer (V : Set G) := by
      have he := (centralizer (V : Set G)).mul_mem hc
        ((centralizer (V : Set G)).inv_mem (V.le_centralizer hv))
      simpa only [mul_inv_cancel_right] using he
    have hpV := (pairCore_fixed_eq_axis s hf hh hk).le ⟨hp,hpc⟩
    exact V.mul_mem hpV.1 hv
  · exact le_inf le_sup_right V.le_centralizer

/-- The original conjugation on V by the actual product PV. -/
@[expose] def pairJoinAction
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H) :
    (pairCore V H h ⊔ V : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (sup_le
    ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)) V.le_normalizer))

theorem pairJoinAction_ker
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h) :
    (pairJoinAction s hh).ker = V.subgroupOf (pairCore V H h ⊔ V) := by
  ext x
  change inclusion _ x ∈ V.normalizerMonoidHom.ker ↔ (x : G) ∈ V
  rw [normalizerMonoidHom_ker]
  change (x : G) ∈ centralizer (V : Set G) ↔ (x : G) ∈ V
  constructor
  · intro hx
    exact (pairJoin_seed_centralizer s hh hf hk).le ⟨x.property,hx⟩
  · intro hx
    exact ((pairJoin_seed_centralizer s hh hf hk).ge hx).2

theorem pairJoinAction_range
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H) :
    (pairJoinAction s hh).range =
      (V.normalizerMonoidHom.comp
        (inclusion ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)))).range := by
  let := D.elementary
  have hn := (pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    have hx : (x : G) ∈ (pairCore V H h : Set G) * (V : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
      exact x.property
    obtain ⟨p,hp,v,hv,he⟩ := hx
    refine ⟨⟨p,hp⟩,?_⟩
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change p * (w : G) * p⁻¹ = (x : G) * (w : G) * (x : G)⁻¹
    rw [←he]
    have hc : v * (w : G) * v⁻¹ = w :=
      mul_inv_eq_iff_eq_mul.mpr (V.le_centralizer w.property v hv)
    calc
      _ = p * (v * (w : G) * v⁻¹) * p⁻¹ := by rw [hc]
      _ = _ := by group
  · rintro _ ⟨p,rfl⟩
    exact ⟨inclusion le_sup_left p,rfl⟩

/-- The literal quotient map PV → PV/V identifies its quotient faithfully
with its actual conjugation image, retaining the map on every element. -/
theorem pairJoin_quotient_action
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h) :
    let := normal_subgroupOf_sup_of_le_normalizer
      ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s))
    ∃ e : ((pairCore V H h ⊔ V : Subgroup G) ⧸
        V.subgroupOf (pairCore V H h ⊔ V)) ≃* (pairJoinAction s hh).range,
      ∀ x, (e (QuotientGroup.mk' _ x)).val = pairJoinAction s hh x := by
  let := normal_subgroupOf_sup_of_le_normalizer
    ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s))
  let e := (QuotientGroup.quotientMulEquivOfEq (pairJoinAction_ker s hh hf hk).symm).trans
    (QuotientGroup.quotientKerEquivRange (pairJoinAction s hh))
  exact ⟨e,fun _ => rfl⟩

/-- The literal quotient PV/V is elementary of order q². Normality and the
second-isomorphism map use the original ambient embeddings. -/
theorem pairCore_seed_quotient
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (c : PairNaturalMarking V H h S.field) (hm : c.multiplicity = 2) :
    let := normal_subgroupOf_sup_of_le_normalizer
      ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s))
    IsElementaryAbelian 2
      ((pairCore V H h ⊔ V : Subgroup G) ⧸ V.subgroupOf (pairCore V H h ⊔ V)) ∧
    Nat.card ((pairCore V H h ⊔ V : Subgroup G) ⧸
      V.subgroupOf (pairCore V H h ⊔ V)) = (2 ^ S.field.degree) ^ 2 := by
  let P := pairCore V H h
  have hn := (pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)
  let := normal_subgroupOf_sup_of_le_normalizer hn
  let := normal_subgroupOf_of_le_normalizer hn
  have hz := pair_intersection_eq_bot s hf hk
  let := pairCore_elementary s hh hz
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient P V hn
  refine ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,?_⟩
  rw [←Nat.card_congr e.toEquiv]
  have hB : Nat.card (V.subgroupOf P) = (2 ^ S.field.degree) ^ 2 := by
    rw [←inf_subgroupOf_left V P]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show P ⊓ V ≤ P from inf_le_left)).toEquiv]
    rw [pairCore_inf_seed hh,c.axis_card s hh hz,hm]
  have he := (V.subgroupOf P).card_mul_index
  change Nat.card (V.subgroupOf P) * Nat.card (P ⧸ V.subgroupOf P) = Nat.card P at he
  rw [hB,c.card,hm] at he
  have hhq : (2 ^ S.field.degree) ^ (2 * 2) =
      (2 ^ S.field.degree) ^ 2 * (2 ^ S.field.degree) ^ 2 := by
    rw [←pow_add]
  rw [hhq] at he
  exact Nat.mul_left_cancel (by positivity : 0 < (2 ^ S.field.degree) ^ 2) he

/-- The actual counterexample supplies the full radical action, with no
action-image or multiplicity premise. The preceding 11.3.7 inputs retain
their final discharge in qt-d-1222-shadow-common-core. -/
theorem source_pair_radical_action
    (cL : Coordinates D S.field) (flag : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    ∃ (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
      (c : PairNaturalMarking V H h S.field),
      c.multiplicity = 2 ∧
      pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
      pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
      Nat.card (pairCore V H h) = (2 ^ S.field.degree) ^ 4 ∧
      (T : Subgroup G) ≤ normalizer (pairCore V H h : Set G) ∧
      (let := normal_subgroupOf_sup_of_le_normalizer
        ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s))
       IsElementaryAbelian 2
        ((pairCore V H h ⊔ V : Subgroup G) ⧸ V.subgroupOf (pairCore V H h ⊔ V)) ∧
       Nat.card ((pairCore V H h ⊔ V : Subgroup G) ⧸
         V.subgroupOf (pairCore V H h ⊔ V)) = (2 ^ S.field.degree) ^ 2 ∧
       ∃ e : ((pairCore V H h ⊔ V : Subgroup G) ⧸
         V.subgroupOf (pairCore V H h ⊔ V)) ≃* (pairJoinAction s hh).range,
         ∀ x, (e (QuotientGroup.mk' _ x)).val = pairJoinAction s hh x) ∧
      ∀ f : InvariantFlag (.sl3 a), f.IsUnique →
        axis V H = f.Vi 1 ∧ pairCore V H h ⊓ V = f.Vi 1 ∧
        pairCore V H h ≤ f.Ri 1 ∧
        ⁅V,pairCore V H h⁆ = f.Vi 1 ∧
        (V.normalizerMonoidHom.comp
          (inclusion ((pairCore_le_core (V := V) hh).trans (core_normalizes_seed s)))).range =
        (V.normalizerMonoidHom.comp
          (inclusion ((localRadical_le_sylow (L := L) (f.Vi 1)).trans S.sylow_normalizes))).range ∧
        (pairJoinAction s hh).range = (V.normalizerMonoidHom.comp
          (inclusion ((localRadical_le_sylow (L := L) (f.Vi 1)).trans S.sylow_normalizes))).range := by
  obtain ⟨a,c,hc2,hI,hK,hcard,hT,hflag⟩ := source_pair_two_summands
    cL flag s p hc hh hm hfixed hf hnot hmodel hG2 R hR cK A hA hHall hAL
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  have hquot := pairCore_seed_quotient s hh hf hk c hc2
  refine ⟨a,c,hc2,hI,hK,hcard,hT,
    ⟨hquot.1,hquot.2,pairJoin_quotient_action s hh hf hk⟩,fun f hu => ?_⟩
  obtain ⟨hB,hPV⟩ := hflag f hu
  have hact := pairCore_action_eq_radical a f s hh hf hk c hc2 hB
  exact ⟨hB,hPV,pairCore_le_plane_radical a f s hh hz hB,
    pairCore_seed_commutator_eq_plane a f s hh hf hk c hc2 hB,
    hact,(pairJoinAction_range s hh).trans hact⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
