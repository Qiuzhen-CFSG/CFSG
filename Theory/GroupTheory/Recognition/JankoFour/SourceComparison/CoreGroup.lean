module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoreComparison
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.QuadraticLift
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist

/-!
# Comparing the actual extraspecial cores and their six-cover actions

Lift the prescribed James quadratic-space comparison to the original
extraspecial groups, then correct it to intertwine the same cubic scalars.
Every six-cover actor commutes with those scalars. Its discrepancy is an
inner automorphism trivial on the quotient; the cubic fixed-space theorem
forces that discrepancy to vanish. Thus one core isomorphism intertwines
the whole original perfect six-cover and retains the marked involution.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
The full normalizer and H comparisons still require the involutory splitting
comparison and its literal quotient marking.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

/-- The original marked involution as an element of the original core. -/
noncomputable def coreMarker : core z :=
  ⟨⟨z,mem_centralizer_singleton_iff.mpr rfl⟩,centralizer_center_le_core h (by
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_centralizer_singleton_iff.mp y.property)))⟩

omit [IsExtraspecial 2 (core z)] in
theorem coreMarker_central : coreMarker h ∈ center (core z) := by
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp q.val.property))

omit [IsExtraspecial 2 (core z)] in
theorem coreMarker_ne_one : coreMarker h ≠ 1 := by
  intro he
  have hz : z = 1 := congrArg (fun x : core z => x.val.val) he
  have hi := h.involution
  rw [hz,orderOf_one] at hi
  contradiction

omit [IsExtraspecial 2 (core z)] in
/-- Every actual core isomorphism preserves the original central involution. -/
theorem coreEquiv_marker (ψ : core z ≃* core z') : ψ (coreMarker h) = coreMarker h' := by
  let c : center (core z') := centerCongr ψ ⟨_,coreMarker_central h⟩
  let d : center (core z') := ⟨_,coreMarker_central h'⟩
  have hc : c ≠ 1 := by
    intro hc
    exact coreMarker_ne_one h (ψ.map_eq_one_iff.mp (congrArg Subtype.val hc))
  have hd : d ≠ 1 := fun he => coreMarker_ne_one h' (congrArg Subtype.val he)
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center (core z'))).mp
    (IsExtraspecial.center_order_p 2 (core z'))
  exact congrArg Subtype.val ((hw c hc).trans (hw d hd).symm)

/-- Lift the prescribed full James-module comparison to the original cores. -/
theorem exists_coreGroup_equiv :
    ∃ ψ : core z ≃* core z',
      (∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
        coreSpaceComparison h e X h' e' X'
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ∧
      ψ (coreMarker h) = coreMarker h' := by
  obtain ⟨ψ,hψ⟩ := QuadraticLift.exists_equiv (coreSpaceComparison h e X h' e' X')
    (coreSpaceComparison_quadratic h e X h' e' X')
  exact ⟨ψ,hψ,coreEquiv_marker h h' ψ⟩

/-- The original cubic scalar subgroup in six-cover coordinates. -/
noncomputable abbrev cubicScalars := (cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X)

/-- The original conjugation action, retaining both subgroup inclusions. -/
noncomputable def cubicScalarsAction : cubicScalars e X →* MulAut (core z) :=
  (MulAut.conjNormal : centralizer z →* MulAut (core z)).comp
    ((cubicCentralizerInH e X).subtype.comp (cubicScalars e X).subtype)

/-- The compared six-cover induces a literal target action of those same scalars. -/
noncomputable def cubicScalarsTargetAction
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X') :
    cubicScalars e X →* MulAut (core z') :=
  (MulAut.conjNormal : centralizer z' →* MulAut (core z')).comp
    ((cubicCentralizerInH e' X').subtype.comp
      (φ.toMonoidHom.comp (cubicScalars e X).subtype))

omit [IsExtraspecial 2 (core z)] in
include h in
theorem cubicScalars_card : Nat.card (cubicScalars e X) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (cubicSylowImage_le_centralizer h e X)).toEquiv,
    cubicSylowImage_card h e X]

private theorem linearAction_coreAction (g : centralizer z) (v : CoreSpace (z := z)) :
    ExtraspecialSquare.linearAction (core z) (MulAut.conjNormal g) v =
      coreBinaryRepresentation h (QuotientGroup.mk' (core z) g) v := by
  obtain ⟨q,hq⟩ := QuotientGroup.mk'_surjective (center (core z)) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center (core z)) q) :=
    congrArg Additive.ofMul hq.symm
  rw [hv,ExtraspecialSquare.linearAction_apply,coreBinaryRepresentation_apply]
  change Additive.ofMul (quotientAut (center (core z)) (MulAut.conjNormal g)
    (QuotientGroup.mk' (center (core z)) q)) = _
  rw [quotientAut_apply_mk]
  exact (congrArg Additive.ofMul (coreQuotientAction_mk h g q)).symm

/-- The cubic-equivariant group lift uses the very same six-cover map and
native quotient coordinates, with no supplied core-group isomorphism. -/
theorem exists_coreGroup_equiv_cubic
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) :
    ∃ ψ : core z ≃* core z',
      (∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
        coreSpaceComparison h e X h' e' X'
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ∧
      ψ (coreMarker h) = coreMarker h' ∧
      ∀ a : cubicScalars e X, ∀ q : core z,
        ψ (MulAut.conjNormal a.val.val q) = MulAut.conjNormal (φ a.val).val (ψ q) := by
  have he (a : cubicScalars e X) (v : CoreSpace (z := z)) :
      coreSpaceComparison h e X h' e' X'
        (ExtraspecialSquare.linearAction (core z) (cubicScalarsAction e X a) v) =
      ExtraspecialSquare.linearAction (core z') (cubicScalarsTargetAction e X e' X' φ a)
        (coreSpaceComparison h e X h' e' X' v) := by
    change coreSpaceComparison h e X h' e' X'
      (ExtraspecialSquare.linearAction (core z) (MulAut.conjNormal a.val.val) v) =
        ExtraspecialSquare.linearAction (core z') (MulAut.conjNormal (φ a.val).val)
          (coreSpaceComparison h e X h' e' X' v)
    rw [linearAction_coreAction h,linearAction_coreAction h',
      cubicNativeComparison_core h e X h' e' X' φ hφ]
    exact coreSpaceComparison_intertwines h e X h' e' X' _ v
  obtain ⟨ψ,hψ,hψa⟩ := QuadraticLift.exists_equiv_threeAction
    (coreSpaceComparison h e X h' e' X') (coreSpaceComparison_quadratic h e X h' e' X')
    (cubicScalars_card h e X) (cubicScalarsAction e X) (cubicScalarsTargetAction e X e' X' φ) he
  exact ⟨ψ,hψ,coreEquiv_marker h h' ψ,hψa⟩


private theorem coreEquiv_action_quotient
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (ψ : core z ≃* core z')
    (hψ : ∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
      coreSpaceComparison h e X h' e' X'
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))
    (c : cubicCentralizerInH e X) :
    quotientAut (center (core z')) (MulAut.congr ψ (MulAut.conjNormal c.val)) =
      quotientAut (center (core z')) (MulAut.conjNormal (φ c).val) := by
  apply MulEquiv.ext
  intro v
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (core z')) v
  obtain ⟨q,rfl⟩ := ψ.surjective q
  rw [quotientAut_apply_mk,quotientAut_apply_mk]
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
  apply Additive.ofMul.injective
  rw [hψ]
  have hh := coreSpaceComparison_intertwines h e X h' e' X'
    (QuotientGroup.mk' (core z) c.val)
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))
  rw [←cubicNativeComparison_core h e X h' e' X' φ hφ,←hψ q] at hh
  simpa only [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk] using hh

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
include h' in
private theorem targetScalars_fixedFree
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (ha : (cubicScalars e X).map φ.toMonoidHom = cubicScalars e' X')
    (v : core z' ⧸ center (core z'))
    (hv : ∀ a : cubicScalars e X,
      quotientAut (center (core z')) (cubicScalarsTargetAction e X e' X' φ a) v = v) : v = 1 := by
  apply (cubicAction_fixed_iff h' e' X' v).mp
  intro x
  have hx : (x.val : centralizer z') ∈ cubicSylowImage e' X' :=
    mem_map_of_mem (CubicLift.subgroup e').subtype x.property
  let c : cubicCentralizerInH e' X' := ⟨x.val,cubicSylowImage_le_centralizer h' e' X' hx⟩
  obtain ⟨a,ha',he⟩ := (show c ∈ (cubicScalars e X).map φ.toMonoidHom from ha ▸ hx)
  have hh := hv ⟨a,ha'⟩
  change quotientAut (center (core z')) (MulAut.conjNormal (φ a).val) v = v at hh
  change φ a = c at he
  rw [he] at hh
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (core z')) v
  rw [cubicAction_mk]
  exact (quotientAut_apply_mk _ _ _).symm.trans hh

/-- Cubic compatibility removes every inner discrepancy in the six-cover action. -/
theorem coreEquiv_intertwines_cover
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (ha : (cubicScalars e X).map φ.toMonoidHom = cubicScalars e' X')
    (ψ : core z ≃* core z')
    (hψ : ∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
      coreSpaceComparison h e X h' e' X'
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))
    (hψa : ∀ a : cubicScalars e X, ∀ q : core z,
      ψ (MulAut.conjNormal a.val.val q) = MulAut.conjNormal (φ a.val).val (ψ q))
    (c : cubicCentralizerInH e X) (q : core z) :
    ψ (MulAut.conjNormal c.val q) = MulAut.conjNormal (φ c).val (ψ q) := by
  let α := MulAut.congr ψ (MulAut.conjNormal c.val)
  let β : MulAut (core z') := MulAut.conjNormal (φ c).val
  let σ := cubicScalarsTargetAction e X e' X' φ
  have hi (a : cubicScalars e X) :
      MulAut.congr ψ (MulAut.conjNormal a.val.val) = σ a := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := ψ.surjective x
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,σ,
      cubicScalarsTargetAction,MonoidHom.comp_apply,
      Subgroup.subtype_apply,MulEquiv.coe_toMonoidHom] using hψa a x
  have hc (a : cubicScalars e X) : Commute c a.val :=
    Subtype.ext (c.property a.val.val a.property).symm
  have hα (a : cubicScalars e X) : Commute α (σ a) := by
    rw [←hi a]
    exact (((hc a).map (cubicCentralizerInH e X).subtype).map
      (MulAut.conjNormal : centralizer z →* MulAut (core z))).map (MulAut.congr ψ)
  have hβ (a : cubicScalars e X) : Commute β (σ a) :=
    ((((hc a).map φ).map (cubicCentralizerInH e' X').subtype).map
      (MulAut.conjNormal : centralizer z' →* MulAut (core z')))
  have hd : quotientAut (center (core z')) (α*β⁻¹) = 1 := by
    rw [map_mul,map_inv,coreEquiv_action_quotient h e X h' e' X' φ hφ ψ hψ c]
    exact mul_inv_cancel _
  have h1 : α*β⁻¹=1 := QuadraticLift.quotient_trivial_of_commute_fixedFree σ
    (targetScalars_fixedFree e X h' e' X' φ ha) _ hd
    (fun a => (hα a).mul_left (hβ a).inv_left)
  have hh := MulEquiv.congr_fun (mul_inv_eq_one.mp h1) (ψ q)
  simpa only [α,β,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))
variable (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))

include hp hp' in
/-- Construct both group comparisons with one cubic and quadratic marking. -/
theorem exists_cubic_coreGroup_equiv :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X') (ψ : core z ≃* core z'),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
        coreSpaceComparison h e X h' e' X'
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ∧
      ψ (coreMarker h) = coreMarker h' ∧
      ∀ c : cubicCentralizerInH e X, ∀ q : core z,
        ψ (MulAut.conjNormal c.val q) = MulAut.conjNormal (φ c).val (ψ q) := by
  obtain ⟨φ,hφ,ha,hz⟩ := exists_cubicCentralizer_equiv_native h e X hp h' e' X' hp'
  obtain ⟨ψ,hψ,hψz,hψa⟩ := exists_coreGroup_equiv_cubic h e X h' e' X' φ hφ
  exact ⟨φ,ψ,hφ,hz,hψ,hψz,
    coreEquiv_intertwines_cover h e X h' e' X' φ hφ ha ψ hψ hψa⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
