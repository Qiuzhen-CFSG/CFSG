module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
public import Theory.GroupTheory.PCoreLocalSetup
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSpecialUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary

/-!
# The projective action on the scalar-fixed derived radical

In the quadratic unitary octagon, the actual center of the root actor has
exponent three and lies in the full Cartan three-core. The crossed unitary
root commutator therefore lies in C = C_[V,V](Z(R)). Its reflection moves
it to a disjoint root, so R acts nontrivially on C.

The action on the effective Frattini quotient has exactly the original
panel kernel. Thus it gives a faithful binary representation of the same
PSU3 model, with its projection square retained. In degree one the regular
nine-point action and its odd kernel give binary degree at least eight;
the special and projective full actors are both included. In higher degree,
perfectness gives effectiveness and the existing six-b degree bound.

The import-all edges are intentional internal reuse of this recognition
family's root separation, scalar placement and small-panel calculations.
Their public boundaries are unchanged. The original-factor and Chapter 12
applications are in the companion CFSG modules.

Source: Fong--Seitz I (6F), printed p.47. This constructs the scalar-fixed
projective section. The general eight-b degree bound, the nine-b subgroup
exclusion and lower-central persistence remain separate obligations.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The scalar-fixed part of the actual derived radical, with its literal action. -/
@[expose] def unitaryScalarDerivedSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) : RootSection Q split j where
  numerator := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
    centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))
  le_radical := inf_le_left.trans (commutator_le_self _)
  normalized := (le_inf ((rankOne_le_parabolic Q split j).trans
    (radical_commutator_normalized Q split j hKj))
      ((le_centralizer_iff.mp (scalar_centralizes_rankOne Q split j)).trans
        (centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))).le_normalizer)).trans
          inf_normalizer_le_normalizer_inf
  denominator := ⊥
  invariant _ := map_bot _

/-- The actual source scalar center lies in the three-core of the full Cartan. -/
theorem unitary_scalar_le_threeCore
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hsquare : ∀ a, μ (RootLocalCover.projection Q split j (σ a))=J.specialToProjective a) :
    rankOneScalar Q split j ≤ cartanThreeCore Q := by
  let R := rankOne Q split j
  let H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  let Z := rankOneScalar Q split j
  have hZH : Z ≤ H := by
    rintro z ⟨r,hr,rfl⟩
    exact center_le_cartan Q split j hKj hr
  have hcube (r : R) (hr : r ∈ center R) : r^3=1 := by
    have hk : r ∈ (RootLocalCover.projection Q split j).ker := by
      have hh := center_eq_panel_kernel Q split j hKj ▸ hr
      change r ∈ ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker at hh
      rw [MonoidHom.ker_rangeRestrict,panelAction_ker,←RootLocalCover.projection_ker] at hh
      exact hh
    obtain ⟨a,rfl⟩ := hσ r
    have ha : a ∈ J.specialToProjective.ker := by
      change J.specialToProjective a=1
      rw [←hsquare,show RootLocalCover.projection Q split j (σ a)=1 from hk,μ.map_one]
    have hc : a^3=1 := congrArg Subtype.val (J.specialToProjective_ker_cube ⟨a,ha⟩)
    rw [←map_pow,hc,map_one]
  have hZ : IsPGroup 3 Z := by
    intro z
    refine ⟨1,?_⟩
    obtain ⟨r,hr,he⟩ := z.property
    apply Subtype.ext
    change (z : X ⧸ Q.D)^3=1
    rw [←he]
    exact congrArg Subtype.val (hcube r hr)
  have hnorm : H ≤ normalizer (Z : Set (X ⧸ Q.D)) := by
    let := split.abelian
    apply (show H ≤ centralizer (Z : Set (X ⧸ Q.D)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx z hz
    exact congrArg Subtype.val (mul_comm (⟨z,hZH hz⟩ : H) (⟨x,hx⟩ : H))
  exact le_pCoreIn_of_normalizes hZ hZH hnorm

/-- A crossed root commutator survives in the scalar centralizer and is
moved by the same unitary reflection. -/
theorem unitary_scalar_derived_crossed_witness
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hZ : rankOneScalar Q split j ≤ cartanThreeCore Q)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    ∃ a : rootAt Q split j (Q.simple i), a ≠ 1 ∧
      (a : X ⧸ Q.D) ∈ (unitaryScalarDerivedSection Q split j hKj).numerator := by
  let A := rootAt Q split j (Q.simple i)
  have hn : ⁅A,A⁆ ≠ ⊥ := by
    intro he
    have hh : rightConjugate ⁅simpleRoot Q split j,simpleRoot Q split j⁆
        (representative (Q.simple i) : X ⧸ Q.D) = ⊥ := by
      simpa only [A,rootAt,rightConjugate,comap_equiv_eq_map_symm',map_commutator] using he
    apply hne
    rw [rightConjugate,comap_equiv_eq_map_symm'] at hh
    exact (map_eq_bot_iff_of_injective _
      (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).symm.injective).mp hh
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hn
  have hAV : A ≤ simpleRemainder Q split j :=
    (show A ≤ middleFive Q split j i from
      le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))).trans
      (middleFive_le_remainder Q split hm j i hij.symm)
  have haA : (a : X ⧸ Q.D) ∈ A := commutator_le_self _ a.property
  have haC : (a : X ⧸ Q.D) ∈ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) := by
    have hp : ⁅A,A⁆ ≤ rootFrattiniAt Q split j (Q.simple i) := by
      have : Fact (IsPGroup 2 A) := ⟨(split.isTwo.to_le (simpleRoot_le Q split j)).of_equiv
        (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))).symm⟩
      rw [rootFrattiniAt,←map_subtype_commutator]
      exact map_mono (commutator_le_frattini_of_isPGroup (p:=2))
    exact centralizer_le hZ ((hfix _).symm ▸ hp a.property).2
  exact ⟨⟨a,haA⟩,(fun he => ha (Subtype.ext (congrArg (fun x : rootAt Q split j (Q.simple i) => (x : X ⧸ Q.D)) he))),
    commutator_mono hAV hAV a.property,haC⟩

/-- The unitary reflection moves the actual scalar-fixed derived section. -/
theorem unitary_scalar_derived_action_ne_one
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hZ : rankOneScalar Q split j ≤ cartanThreeCore Q)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    (unitaryScalarDerivedSection Q split j hKj).action ≠ 1 := by
  obtain ⟨a,ha,hax⟩ := unitary_scalar_derived_crossed_witness Q split hm i j hij hKj hZ hfix hne
  exact cross_root_moves_section Q split hm i j hij (UnitarySource.actorReflection Q split j)
    (unitaryScalarDerivedSection Q split j hKj) rfl a a.property hax
    (fun he => ha (Subtype.ext he))

/-- Centralizing the actual scalar subgroup kills exactly that subgroup
in the conjugation action, once source effectiveness is proved. -/
theorem unitary_scalar_derived_effective_kernel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hmove : (unitaryScalarDerivedSection Q split j hKj).action ≠ 1) :
    (unitaryScalarDerivedSection Q split j hKj).effectiveAction.ker =
      (RootLocalCover.projection Q split j).ker := by
  let d := unitaryScalarDerivedSection Q split j hKj
  apply le_antisymm
  · rw [RootLocalCover.projection_ker]
    exact unitary_section_effective Q split j J hb hcard hconj σ hσ hKj μ d hmove
  · intro r hr
    have hz := RootLocalCover.projection_ker_central Q split j hr
    have hnum : d.numeratorAction r=1 := scalar_section_kernel Q split j d inf_le_right hz
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H z => rw [d.effectiveAction_mk,hnum]; rfl



private theorem small_scalar_section_kernel_and_bound
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (d : RootSection Q split j)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    [Group.IsSolvable (rootPanelImage Q split j)]
    (hp : Nat.card (Panel Q j)=9) (hc : Nat.card (rootPanelImage Q split j)=72)
    (hfree : ∀ g : MulAction.stabilizer (rootPanelImage Q split j) (panelBase Q j),
      ∀ x : Panel Q j, x ≠ panelBase Q j → (g : rootPanelImage Q split j) • x=x → g=1)
    (hn : ¬ IsPGroup 2 d.action.range) :
    d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker ∧
      256 ≤ Nat.card d.EffectiveCarrier := by
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hk : f.ker ≤ d.numeratorAction.ker :=
    (center_eq_panel_kernel Q split j hKj) ▸ scalar_section_kernel Q split j d hd
  have hka : f.ker ≤ d.action.ker := by
    intro r hr
    ext z
    induction z using QuotientGroup.induction_on with
    | H z => rw [d.action_mk,show d.numeratorAction r=1 from hk hr]; rfl
  have hke : f.ker ≤ d.effectiveAction.ker := by
    intro r hr
    ext z
    induction z using QuotientGroup.induction_on with
    | H z => rw [d.effectiveAction_mk,show d.numeratorAction r=1 from hk hr]; rfl
  let β : rootPanelImage Q split j →* MulAut d.Carrier := f.liftOfSurjective hf ⟨d.action,hka⟩
  have hb (r) : β (f r)=d.action r := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hbr : β.range=d.action.range := by
    have he : β.comp f=d.action := MonoidHom.ext hb
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
  have hβ : Function.Injective β := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hc (panelBase Q j) β (hbr ▸ hn)
  let γ : rootPanelImage Q split j →* MulAut d.EffectiveCarrier :=
    f.liftOfSurjective hf ⟨d.effectiveAction,hke⟩
  have hg (r) : γ (f r)=d.effectiveAction r := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have htwo : IsPGroup 2 γ.ker := by
    apply ((d.effectiveKernel_action_isTwo).comap_of_injective β hβ).to_le
    intro z hz
    obtain ⟨r,rfl⟩ := hf z
    exact ⟨r,show d.effectiveAction r=1 from (hg r).symm.trans hz,(hb r).symm⟩
  have hγ : Function.Injective γ := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) γ htwo
  have heq : d.effectiveAction.ker=f.ker := by
    apply le_antisymm ?_ hke
    intro r hr
    exact hγ ((hg r).trans (hr.trans γ.map_one.symm))
  refine ⟨?_,?_⟩
  · rw [heq]
    change ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker = _
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker,RootLocalCover.projection_ker]
  · let ρ := Representation.FrattiniAction.ofAutomorphismHom γ
    have hρ : Function.Injective ρ := by
      intro r t he
      apply hγ
      ext x
      exact Additive.ofMul.injective (congrArg
        (fun a : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => a (Additive.ofMul x)) he)
    have hdim := BinaryPanel.frobenius_nine_degree
      (rootPanelImage_two_pretransitive Q split j) hp hc (panelBase Q j) hfree ρ hρ
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
    have he := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier)
    simp only [Nat.card_zmod] at he
    rw [←he] at hh
    exact hh

/-- At unitary degree one the scalar-fixed section has a faithful projective
Frattini action and degree at least eight, for either full scalar convention. -/
theorem small_unitary_scalar_derived_kernel_and_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hroot : Nat.card (simpleRoot Q split j)=8)
    (hfull : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hZ : rankOneScalar Q split j ≤ cartanThreeCore Q)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    (unitaryScalarDerivedSection Q split j hKj).effectiveAction.ker =
      (RootLocalCover.projection Q split j).ker ∧
      256 ≤ Nat.card (unitaryScalarDerivedSection Q split j hKj).EffectiveCarrier := by
  let d := unitaryScalarDerivedSection Q split j hKj
  obtain ⟨a,ha,hax⟩ := unitary_scalar_derived_crossed_witness Q split hm i j hij hKj hZ hfix hne
  have hp : Nat.card (Panel Q j)=9 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j)=1+Nat.card (simpleRoot Q split j) at he
    omega
  rcases hfull with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
  · obtain ⟨hT,hcenter⟩ := small_special_cartan Q split j J hcard hconj hKj ν hroot
    have hR : Nat.card (rankOne Q split j)=216 := (Nat.card_congr ν.toEquiv).trans
      (HermitianForm.SmallThreeCore.special_group_card J hcard hconj)
    obtain ⟨hsol,hc,hfree⟩ := central_nine_panel_structure Q split j hKj hR hcenter hroot
    let := hsol
    exact small_scalar_section_kernel_and_bound Q split j hKj d inf_le_right hp hc hfree
      (small_special_section_not_two Q split j hT.le hcenter hroot hm i hij
        (UnitarySource.actorReflection Q split j) d rfl a ha hax)
  · let := HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
    let : Group.IsSolvable (rankOne Q split j) :=
      Group.isSolvable_of_surjective (f:=ν.symm.toMonoidHom) ν.symm.surjective
    have hR : Nat.card (rankOne Q split j)=72 := (Nat.card_congr ν.toEquiv).trans
      (HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
    obtain ⟨hsol,hc,hfree⟩ := nine_actor_structure Q split j hR hroot
    let := hsol
    exact small_scalar_section_kernel_and_bound Q split j hKj d inf_le_right hp hc hfree
      (nine_section_action_not_two Q split j hR hroot hm i hij
        (UnitarySource.actorReflection Q split j) d rfl a ha hax)



/-- The literal scalar-fixed derived section affords a faithful projective
binary action, with the special-to-projective square retained. At degree one
its binary degree is at least eight; the general degree bound here is six b. -/
theorem unitary_scalar_derived_projective
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hsquare : ∀ a, μ (RootLocalCover.projection Q split j (σ a))=J.specialToProjective a)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w) :
    let d := unitaryScalarDerivedSection Q split j hKj
    rankOneScalar Q split j ≤ cartanThreeCore Q ∧ d.action ≠ 1 ∧
      d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker ∧
      ∃ ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J)
          (Additive d.EffectiveCarrier),
        Function.Injective ρ ∧
        (∀ r, ρ (μ (RootLocalCover.projection Q split j r))=d.effectiveRepresentation r) ∧
        2^(6*b) ≤ Nat.card d.EffectiveCarrier ∧ (b=1 → 256 ≤ Nat.card d.EffectiveCarrier) := by
  let d := unitaryScalarDerivedSection Q split j hKj
  have hZ := unitary_scalar_le_threeCore Q split J j hKj μ σ hσ hsquare
  have hne := unitary_root_commutator_ne_bot Q split J hb hcard hconj j hKj μ
  have hmoving := unitary_scalar_derived_action_ne_one Q split hm i j hij hKj hZ hfix hne
  have hsmall' (he : b=1) : d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker ∧
      256 ≤ Nat.card d.EffectiveCarrier := by
    exact small_unitary_scalar_derived_kernel_and_bound Q split J
      (by simpa only [he,pow_one,Nat.reducePow] using hcard) (by simpa only [he,pow_one] using hconj)
      hm i j hij hKj (by simpa only [he,pow_one,Nat.reducePow] using hroot) (hsmall he) hZ hfix hne
  have hk : d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker := by
    by_cases he : b=1
    · exact (hsmall' he).1
    · exact unitary_scalar_derived_effective_kernel Q split J (by omega) hcard hconj
        j hKj μ σ hσ hmoving
  have hlo : 2^(6*b) ≤ Nat.card d.EffectiveCarrier := by
    by_cases he : b=1
    · exact (by norm_num [he] : 2^(6*b) ≤ 256).trans (hsmall' he).2
    · exact unitary_section_card_bound Q split j J (by omega) hcard hconj σ hσ d hmoving
  let π := μ.toMonoidHom.comp (RootLocalCover.projection Q split j)
  have hπ : Function.Surjective π := μ.surjective.comp
    (RootLocalCover.central_odd_cover Q split j hKj).1
  have hkπ : π.ker=d.effectiveAction.ker := by
    rw [hk]
    ext r
    exact μ.map_eq_one_iff
  let γ : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut d.EffectiveCarrier :=
    π.liftOfSurjective hπ ⟨d.effectiveAction,hkπ.le⟩
  have hg (r) : γ (π r)=d.effectiveAction r := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hγ : Function.Injective γ := by
    apply γ.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨r,rfl⟩ := hπ z
    exact (hkπ.symm.le (show d.effectiveAction r=1 from (hg r).symm.trans hz))
  let ρ := Representation.FrattiniAction.ofAutomorphismHom γ
  refine ⟨hZ,hmoving,hk,ρ,?_,?_,hlo,fun he => (hsmall' he).2⟩
  · intro r t he
    apply hγ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => a (Additive.ofMul x)) he)
  · intro r
    ext x
    change Additive.ofMul (γ (π r) x.toMul)=Additive.ofMul (d.effectiveAction r x.toMul)
    rw [hg]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
