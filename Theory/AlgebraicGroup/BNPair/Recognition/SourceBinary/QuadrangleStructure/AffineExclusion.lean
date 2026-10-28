module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryFactorOrders
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineFrattiniExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CubicLocal
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitarySections
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnequalLinearRadicals

/-!
# The quadrangle estimates excluding an exceptional affine panel

A nontrivial square in the opposite root is moved to a disjoint root by
its simple reflection. Thus both the complementary section and its Frattini
subgroup carry nontrivial actions of the same rank-one actor. The binary
minimum-degree bounds exclude nonbinary Suzuki and unitary opposite factors,
and bound an opposite linear field by four.

For the remaining roots of order at most eight, local characteristic two
makes the root actor faithful on the actual panel two-kernel. If its own
panel action is faithful, the order-72 image forces a Frattini quotient of
order at least 256. The crossed affine root meets that kernel in a subgroup
of index at most two, with a nontrivial square, so the kernel has order at
least 512. The quadrangle product and the exact defect two bound it by 256.
The separate affine odd-stem-cover theorem supplies the faithfulness premise.

All subgroups and actions belong to the same marked split quotient. No
regularity is assumed at the affine endpoint, and the full panel kernel is
kept distinct from its two-core. The import-all edge intentionally reuses
the internal quadrangle Frattini and root-order calculations; their public
boundaries remain unchanged. The original marked application exhausts F.1.1.
Source: Fong--Seitz I (4A),(4B),(4D),(4F),(5I), pp.19--24,31--35.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem frattini_action_moves_square (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (a : simpleRoot Q split j) (ha : a^2 ≠ 1) :
    ∃ r, ((MulAut.characteristic (frattini (simpleRemainder Q split i))).comp
      (remainderRankOneAction Q split i hV)) r ≠ 1 := by
  let V := simpleRemainder Q split i
  let φ := (MulAut.characteristic (frattini V)).comp
    (remainderRankOneAction Q split i hV)
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let v : V := ⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 a.property⟩
  let z : frattini V := ⟨v^2,pth_power_mem_frattini_of_isPGroup (p := 2) v⟩
  let s := UnitarySource.actorReflection Q split i
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  refine ⟨r⁻¹,?_⟩
  intro he
  have hz := congrArg (fun f : MulAut (frattini V) => ((f z : V) : X ⧸ Q.D)) he
  change (s.val : X ⧸ Q.D)⁻¹ * (a : X ⧸ Q.D)^2 *
    ((s.val : X ⧸ Q.D)⁻¹)⁻¹ = (a : X ⧸ Q.D)^2 at hz
  rw [inv_inv] at hz
  have hac : (a : X ⧸ Q.D)^2 ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq,←hz,rightConjugate]
    change (s.val : X ⧸ Q.D) *
      ((s.val : X ⧸ Q.D)⁻¹ * (a : X ⧸ Q.D)^2 * (s.val : X ⧸ Q.D)) *
        (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using
      (simpleRoot Q split j).pow_mem a.property 2
  have hz' := (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le
    ⟨(simpleRoot Q split j).pow_mem a.property 2,
      cross_root_le_own_remainder Q split hm j i hij.symm hac⟩
  exact ha (Subtype.ext hz')

theorem linear_remainder_card_lower_of_opposite_square
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (a : simpleRoot Q split j) (ha : a^2 ≠ 1) :
    Nat.card F ^ 4 ≤ Nat.card (simpleRemainder Q split i) := by
  let V := simpleRemainder Q split i
  have hp : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  let φ := (MulAut.characteristic (frattini V)).comp
    (remainderRankOneAction Q split i hV)
  have hfirst := linear_frattini_card_lower μ hp (remainderRankOneAction Q split i hV)
    (remainder_action_moves_root Q split hm i j hij hV) hn hF
  have hsecond := linear_frattini_card_lower μ
    (hp.of_injective (frattini V).subtype (frattini V).subtype_injective) φ
    (frattini_action_moves_square Q split hm i j hij hV a ha) hn hF
  have hphi : Nat.card F ^ 2 ≤ Nat.card (frattini V) := hsecond.trans
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini (frattini V))))
  calc
    Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
    _ ≤ Nat.card (V ⧸ frattini V) * Nat.card (frattini V) := Nat.mul_le_mul hfirst hphi
    _ = Nat.card V := (Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)).symm

theorem affine_quadrangle_linear_field_le_four
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F))
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Nat.card F ≤ 4 := by
  by_contra! hlarge
  let ξ := (localGroupEquivOfCenterless Q split i hV μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hri := GTwoSource.simpleRoot_card Q split i hV ξ
  have hrj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  obtain ⟨a,ha⟩ := affine_root_subgroup_square Q split j hs hp hg 1
    (simpleRoot Q split j) (by rw [rootAt_one]) (by rw [hrj]; decide)
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n : ℕ) := by
    by_contra! hsmall
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall
    rw [←hF] at hh
    norm_num at hh
    omega
  have hl := linear_remainder_card_lower_of_opposite_square Q split hm i j hij hV μ hn' hF a ha
  rw [remainder_card_four Q split hm i j hij,hri,hrj] at hl
  norm_num only [Nat.reducePow] at hl
  have hl' : Nat.card F ^ 3 ≤ 64 := Nat.le_of_mul_le_mul_left (by
    calc Nat.card F * Nat.card F ^ 3 = Nat.card F ^ 4 := by ring
         _ ≤ Nat.card F * 64 := hl) (Nat.card_pos (α := F))
  have hsq : 25 ≤ Nat.card F ^ 2 := by nlinarith
  have hcube : 125 ≤ Nat.card F ^ 3 := by nlinarith
  omega

private def trueRadicalSection (j : Fin 2) : RootSection Q split j where
  numerator := LocalCover.radical Q split j
  le_radical := unipotent_inf_kernel_le_remainder Q split j
  normalized := (rankOne_le_parabolic Q split j).trans
    (LocalCover.radical_parabolic_normalizes Q split j)
  denominator := ⊥
  invariant _ := map_bot _

private theorem trueRadicalAction_injective (j : Fin 2)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j})) :
    Function.Injective (trueRadicalSection Q split j).numeratorAction := by
  let d := trueRadicalSection Q split j
  let D := Q.tits.standardParabolic {Q.simple j}
  have hcore : D.pCoreIn 2 = d.numerator :=
    (PanelKernel.radical_eq_parabolic_twoCore Q split j).symm
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply _root_.eq_bot_iff.mpr
  intro r hr
  let rD : D := ⟨r,rankOne_le_parabolic Q split j r.property⟩
  have hrD : rD ∈ pCore 2 D := by
    apply hc
    rw [mem_centralizer_iff]
    intro v hv
    have hvV : (v : X ⧸ Q.D) ∈ d.numerator := hcore ▸ mem_map_of_mem D.subtype hv
    have he := congrArg (fun a : MulAut d.numerator => (a ⟨v,hvV⟩ : X ⧸ Q.D)) hr
    rw [d.numeratorAction_apply] at he
    change (r : X ⧸ Q.D) * v * (r : X ⧸ Q.D)⁻¹ = v at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  have hrV : (r : X ⧸ Q.D) ∈ d.numerator := hcore ▸ mem_map_of_mem D.subtype hrD
  exact Subtype.ext ((disjoint_def.mp (RootLocalCover.rankOne_disjoint_radical Q split j))
    r.property hrV)

private theorem affine_trueRadical_frattini_card_lower (j : Fin 2)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (hinj : Function.Injective (rootImageProjection Q split j)) :
    256 ≤ Nat.card (LocalCover.radical Q split j ⧸ frattini (LocalCover.radical Q split j)) := by
  let d := trueRadicalSection Q split j
  let e := MulEquiv.ofBijective (rootImageProjection Q split j)
    ⟨hinj,(panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective⟩
  let α := d.numeratorAction.comp e.symm.toMonoidHom
  have hα : Function.Injective α := (trueRadicalAction_injective Q split j hc).comp e.symm.injective
  let β := (quotientAut (frattini d.numerator)).comp α
  have hβ : Function.Injective β := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) β
    ((isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective α hα)
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let : IsElementaryAbelian 2 (d.numerator ⧸ frattini d.numerator) :=
    isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hβ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive (d.numerator ⧸ frattini d.numerator)) =>
        a (Additive.ofMul x)) he)
  obtain ⟨hsol,hcard,hfree⟩ := affine_root_image_structure Q split j hs hp hg
  let := hsol
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (d.numerator ⧸ frattini d.numerator))
  simp only [Nat.card_zmod] at he
  rw [←he] at hh
  exact hh

private theorem affine_trueRadical_frattini_nontrivial (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    2 ≤ Nat.card (frattini (LocalCover.radical Q split j)) := by
  let A := rootAt Q split j (Q.simple i)
  let V := LocalCover.radical Q split j
  have hAR : A ≤ simpleRemainder Q split j := cross_root_le_own_remainder Q split hm j i hij.symm
  have hcard : Nat.card A = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    change Nat.card (rootAt Q split j _) = 8
    rw [rootAt,card_rightConjugate]
    omega
  have hi : V.relIndex (simpleRemainder Q split j) = 2 := by
    rcases BinaryPanel.remainder_index_cases Q split j hp (Or.inr hg) with hr | hr
    · omega
    · exact hr.2.1
  have hi' := relIndex_le_of_le_right (H := V) hAR (by rw [hi]; decide)
  rw [←inf_relIndex_left A V,hi] at hi'
  have hc := ((A ⊓ V).subgroupOf A).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ V ≤ A from inf_le_left)).toEquiv] at hc
  change (A ⊓ V).relIndex A * Nat.card ↥(A ⊓ V) = Nat.card A at hc
  rw [hcard] at hc
  have hgt : 2 < Nat.card ↥(A ⊓ V) := by nlinarith
  obtain ⟨a,ha⟩ := affine_root_subgroup_square Q split j hs hp hg (Q.simple i)
    (A ⊓ V) inf_le_left hgt
  let x : V := ⟨a,a.property.2⟩
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hx : x^2 ≠ 1 := fun he => ha
    (Subtype.ext (congrArg (fun z : V => (z : X ⧸ Q.D)) he))
  have hn : frattini V ≠ ⊥ := by
    intro hz
    have hh := pth_power_mem_frattini_of_isPGroup (p := 2) x
    rw [hz,mem_bot] at hh
    exact hx hh
  exact (frattini V).one_lt_card_iff_ne_bot.mpr hn

theorem no_affine_quadrangle_of_small_opposite_of_faithful
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (hsmall : Nat.card (simpleRoot Q split i) ≤ 8)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (hinj : Function.Injective (rootImageProjection Q split j)) : False := by
  let V := LocalCover.radical Q split j
  have hfirst := affine_trueRadical_frattini_card_lower Q split j hc hs hp hg hinj
  have hsecond := affine_trueRadical_frattini_nontrivial Q split hm i j hij hs hp hg
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)
  have hlower : 512 ≤ Nat.card V := by
    change 256 ≤ Nat.card (V ⧸ frattini V) at hfirst
    change 2 ≤ Nat.card (frattini V) at hsecond
    nlinarith
  have hi : V.relIndex (simpleRemainder Q split j) = 2 := by
    rcases BinaryPanel.remainder_index_cases Q split j hp (Or.inr hg) with hr | hr
    · omega
    · exact hr.2.1
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) V
    (simpleRemainder Q split j) bot_le (unipotent_inf_kernel_le_remainder Q split j)
  rw [relIndex_bot_left,relIndex_bot_left,hi,remainder_card_four Q split hm j i hij.symm] at hcard
  have hrj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  rw [hrj] at hcard
  have hsq := Nat.pow_le_pow_left hsmall 2
  norm_num only [Nat.reducePow] at hsq
  nlinarith

private theorem section_moves_opposite_root (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (d : RootSection Q split i) (hd : d.denominator = ⊥)
    (x : X ⧸ Q.D) (hx : x ∈ simpleRoot Q split j) (hxd : x ∈ d.numerator)
    (hne : x ≠ 1) : d.action ≠ 1 := by
  intro he
  let s := UnitarySource.actorReflection Q split i
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  let z : d.numerator := ⟨x,hxd⟩
  have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk z))
    (show d.action r⁻¹ = 1 by rw [he]; rfl)
  rw [d.action_mk] at hh
  have hz : d.numeratorAction r⁻¹ z = z := by
    have hv := QuotientGroup.eq.mp hh
    rw [hd,mem_bot,inv_mul_eq_one] at hv
    exact hv
  have hzx := congrArg Subtype.val hz
  rw [d.numeratorAction_apply] at hzx
  change (s.val : X ⧸ Q.D)⁻¹*x*((s.val : X ⧸ Q.D)⁻¹)⁻¹ = x at hzx
  rw [inv_inv] at hzx
  have hac : x ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq,←hzx,rightConjugate]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*x*(s.val : X ⧸ Q.D))*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hx
  exact hne ((disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le
    ⟨hx,cross_root_le_own_remainder Q split hm j i hij.symm hac⟩)

private theorem affine_opposite_two_sections_move (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    (radicalSection Q split i hV).action ≠ 1 ∧
      (frattiniSection Q split i (radicalSection Q split i hV)).action ≠ 1 := by
  let d := radicalSection Q split i hV
  let f := frattiniSection Q split i d
  have hrj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  obtain ⟨a,ha⟩ := affine_root_subgroup_square Q split j hs hp hg 1
    (simpleRoot Q split j) (by rw [rootAt_one]) (by rw [hrj]; decide)
  have hne : (a : X ⧸ Q.D)^2 ≠ 1 := fun he => ha (Subtype.ext he)
  have hx := (simpleRoot Q split j).pow_mem a.property 2
  have hxd : (a : X ⧸ Q.D)^2 ∈ d.numerator :=
    (opposite_roots_le_remainder Q split j i hij.symm).1 hx
  have hxf : (a : X ⧸ Q.D)^2 ∈ f.numerator := by
    let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
    let v : d.numerator := ⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 a.property⟩
    exact ⟨v^2,pth_power_mem_frattini_of_isPGroup (p := 2) v,rfl⟩
  exact ⟨section_moves_opposite_root Q split hm i j hij d rfl _ hx hxd hne,
    section_moves_opposite_root Q split hm i j hij f rfl _ hx hxf hne⟩

private theorem two_section_card_bound (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (b : ℕ)
    (hfirst : b ≤ Nat.card (radicalSection Q split i hV).EffectiveCarrier)
    (hsecond : b ≤ Nat.card (frattiniSection Q split i
      (radicalSection Q split i hV)).EffectiveCarrier) :
    b^2 ≤ Nat.card (simpleRemainder Q split i) := by
  let d := radicalSection Q split i hV
  let f := frattiniSection Q split i d
  have hden : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  have hfirst' : b ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    change b ≤ Nat.card (d.numerator ⧸ d.effectiveDenominator) at hfirst
    rwa [hden] at hfirst
  have hsz : Nat.card f.EffectiveCarrier ≤ Nat.card (frattini d.numerator) := by
    calc
      Nat.card f.EffectiveCarrier ≤ Nat.card f.numerator :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ = Nat.card (frattini d.numerator) :=
        Nat.card_congr ((frattini d.numerator).equivMapOfInjective
          d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  calc
    b^2 = b*b := pow_two b
    _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator) * Nat.card (frattini d.numerator) :=
      Nat.mul_le_mul hfirst' (hsecond.trans hsz)
    _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card

theorem no_affine_quadrangle_of_suzuki
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hmpos : 0 < m)
    (μ : rankOne Q split i ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hroot : Nat.card (simpleRoot Q split i) = (2^(2*m+1))^2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  obtain ⟨hmove,hphimove⟩ := affine_opposite_two_sections_move Q split hm i j hij hV hs hp hg
  have hfirst := suzuki_section_card_bound Q split i hmpos μ _ hmove
  have hsecond := suzuki_section_card_bound Q split i hmpos μ _ hphimove
  have hlow := two_section_card_bound Q split i hV _ hfirst hsecond
  have hrj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  rw [remainder_card_four Q split hm i j hij,hroot,hrj] at hlow
  have hpow : 2^(8*(2*m+1)) ≤ 2^(2*(2*m+1)+6) := by
    calc
      2^(8*(2*m+1)) = (2^(4*(2*m+1)))^2 := by rw [←pow_mul]; congr 1; omega
      _ ≤ (2^(2*m+1))^2 * 8^2 := hlow
      _ = 2^(2*(2*m+1)+6) := by
        rw [←pow_mul,show (8:ℕ)^2 = 2^6 from rfl,←pow_add]
        congr 1; omega
  have hb := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  omega

theorem no_affine_quadrangle_of_unitary
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (π : J.specialSubgroup →* rankOne Q split i) (hπ : Function.Surjective π)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  obtain ⟨hmove,hphimove⟩ := affine_opposite_two_sections_move Q split hm i j hij hV hs hp hg
  have hfirst := unitary_section_card_bound Q split i J hn hE hconj π hπ _ hmove
  have hsecond := unitary_section_card_bound Q split i J hn hE hconj π hπ _ hphimove
  have hlow := two_section_card_bound Q split i hV _ hfirst hsecond
  have hrj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  rw [remainder_card_four Q split hm i j hij,hroot,hrj] at hlow
  have hpow : 2^(12*n) ≤ 2^(3*n+6) := by
    calc
      2^(12*n) = (2^(6*n))^2 := by rw [←pow_mul]; congr 1; omega
      _ ≤ (2^n)^3 * 8^2 := hlow
      _ = 2^(3*n+6) := by
        rw [←pow_mul,show (8:ℕ)^2 = 2^6 from rfl,←pow_add]
        congr 1; omega
  have hb := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
