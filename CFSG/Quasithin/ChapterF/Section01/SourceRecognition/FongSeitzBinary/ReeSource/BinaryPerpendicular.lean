module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularFrattini

/-!
# Binary perpendicular-root commutation on the source octagon

Normality of the quintic subgroup of Sz(2) makes its fixed space invariant
under the whole actor. The perpendicular image in V/Φ(V) is already fixed,
so every perpendicular commutator has fixed image. Its proved product
support has only the first linear coordinate outside Φ(V). The actual
reflection sends that coordinate to the simple linear root; the literal
linear panel kernel contains Φ(V) and the first root, and meets the simple
root trivially. The fixed coordinate must therefore vanish.

Consequently the whole binary actor preserves Φ(V)E. Reflection removes
both linear factors from the perpendicular commutator, and the square
identity proves Omega centralization. The genuine quintic centralizer then
forces perpendicular normalization and commutation, including Sz(2).
The final exports combine this with the positive-parameter proof.

Source: Fong--Seitz I (1973), (6H)(d), printed p.54. This proof uses the
narrow Omega support, not the false whole-root centrality assertion on p.53.
Natural panel markings, odd linear degree and faithful Borel remain explicit.
PositiveSixFourEquality, OriginalPositivePerpendicular and Section10Perpendicular
consume the all-parameter result on the same quotient and literal endpoint maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem sinv (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) = rootAt Q split k w := rfl

set_option linter.unusedSimpArgs false in
private theorem root_remainder (hm : rotationOrder Q = 8) (k : Fin 5) :
    rootAt Q split ((![0,0,1,1,1] : Fin 5 → Fin 2) k)
      ((![Q.simple 1*Q.simple 0,Q.simple 1*Q.simple 0*Q.simple 1,Q.simple 0,
        Q.simple 0*Q.simple 1,Q.simple 0*Q.simple 1*Q.simple 0] : Fin 5 → Weyl Q) k) ≤
        simpleRemainder Q split 1 := by
  have hL (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have h0 := hL false
  have h1 := hL true
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    mul_one,←mul_assoc] at h0 h1
  fin_cases k <;> dsimp <;> apply rootAt_le_remainder Q split _ 1 _ <;>
    simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple 0) (Q.simple 0),
      ←mul_assoc (Q.simple 1) (Q.simple 1),ssq,one_mul,mul_one,←mul_assoc,
      Q.tits.wordLength_one,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,
      h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2]

include ν hC μ hB hn in
private theorem internal_linear_le_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    rootAt Q split 0 (Q.simple 1*Q.simple 0) ≤
        (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ∧
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ≤
        (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  let V := simpleRemainder Q split 1
  let F := (frattini V).map V.subtype
  have hphi : ⁅V,V⁆ ≤ F := by
    let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hnear := source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc
  constructor
  · have he := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) hnear
    rw [right_comm,right_simple,right_rep,right_rep] at he
    rw [←he]
    exact (commutator_mono (root_remainder Q split hm 2) (root_remainder Q split hm 4)).trans hphi
  · have he := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)) hnear
    rw [right_comm,right_simple,right_rep,right_rep] at he
    have hE : rootAt Q split 1 ((Q.simple 0*Q.simple 1)*(Q.simple 0*Q.simple 1)) =
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
      rw [←mul_assoc,←right_rep]
      exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    rw [hE] at he
    have he' : ⁅rootAt Q split 1 (Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ =
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) := by simpa only [mul_assoc] using he
    rw [←he']
    exact (commutator_mono (root_remainder Q split hm 3) (root_remainder Q split hm 4)).trans hphi

include ν hC in
private theorem linear_square (w : Weyl Q) (x : X ⧸ Q.D)
    (hx : x ∈ rootAt Q split 0 w) : x^2 = 1 := by
  let e : rootAt Q split 0 w ≃* Multiplicative (BinaryGaloisField n) :=
    (RootAction.conjugateEquiv (simpleRoot Q split 0) (representative w)).trans
      (linearRootEquiv Q split 0 ν T hC)
  have hs : (⟨x,hx⟩ : rootAt Q split 0 w)^2 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (e ⟨x,hx⟩).toAdd = 0
    rw [two_nsmul,CharTwo.add_self_eq_zero]
  exact congrArg Subtype.val hs

include ν hC in
private theorem unipotent_frattini_le_linear_kernel :
    (frattini split.U).map split.U.subtype ≤ embeddedPanelKernel Q 0 := by
  let f : split.U →* (Endpoint Q 0 ⧸ panelKernel Q 0) :=
    (QuotientGroup.mk' (panelKernel Q 0)).comp
      (inclusion (split.U_le.trans (Q.tits.B_le_standardParabolic _)))
  have hsq (u : split.U) : f u ^ 2 = 1 := by
    have hp : (u : X ⧸ Q.D) ∈
        (simpleRoot Q split 0 : Set (X ⧸ Q.D)) * (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]; exact u.property
    obtain ⟨a,ha,b,hb,hab⟩ := hp
    have hk := remainder_le_panelKernel_of_marking Q split 0 ν T hC
      (linear_normalizer_index T) hb
    have hbP : b ∈ Endpoint Q 0 := Q.tits.B_le_standardParabolic _ (split.U_le hb.1)
    have hbK : (⟨b,hbP⟩ : Endpoint Q 0) ∈ panelKernel Q 0 := by
      obtain ⟨v,hv,he⟩ := hk
      exact (Subtype.ext he : v = ⟨b,hbP⟩) ▸ hv
    have hf : f u = rootProjection Q split 0 ⟨a,ha⟩ := by
      have hu : (⟨u,split.U_le.trans (Q.tits.B_le_standardParabolic _) u.property⟩ : Endpoint Q 0) =
          rootInEndpoint Q split 0 ⟨a,ha⟩ * ⟨b,hbP⟩ := Subtype.ext hab.symm
      change QuotientGroup.mk' (panelKernel Q 0)
        (⟨u,split.U_le.trans (Q.tits.B_le_standardParabolic _) u.property⟩ : Endpoint Q 0) = _
      have hbq : QuotientGroup.mk' (panelKernel Q 0) ⟨b,hbP⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hbK
      rw [hu,map_mul,hbq,mul_one]
      rfl
    rw [hf,←map_pow,show (⟨a,ha⟩ : simpleRoot Q split 0)^2 = 1 from Subtype.ext (linear_square Q split n ν T hC 1 a (by rw [rootAt_one]; exact ha)),map_one]
  rintro x ⟨u,hu,rfl⟩
  have hk := Theory.GroupTheory.frattini_le_ker_of_square_image f hsq hu
  exact mem_map_of_mem (Endpoint Q 0).subtype ((QuotientGroup.eq_one_iff _).mp hk)


private instance fiveFour_decEq : DecidableEq FiveFour.Group := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) SemidirectProduct.ext_iff.symm

private theorem fiveFour_fifth_conjugate :
    ∀ c r : FiveFour.Group, c^5 = 1 → c ≠ 1 →
      ∃ k : Fin 5, r*c*r⁻¹ = c^k.val := by decide +kernel

private theorem quintic_fixed_preserved {R W : Type*} [Group R] [Group W]
    (e : R ≃* FiveFour.Group) (c : R) (hc : orderOf c = 5)
    (f : R →* MulAut W) (r : R) (x : W) (hx : f c x = x) :
    f c (f r x) = f r x := by
  have hc5 : c^5 = 1 := by rw [←hc,pow_orderOf_eq_one]
  obtain ⟨k,hk⟩ := fiveFour_fifth_conjugate (e c) (e r⁻¹)
    (by rw [←map_pow,hc5,map_one])
    (e.map_ne_one_iff.mpr (by intro he; rw [he,orderOf_one] at hc; omega))
  have hk' : r⁻¹*c*r = c^k.val := e.injective (by simpa only [map_mul,map_inv,map_pow,inv_inv] using hk)
  have he : c*r = r*c^k.val := by rw [←hk']; group
  have hpow (l : ℕ) : ((f c)^l) x = x := by
    induction l with
    | zero => rfl
    | succ l ih => rw [pow_succ',MulAut.mul_apply,ih,hx]
  change (f c*f r) x = f r x
  rw [←map_mul,he,map_mul,MulAut.mul_apply,map_pow,hpow]

set_option linter.unusedSimpArgs false in
private theorem first_linear_le_remainder (hm : rotationOrder Q = 8) :
    rootAt Q split 0 (Q.simple 1) ≤ simpleRemainder Q split 1 := by
  have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
  have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
  have h01 := wordLength_alternatingWord Q false (n := 2) (by omega)
  have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
  have h010 := wordLength_alternatingWord Q false (n := 3) (by omega)
  have h101 := wordLength_alternatingWord Q true (n := 3) (by omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    mul_one,←mul_assoc] at h0 h1 h01 h10 h010 h101
  apply rootAt_le_remainder Q split 0 1 (Q.simple 1) <;>
    simp only [mul_inv_rev,sinv,mul_assoc,ssq,one_mul,mul_one,Q.tits.wordLength_one,h0,h1,h01,h10,←mul_assoc,h010,h101]

set_option linter.unusedSimpArgs false in
private theorem first_linear_le_own_remainder (hm : rotationOrder Q = 8) :
    rootAt Q split 0 (Q.simple 1) ≤ simpleRemainder Q split 0 := by
  have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
  have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
  have h01 := wordLength_alternatingWord Q false (n := 2) (by omega)
  have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
  have h010 := wordLength_alternatingWord Q false (n := 3) (by omega)
  have h101 := wordLength_alternatingWord Q true (n := 3) (by omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    mul_one,←mul_assoc] at h0 h1 h01 h10 h010 h101
  apply rootAt_le_remainder Q split 0 0 (Q.simple 1) <;>
    simp only [mul_inv_rev,sinv,mul_assoc,ssq,one_mul,mul_one,Q.tits.wordLength_one,h0,h1,h01,h10,←mul_assoc,h010,h101]

omit m μ hB in
include ν hC in
private theorem first_linear_fixed_eq_one
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (hm : rotationOrder Q = 8)
    (v : simpleRemainder Q split 1)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split 0 (Q.simple 1))
    (hfix : quotientAut (frattini (simpleRemainder Q split 1))
      ((radicalSection Q split 1 (marked_suzuki_remainder_le_kernel Q split 1 0 μ hB)).numeratorAction
        (frattiniMover Q split 1 0 μ hB)) (QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v) =
        QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v) :
    v = 1 := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
  let d := radicalSection Q split 1 hV
  let V := simpleRemainder Q split 1
  let F := (frattini V).map V.subtype
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  let c := frattiniMover Q split 1 0 μ hB
  let u := suzukiParameter Q split 1 0 μ hB 0 1
  let y : V := d.numeratorAction c v
  have hA := adjacent_commutator_eq_bot Q split hm 1 0 (by decide) hV
    (marked_linear_remainder_le_kernel Q split 0 ν T hC)
  have hu : Commute (u : X ⧸ Q.D) v :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hA u.property) v hv).symm
  have hy : (y : X ⧸ Q.D) = (s.val : X ⧸ Q.D)*v*(s.val : X ⧸ Q.D)⁻¹ := by
    change ((s.val : X ⧸ Q.D)*u)*v*((s.val : X ⧸ Q.D)*u)⁻¹ = _
    calc
      _ = (s.val : X ⧸ Q.D)*((u : X ⧸ Q.D)*v*(u : X ⧸ Q.D)⁻¹)*(s.val : X ⧸ Q.D)⁻¹ := by group
      _ = _ := by rw [hu.eq,mul_inv_cancel_right]
  have hyA : (y : X ⧸ Q.D) ∈ simpleRoot Q split 0 := by
    rw [hy]
    rw [rootAt_eq Q split 0 _ s.val s.class_eq] at hv
    exact hv
  rw [quotientAut_apply_mk] at hfix
  have hdiff : y/v ∈ frattini V := QuotientGroup.eq_iff_div_mem.mp hfix
  have hFkernel : F ≤ embeddedPanelKernel Q 0 :=
    (frattini_image_le_of_le (show V ≤ split.U from inf_le_left) split.isTwo).trans
      (unipotent_frattini_le_linear_kernel Q split n ν T hC)
  have hyv : (y : X ⧸ Q.D)/(v : X ⧸ Q.D) ∈ embeddedPanelKernel Q 0 :=
    hFkernel (mem_map_of_mem V.subtype hdiff)
  have hvK : (v : X ⧸ Q.D) ∈ embeddedPanelKernel Q 0 :=
    remainder_le_panelKernel_of_marking Q split 0 ν T hC (linear_normalizer_index T)
      ((first_linear_le_own_remainder Q split hm) hv)
  have hyK : (y : X ⧸ Q.D) ∈ embeddedPanelKernel Q 0 := by
    simpa only [div_mul_cancel] using (embeddedPanelKernel Q 0).mul_mem hyv hvK
  have hy1 : y = 1 := Subtype.ext (disjoint_def.mp
    (simpleRoot_disjoint_panelKernel Q split 0) hyA hyK)
  have hvF : (v : X ⧸ Q.D) ∈ F := by
    rw [hy1,one_div] at hdiff
    exact mem_map_of_mem V.subtype (by simpa only [inv_inv] using (frattini V).inv_mem hdiff)
  exact Subtype.ext (disjoint_def.mp
    (source_frattini_disjoint_first_linear Q split 1 0 0 μ hB ν T hC) hv hvF)

omit m μ hB in
include ν hC hn in
/-- The binary perpendicular commutator lies in the actual radical Frattini subgroup.
Normality of the quintic subgroup and the literal panel kernel remove its first
linear coordinate, without a torus-separation hypothesis. -/
theorem source_binary_perpendicular_le_frattini
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ ≤
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
  let d := radicalSection Q split 1 hV
  let V := simpleRemainder Q split 1
  let F := (frattini V).map V.subtype
  let q := QuotientGroup.mk' (frattini V)
  let c := frattiniMover Q split 1 0 μ hB
  let f := (quotientAut (frattini V)).comp d.numeratorAction
  have hcomm := (source_six_three Q split 1 0 0 μ hB ν T hC hm (by decide)).2
  have ho := binary_frattiniMover_order Q split 1 hV μ hB hm 0 (by decide) hcomm
  have hlin := internal_linear_le_frattini Q split n hn 0 ν T hC μ hB hm hcore hc
  have hΩF := source_omega_le_frattini Q split 1 0 μ hB _ (root_remainder Q split hm 3)
  have hq (v : V) (hv : (v : X ⧸ Q.D) ∈ F) : q v = 1 := by
    obtain ⟨t,ht,he⟩ := hv
    have he' : t = v := Subtype.ext he
    exact (QuotientGroup.eq_one_iff v).mpr (he' ▸ ht)
  apply commutator_le.mpr
  intro a ha y hy
  let r : rankOne Q split 1 := ⟨a,(show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) ha⟩
  let v : V := ⟨y,root_remainder Q split hm 4 hy⟩
  let av : V := d.numeratorAction r v
  let z : V := av*v⁻¹
  have hz : (z : X ⧸ Q.D) = ⁅a,y⁆ := rfl
  have hvfix : f c (q v) = q v :=
    source_binary_perpendicular_frattini_fixed Q split n hn ν T hC μ hB hm hcore hc v hy
  have havfix : f c (f r (q v)) = f r (q v) :=
    quintic_fixed_preserved ((suzukiActorEquiv Q split 1 0 μ hB).trans FiveFour.suzukiZeroEquiv.symm)
      c ho f r (q v) hvfix
  have hzfix : f c (q z) = q z := by
    have he : q z = f r (q v)*(q v)⁻¹ := by
      rw [show q z = q (d.numeratorAction r v)*q (v⁻¹) from map_mul q _ _,map_inv]
      exact congrArg (fun x => x*(q v)⁻¹) (quotientAut_apply_mk (frattini V) (d.numeratorAction r) v).symm
    rw [he,map_mul,map_inv,havfix,hvfix]
  have hzm := commutator_mem_commutator ha hy
  obtain ⟨bc,⟨b,hb,t,ht,rfl⟩,u,hu,hprod⟩ :=
    source_perpendicular_product_support Q split n hn 0 ν T hC μ hB hm hcore hc _ hzm
  let vb : V := ⟨b,first_linear_le_remainder Q split hm hb⟩
  let vt : V := ⟨t,root_remainder Q split hm 3 (omegaOneAmbient_le _ ht)⟩
  let vu : V := ⟨u,root_remainder Q split hm 1 hu⟩
  have he : z = vb*vt*vu := Subtype.ext (hz.trans hprod.symm)
  have hzb : q z = q vb := by
    rw [he,map_mul,map_mul,hq vt (hΩF ht),hq vu (hlin.2 hu),mul_one,mul_one]
  have hbfix : f c (q vb) = q vb := by rw [←hzb]; exact hzfix
  have hb1 : vb = 1 := first_linear_fixed_eq_one Q split n ν T hC μ hB hm vb hb hbfix
  have hz1 : q z = 1 := by rw [hzb,hb1,map_one]
  have hzF : (z : X ⧸ Q.D) ∈ F := mem_map_of_mem V.subtype ((QuotientGroup.eq_one_iff z).mp hz1)
  rwa [hz] at hzF

omit m μ hB in
include ν hC hn in
/-- The whole binary actor preserves the perpendicular root image in V/Φ(V). -/
theorem source_binary_actor_normalizes_perpendicular_frattini
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    rankOne Q split 1 ≤ normalizer
      (((frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ⊔
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  let F := (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let K := F ⊔ E
  have hPF := source_frattini_parabolic_normalizes Q split 1 0 μ hB
  have hAF : simpleRoot Q split 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    (simpleRoot_le Q split 1).trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hPF))
  have hAK : simpleRoot Q split 1 ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal K F E (simpleRoot Q split 1) K
      le_normalizer le_sup_left le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp hAF).trans le_sup_left
    · rw [commutator_comm]
      exact (source_binary_perpendicular_le_frattini Q split n hn ν T hC μ hB hm hcore hc).trans le_sup_left
  let s := UnitarySource.actorReflection Q split 1
  have hs : (s.val : X ⧸ Q.D) ∈ normalizer (K : Set (X ⧸ Q.D)) :=
    normalizer_inf_normalizer_le_normalizer_sup F E
      ⟨hPF ((rankOne_le_parabolic Q split 1) s.mem_rankOne),
        perpendicular_root_normalizes Q split hm 1 0 (by decide) s.val s.class_eq⟩
  rw [rankOne]
  apply sup_le hAK
  intro a ha
  have hn := hs
  have ht : (s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split 1 := by
    rw [rootAt_eq Q split 1 _ s.val s.class_eq] at ha
    exact ha
  have hh := (normalizer (K : Set (X ⧸ Q.D))).mul_mem
    ((normalizer (K : Set (X ⧸ Q.D))).mul_mem
      ((normalizer (K : Set (X ⧸ Q.D))).inv_mem hn) (hAK ht)) hn
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _

include μ hB in
private theorem omega_square_one (w : Weyl Q) (x : X ⧸ Q.D)
    (hx : x ∈ omegaOneAmbient (rootAt Q split 1 w)) : x^2 = 1 := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hΩ : (omegaOneAmbient (simpleRoot Q split 1)).map e.toMonoidHom =
      omegaOneAmbient (rootAt Q split 1 w) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  rw [←hΩ] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  rw [←suzukiOmegaParameter_range Q split 1 m μ hB] at ha
  obtain ⟨b,rfl⟩ := ha
  have hb : b^2 = 1 := by
    apply Multiplicative.toAdd.injective
    change 2 • b.toAdd = 0
    rw [two_nsmul,CharTwo.add_self_eq_zero]
  rw [←map_pow,←map_pow,hb,map_one,map_one]

include ν hC μ hB hn in
/-- The perpendicular commutator is contained in Φ(V) for every parameter. -/
theorem source_perpendicular_le_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ ≤
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  cases m with
  | zero => exact source_binary_perpendicular_le_frattini Q split n hn ν T hC μ hB hm hcore hc
  | succ m => exact source_positive_perpendicular_le_frattini Q split n hn (m+1) ν T hC μ hB hm hcore (by omega) hc

include ν hC μ hB hn in
/-- Reflection and the first-linear-root intersection remove both linear
factors from the perpendicular commutator for every parameter. -/
theorem source_perpendicular_le_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ ≤
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  let A := simpleRoot Q split 1
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let F := (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype
  let w := Q.simple 0*Q.simple 1*Q.simple 0
  let g := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have hmap (K : Subgroup (X ⧸ Q.D)) : K.map g.toMonoidHom =
      rightConjugate K (representative w : X ⧸ Q.D) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hAE : A.map g.toMonoidHom = E := by rw [hmap]; rfl
  have hEA : E.map g.toMonoidHom = A := by
    rw [hmap,right_rep]
    dsimp only [w,A]
    simp only [mul_assoc,←mul_assoc (Q.simple 0) (Q.simple 0),ssq,
      ←mul_assoc (Q.simple 1) (Q.simple 1),one_mul,rootAt_one]
  have hstable : ⁅A,E⁆.map g.toMonoidHom = ⁅A,E⁆ := by
    rw [map_commutator,hAE,hEA,commutator_comm]
  have hPhi := source_perpendicular_le_frattini Q split n hn m ν T hC μ hB hm hcore hc
  have hdj := source_frattini_disjoint_first_linear Q split 1 0 m μ hB ν T hC
  intro z hz
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,rfl⟩ :=
    source_perpendicular_product_support Q split n hn m ν T hC μ hB hm hcore hc z hz
  have hlin := internal_linear_le_frattini Q split n hn m ν T hC μ hB hm hcore hc
  have hΩF := source_omega_le_frattini Q split 1 m μ hB _ (root_remainder Q split hm 3)
  have hbF : b ∈ F := by
    have hh := F.mul_mem (F.mul_mem (hPhi hz) (F.inv_mem (hlin.2 hd))) (F.inv_mem (hΩF hc'))
    simpa only [mul_inv_cancel_right] using hh
  have hb1 : b = 1 := disjoint_def.mp hdj hb hbF
  subst b
  simp only [one_mul] at hz ⊢
  have hgz : g (c*d) ∈ F := hPhi (hstable ▸ mem_map_of_mem g.toMonoidHom hz)
  have ht := four_interval_reflection Q split hm 1 0 (by decide) (representative w) (representative_spec _)
  have hgc : g c ∈ omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
    have hh := mem_map_of_mem g.toMonoidHom hc'
    rw [hmap,right_omega,ht.2.1] at hh
    exact hh
  have hgd : g d ∈ rootAt Q split 0 (Q.simple 1) := by
    have hh := mem_map_of_mem g.toMonoidHom hd
    rwa [hmap,ht.2.2] at hh
  have hgdF : g d ∈ F := by
    have hh := F.mul_mem (F.inv_mem (hΩF hgc)) hgz
    simpa only [map_mul,inv_mul_cancel_left] using hh
  have hd1 : d = 1 := g.injective ((disjoint_def.mp hdj hgd hgdF).trans (map_one g).symm)
  rw [hd1,mul_one]
  exact hc'

include ν hC μ hB hn in
/-- The Suzuki half of (6H)(d) for every parameter, including Sz(2). The perpendicular roots
commute; no support, movement or nonzero-commutator premise remains. -/
theorem source_perpendicular_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ := by
  have hle := source_perpendicular_le_omega Q split n hn m ν T hC μ hB hm hcore hc
  have hΩ : ⁅omegaOneAmbient (simpleRoot Q split 1),
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := (suzukiOmega_mem_iff_square Q split 1 m μ hB x).mp hx
    have hz := hle (commutator_mem_commutator ha hy)
    have hcomm : Commute a ⁅a,y⁆ :=
      mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (source_shifted_omega_commute Q split 1 0 m μ hB ν T hC hm (by decide)) hz) a ha
    rw [mem_bot,pow_two,commutatorElement_mul_left_eq_conj_mul,hcomm.eq,
      mul_inv_cancel_right,←pow_two,omega_square_one Q split m μ hB _ _ hz]
  have hnA : simpleRoot Q split 1 ≤ normalizer
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) := by
    cases m with
    | zero =>
      have hl : Nat.card (simpleRoot Q split 0) = 2 := by
        rw [Nat.card_congr (linearRootEquiv Q split 0 ν T hC).toEquiv,
          Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 n hn.pos.ne',
          ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
        norm_num
      exact binary_perpendicular_normalizes_of_omega_commutes Q split 1
        (marked_suzuki_remainder_le_kernel Q split 1 0 μ hB) μ hB hc hm 0 (by decide)
        (source_six_three Q split 1 0 0 μ hB ν T hC hm (by decide)).2 hl hΩ
    | succ m =>
      exact le_sup_left.trans (positive_perpendicular_normalizes_of_omega_normalizes Q split 1 (m+1) μ hB
        (by omega) hm 0 (by decide) ((commutator_eq_bot_iff_le_centralizer.mp hΩ).trans
          (Subgroup.centralizer_le_normalizer _)))
  exact perpendicular_commutator_eq_bot_of_normalizes Q split hm 1 0 (by decide)
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) hnA

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
