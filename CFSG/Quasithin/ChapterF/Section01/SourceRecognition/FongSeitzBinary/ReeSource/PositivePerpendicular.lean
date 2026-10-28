module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SeparatedProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.InvariantRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FiveRootIntervals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ShiftedIntersections

/-!
# Positive perpendicular Suzuki roots commute

Reflecting the perpendicular commutator puts it in the actual radical
Frattini subgroup. Separation of its ordered root coordinates and the
shifted-root intersection rule exclude an order-four middle coordinate.
The square commutator identity then bounds the simple Omega action by the
shifted Omega. Omega-and-reflection generation makes the product of the
Frattini subgroup and the perpendicular root invariant. A second coordinate
separation removes the perpendicular component, and reflection removes both
linear support factors. The same square identity and generation finally
force the two perpendicular Suzuki roots to commute.

This proves the positive-parameter Suzuki clause of Fong--Seitz I (6H)(d),
printed p.54. It uses only the narrower Omega support, preserving the
counterexample to the printed whole-root centrality assertion on p.53.
The actual natural panel markings, odd linear degree and faithful Borel
remain explicit. The binary clause, other (6H) relations and source pairing
are separate obligations. OriginalPositivePerpendicular and
Section10Perpendicular apply the result to the original quotient and (10.2).
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
private def supportKind : Fin 3 → Fin 2 := ![0,1,0]
private def supportWord (r : Bool) : Fin 3 → Weyl Q :=
  if r then ![Q.simple 1*Q.simple 0,Q.simple 0*Q.simple 1*Q.simple 0,
    Q.simple 1*Q.simple 0*Q.simple 1]
  else ![Q.simple 1,Q.simple 0*Q.simple 1,Q.simple 1*Q.simple 0*Q.simple 1]

set_option linter.unusedSimpArgs false in
private theorem support_root_le (hm : rotationOrder Q = 8) (r : Bool) (t : Fin 3) :
    rootAt Q split (supportKind t) (supportWord Q r t) ≤ simpleRemainder Q split 1 := by
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
  cases r <;> fin_cases t <;> dsimp [supportKind,supportWord] <;>
    apply rootAt_le_remainder Q split _ 1 _ <;>
    simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple 0) (Q.simple 0),
      ←mul_assoc (Q.simple 1) (Q.simple 1),ssq,one_mul,mul_one,←mul_assoc,
      Q.tits.wordLength_one,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,
      h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2]

set_option linter.unusedSimpArgs false in
private theorem support_reflections_distinct (hm : rotationOrder Q = 8) (r : Bool) :
    Pairwise fun t u : Fin 3 =>
      (supportWord Q r t)⁻¹*Q.simple (supportKind t)*(supportWord Q r t) ≠
        (supportWord Q r u)⁻¹*Q.simple (supportKind u)*(supportWord Q r u) := by
  intro t u htu he
  have hh := congrArg (weylEquiv Q) he
  simp only [map_mul,map_inv,supportWord,supportKind] at hh
  cases r <;> fin_cases t <;> fin_cases u <;> try exact htu rfl
  all_goals
    simp [map_mul,map_inv,weylEquiv_simple_zero,weylEquiv_simple_one] at hh
    rw [hm] at hh
    norm_num [DihedralGroup.sr_mul_sr,DihedralGroup.r_mul_sr,DihedralGroup.sr_mul_r] at hh
    revert hh
    decide

include ν hC μ hB hn in
private theorem middle_coordinate_in_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (r : Bool) (a : rootAt Q split 0 (supportWord Q r 0))
    (b : rootAt Q split 1 (supportWord Q r 1))
    (c : rootAt Q split 0 (supportWord Q r 2))
    (hz : (a : X ⧸ Q.D)*b*c ∈
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype) :
    (b : X ⧸ Q.D) ∈
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  let z (t : Fin 3) : rootAt Q split (supportKind t) (supportWord Q r t) :=
    ⟨(![(a : X ⧸ Q.D),(b : X ⧸ Q.D),(c : X ⧸ Q.D)] : Fin 3 → X ⧸ Q.D) t,by
      fin_cases t
      · exact a.property
      · exact b.property
      · exact c.property⟩
  have hz' := source_ordered_frattini_product_support Q split n hn m ν T hC μ hB
    hm hcore hmpos 1 supportKind (supportWord Q r) (support_root_le Q split hm r)
    (support_reflections_distinct Q hm r) z (by
      simpa [z,List.ofFn_succ,mul_assoc] using hz)
  exact hz' 1

private theorem shifted_le_remainder (hm : rotationOrder Q = 8) :
    rootAt Q split 1 (Q.simple 0) ≤ simpleRemainder Q split 1 := by
  have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
  have h01 := wordLength_alternatingWord Q false (n := 2) (by omega)
  have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
  have h101 := wordLength_alternatingWord Q true (n := 3) (by omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    mul_one,←mul_assoc] at h0 h01 h10 h101
  apply rootAt_le_remainder Q split 1 1 (Q.simple 0) <;>
    simp only [sinv,h0,h01,h10,h101]

include ν hC μ hB hn in
/-- The perpendicular Suzuki commutator has only Omega in its middle
coordinate. This removes the near-zero assumption from this support bound. -/
theorem source_positive_perpendicular_product_support
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (z : X ⧸ Q.D)
    (hz : z ∈ ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆) :
    z ∈ (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  let V := simpleRemainder Q split 1
  let D := (frattini V).map V.subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let s := (representative (Q.simple 0) : X ⧸ Q.D)
  let e := (MulAut.conj s).symm
  have hD : Q.tits.standardParabolic {Q.simple 1} ≤ normalizer (D : Set (X ⧸ Q.D)) :=
    source_frattini_parabolic_normalizes Q split 1 m μ hB
  have hAD : simpleRoot Q split 1 ≤ normalizer (D : Set (X ⧸ Q.D)) :=
    (simpleRoot_le Q split 1).trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hD))
  have hBD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)) :=
    (inf_le_left.trans (Q.tits.B_le_standardParabolic _)).trans hD
  have hphi : ⁅V,V⁆ ≤ D := by
    let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hE : rightConjugate E s = rootAt Q split 1 (Q.simple 0*Q.simple 1) := by
    dsimp only [E,s]
    rw [right_rep]
    simp only [mul_assoc,ssq,mul_one]
  have he_mem (A : Subgroup (X ⧸ Q.D)) {x : X ⧸ Q.D} (hx : x ∈ A) : e x ∈ rightConjugate A s := by
    change (MulAut.conj s) ((MulAut.conj s).symm x) ∈ A
    simpa only [MulEquiv.apply_symm_apply] using hx
  have hzD : e z ∈ D := by
    have hh := he_mem _ hz
    change e z ∈ rightConjugate ⁅simpleRoot Q split 1,E⁆ s at hh
    rw [show rightConjugate ⁅simpleRoot Q split 1,E⁆ s =
      ⁅rootAt Q split 1 (Q.simple 0),rightConjugate E s⁆ from right_comm Q _ _ _,hE] at hh
    exact hphi ((commutator_mono (shifted_le_remainder Q split hm)
      (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.1) hh)
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,rfl⟩ := distance_four_commutator_support Q split hm 1 0
    (by decide) (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) z hz
  have hΩ : c ∈ omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
    by_contra hnot
    have hc2 : c^2 ≠ 1 := by
      intro heq
      exact hnot ((omegaOneAmbient_le_iff _ _).mp le_rfl c hc' heq)
    have he_b : e b ∈ rootAt Q split 0 (Q.simple 1*Q.simple 0) := by
      have hh := he_mem _ hb
      rwa [show rightConjugate (rootAt Q split 0 (Q.simple 1)) s = _ from right_rep Q split _ _ _] at hh
    have he_c : e c ∈ E := by
      have hh := he_mem _ hc'
      rwa [show rightConjugate (rootAt Q split 1 (Q.simple 0*Q.simple 1)) s = E from right_rep Q split _ _ _] at hh
    have he_d : e d ∈ rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) := by
      have hh := he_mem _ hd
      rwa [perpendicular_root_stable Q split hm 0 1 (by decide) _ (representative_spec _)] at hh
    have he_cD : e c ∈ D := middle_coordinate_in_frattini Q split n hn m ν T hC μ hB hm hcore hmpos true
      ⟨e b,he_b⟩ ⟨e c,he_c⟩ ⟨e d,he_d⟩ (by simpa only [map_mul] using hzD)
    have hwhole : E ≤ D := suzuki_rootAt_le_of_invariant_of_square_ne_one Q split 1 m μ hB _ D hBD
      (e c) he_c he_cD (fun heq => hc2 (e.injective (by simpa only [map_pow,map_one] using heq)))
    have hzPhi : b*c*d ∈ D := ((commutator_mono le_rfl hwhole).trans
      (le_normalizer_iff_commutator_le_right.mp hAD)) hz
    have hcD : c ∈ D := middle_coordinate_in_frattini Q split n hn m ν T hC μ hB hm hcore hmpos false
      ⟨b,hb⟩ ⟨c,hc'⟩ ⟨d,hd⟩ hzPhi
    have hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6 := by
      rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore]
      exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide)
    exact hnot ((source_shifted_frattini_intersection Q split 1 0 ν T hC m μ hB hc hm (by decide) hsize).le ⟨hcD,hc'⟩)
  exact ⟨b*c,⟨b,hb,c,hΩ,rfl⟩,d,hd,rfl⟩

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
/-- The simple Omega moves the perpendicular root only into the shifted
Omega. This is the pre-normalization step in the positive (6H)(d) proof. -/
theorem source_positive_omega_perpendicular_le
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ ≤
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  let B := rootAt Q split 0 (Q.simple 1)
  let C := omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1))
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  have hAB := adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
    (marked_linear_remainder_le_kernel Q split 0 ν T hC)
  have hCB : ⁅C,B⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 0 1 (by decide)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB))
    rw [right_comm,right_rep] at hh
    have hh' : ⁅B,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥ := by
      have hz : rightConjugate (⊥ : Subgroup (X ⧸ Q.D))
          (representative (Q.simple 1) : X ⧸ Q.D) = ⊥ := by
        simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
      rw [hz] at hh
      exact hh
    apply eq_bot_iff.mpr
    rw [commutator_comm]
    exact (commutator_mono le_rfl (omegaOneAmbient_le _)).trans hh'.le
  have hCD : ⁅C,D⁆ = ⊥ := eq_bot_iff.mpr ((commutator_mono (omegaOneAmbient_le _) le_rfl).trans
    (source_shifted_pair_commute Q split 1 0 m μ hB ν T hC hm (by decide)).le)
  have hBD : ⁅B,D⁆ ≤ C := by
    have hh := map_mono (f := (MulAut.conj (representative (Q.simple 1) : X ⧸ Q.D)).symm.toMonoidHom)
      (source_six_two Q split 1 0 m μ hB ν T hC hm (by decide))
    have he (A : Subgroup (X ⧸ Q.D)) : A.map
        (MulAut.conj (representative (Q.simple 1) : X ⧸ Q.D)).symm.toMonoidHom =
        rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']
    simp only [he,right_comm,right_rep,right_omega] at hh
    exact hh
  have hAC : ⁅simpleRoot Q split 1,C⁆ = ⊥ :=
    (commutator_comm _ _).trans (source_shifted_omega_commute Q split 1 0 m μ hB ν T hC hm (by decide))
  have hAD : ⁅simpleRoot Q split 1,D⁆ ≤ C :=
    (source_six_four_of_odd_degree Q split hc hm n hn m ν T hC μ hB hcore).1
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (suzukiOmega_mem_iff_square Q split 1 m μ hB x).mp hx
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,hz⟩ := source_positive_perpendicular_product_support
    Q split n hn m ν T hC μ hB hm hcore hmpos hc ⁅a,y⁆ (commutator_mem_commutator ha hy)
  have hac : Commute a c :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAC ha) c hc').symm
  have hab : Commute a b :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb).symm
  have hcb : Commute c b :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCB hc') b hb).symm
  have hcd : Commute c d :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCD hc') d hd).symm
  have hbcN : b*c ∈ normalizer (C : Set (X ⧸ Q.D)) := by
    apply (normalizer (C : Set (X ⧸ Q.D))).mul_mem
    · exact Subgroup.centralizer_le_normalizer _
        (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hCB) hb)
    · exact le_normalizer hc'
  have haz : ⁅a,b*c*d⁆ ∈ C := by
    rw [commutatorElement_mul_right_eq_mul_conj,(hab.mul_right hac).commutator_eq,one_mul]
    exact (mem_normalizer_iff.mp hbcN _).mp (hAD (commutator_mem_commutator ha hd))
  have hsq : (b*c*d)^2 ∈ C := by
    have hp : b*c*d = (b*d)*c := by rw [mul_assoc,hcd.eq,←mul_assoc]
    rw [hp,((hcb.mul_right hcd).symm).mul_pow,omega_square_one Q split m μ hB _ c hc',mul_one]
    have hb2 := linear_square Q split n ν T hC _ b hb
    have hd2 := linear_square Q split n ν T hC _ d hd
    have hbI : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb2)
    have hdI : d⁻¹ = d := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hd2)
    have he : (b*d)^2 = ⁅b,d⁆ := by simp only [pow_two,commutatorElement_def,hbI,hdI,mul_assoc]
    rw [he]
    exact hBD (commutator_mem_commutator hb hd)
  have he : ⁅a^2,y⁆ = ⁅a,⁅a,y⁆⁆ * ⁅a,y⁆^2 := by
    simp only [pow_two,commutatorElement_def]
    group
  rw [he,←hz]
  exact C.mul_mem haz hsq

private def fourKind : Fin 4 → Fin 2 := ![0,1,0,1]
private def fourWord : Fin 4 → Weyl Q :=
  ![Q.simple 1,Q.simple 0*Q.simple 1,Q.simple 1*Q.simple 0*Q.simple 1,
    Q.simple 0*Q.simple 1*Q.simple 0]

private theorem four_root_le (hm : rotationOrder Q = 8) (t : Fin 4) :
    rootAt Q split (fourKind t) (fourWord Q t) ≤ simpleRemainder Q split 1 := by
  fin_cases t
  · exact support_root_le Q split hm false 0
  · exact support_root_le Q split hm false 1
  · exact support_root_le Q split hm false 2
  · exact (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2

set_option linter.unusedSimpArgs false in
private theorem four_reflections_distinct (hm : rotationOrder Q = 8) :
    Pairwise fun t u : Fin 4 => (fourWord Q t)⁻¹*Q.simple (fourKind t)*(fourWord Q t) ≠
      (fourWord Q u)⁻¹*Q.simple (fourKind u)*(fourWord Q u) := by
  intro t u htu he
  have hh := congrArg (weylEquiv Q) he
  simp only [map_mul,map_inv,fourWord,fourKind] at hh
  fin_cases t <;> fin_cases u <;> try exact htu rfl
  all_goals
    simp [map_mul,map_inv,weylEquiv_simple_zero,weylEquiv_simple_one] at hh
    rw [hm] at hh
    norm_num [DihedralGroup.sr_mul_sr,DihedralGroup.r_mul_sr,DihedralGroup.sr_mul_r] at hh
    revert hh
    decide

include ν hC μ hB hn in
private theorem four_coordinates_in_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (a : rootAt Q split 0 (Q.simple 1))
    (b : rootAt Q split 1 (Q.simple 0*Q.simple 1))
    (c : rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1))
    (d : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))
    (hz : (a : X ⧸ Q.D)*b*c*d ∈
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype) :
    (a : X ⧸ Q.D) ∈ (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ∧
    (b : X ⧸ Q.D) ∈ (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ∧
    (c : X ⧸ Q.D) ∈ (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  let z (t : Fin 4) : rootAt Q split (fourKind t) (fourWord Q t) :=
    ⟨(![(a : X ⧸ Q.D),(b : X ⧸ Q.D),(c : X ⧸ Q.D),(d : X ⧸ Q.D)] : Fin 4 → X ⧸ Q.D) t,by
      fin_cases t
      · exact a.property
      · exact b.property
      · exact c.property
      · exact d.property⟩
  have hz' := source_ordered_frattini_product_support Q split n hn m ν T hC μ hB
    hm hcore hmpos 1 fourKind (fourWord Q) (four_root_le Q split hm)
    (four_reflections_distinct Q hm) z (by simpa [z,List.ofFn_succ,mul_assoc] using hz)
  exact ⟨hz' 0,hz' 1,hz' 2⟩

include ν hC μ hB hn in
/-- The perpendicular commutator lies in the actual radical Frattini subgroup. -/
theorem source_positive_perpendicular_le_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ ≤
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  let A := simpleRoot Q split 1
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let F := (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype
  let K := F ⊔ E
  have hEP : E ≤ Endpoint Q 1 := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2.trans
    (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _)))
  have hAP : A ≤ Endpoint Q 1 := (simpleRoot_le Q split 1).trans
    (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hPF : Endpoint Q 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    source_frattini_parabolic_normalizes Q split 1 m μ hB
  have hΩF := (omegaOneAmbient_le A).trans (hAP.trans hPF)
  have hΩE : ⁅omegaOneAmbient A,E⁆ ≤ F :=
    (source_positive_omega_perpendicular_le Q split n hn m ν T hC μ hB hm hcore hmpos hc).trans
      (source_omega_le_frattini Q split 1 m μ hB _
        (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.1)
  have hΩK : omegaOneAmbient A ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal K F E (omegaOneAmbient A) K
      le_normalizer le_sup_left le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp hΩF).trans le_sup_left
    · rw [commutator_comm]
      exact hΩE.trans le_sup_left
  let s := UnitarySource.actorReflection Q split 1
  have hsK : (s.val : X ⧸ Q.D) ∈ normalizer (K : Set (X ⧸ Q.D)) :=
    normalizer_inf_normalizer_le_normalizer_sup F E
      ⟨hPF ((rankOne_le_parabolic Q split 1) s.mem_rankOne),
        perpendicular_root_normalizes Q split hm 1 0 (by decide) s.val s.class_eq⟩
  have hAK : A ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    apply (show A ≤ rankOne Q split 1 from le_sup_left).trans
    rw [←positive_suzuki_omega_reflection_generate Q split 1 m μ hB hmpos s]
    exact sup_le hΩK (zpowers_le.mpr hsK)
  intro z hz
  have hzK : z ∈ K := ((commutator_mono le_rfl (show E ≤ K from le_sup_right)).trans
    (le_normalizer_iff_commutator_le_right.mp hAK)) hz
  obtain ⟨p,hp,e,he,hpe⟩ : ∃ p ∈ F, ∃ e ∈ E, p*e=z := by
    have hprod := coe_mul_of_right_le_normalizer_left F E (hEP.trans hPF)
    change z ∈ ((F ⊔ E : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) at hzK
    rw [hprod] at hzK
    exact hzK
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,rfl⟩ :=
    source_positive_perpendicular_product_support Q split n hn m ν T hC μ hB hm hcore hmpos hc z hz
  have hprod : b*c*d*e⁻¹ ∈ F := by
    change p*e = b*c*d at hpe
    rw [←hpe,mul_inv_cancel_right]
    exact hp
  obtain ⟨hbF,hcF,hdF⟩ := four_coordinates_in_frattini Q split n hn m ν T hC μ hB hm hcore hmpos
    ⟨b,hb⟩ ⟨c,omegaOneAmbient_le _ hc'⟩ ⟨d,hd⟩ ⟨e⁻¹,E.inv_mem he⟩ hprod
  exact F.mul_mem (F.mul_mem hbF hcF) hdF

include ν hC μ hB hn in
/-- Reflection and the first-linear-root intersection remove both linear
factors from the positive perpendicular commutator. -/
theorem source_positive_perpendicular_le_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
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
  have hPhi := source_positive_perpendicular_le_frattini Q split n hn m ν T hC μ hB hm hcore hmpos hc
  have hdj := source_frattini_disjoint_first_linear Q split 1 0 m μ hB ν T hC
  intro z hz
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,rfl⟩ :=
    source_positive_perpendicular_product_support Q split n hn m ν T hC μ hB hm hcore hmpos hc z hz
  have hbF := (four_coordinates_in_frattini Q split n hn m ν T hC μ hB hm hcore hmpos
    ⟨b,hb⟩ ⟨c,omegaOneAmbient_le _ hc'⟩ ⟨d,hd⟩ 1 (by simpa only [coe_one,mul_one] using hPhi hz)).1
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
  have hcd : Commute c d :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_shifted_pair_commute Q split 1 0 m μ hB ν T hC hm (by decide))
        (omegaOneAmbient_le _ hc')) d hd).symm
  have hgdF := (four_coordinates_in_frattini Q split n hn m ν T hC μ hB hm hcore hmpos
    ⟨g d,hgd⟩ ⟨g c,omegaOneAmbient_le _ hgc⟩ 1 1 (by
      simpa only [coe_one,mul_one,←map_mul,hcd.eq] using hgz)).1
  have hd1 : d = 1 := g.injective ((disjoint_def.mp hdj hgd hgdF).trans (map_one g).symm)
  rw [hd1,mul_one]
  exact hc'

include ν hC μ hB hn in
/-- The positive-parameter Suzuki half of (6H)(d). The perpendicular roots
commute; no support, movement or nonzero-commutator premise remains. -/
theorem source_positive_perpendicular_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ := by
  have hle := source_positive_perpendicular_le_omega Q split n hn m ν T hC μ hB hm hcore hmpos hc
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
  exact perpendicular_commutator_eq_bot_of_normalizes Q split hm 1 0 (by decide)
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
    (le_sup_left.trans (positive_perpendicular_normalizes_of_omega_normalizes Q split 1 m μ hB
      hmpos hm 0 (by decide) ((commutator_eq_bot_iff_le_centralizer.mp hΩ).trans
        (Subgroup.centralizer_le_normalizer _))))
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
