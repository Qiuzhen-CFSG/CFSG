module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositivePerpendicular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearNear

/-!
# Perpendicular Frattini support, including the binary row

The near commutator equality puts both internal linear factors in Φ(V).
Reflecting a perpendicular commutator therefore places its middle Suzuki
coordinate in Φ(V). An order-four coordinate would force the whole
perpendicular root into Φ(V). The existing Frattini product bound, applied
to the commuting linear factors, excludes this possibility. Thus the
middle coordinate is in Omega for every parameter, including Sz(2).
The square commutator identity then bounds the simple Omega action by the
shifted Omega.

For the binary actor, the actual reflection--Omega product preserves the
perpendicular image in V/Φ(V). Its order is five, while that image has at
most four elements, so it fixes the image. The two faithful Frattini layers
also bound the entire fixed subgroup in V/Φ(V) by four elements. These are
the fixed-image and size steps on Fong--Seitz I (1973), printed p.54.
Preservation of that image by the whole binary actor, hence perpendicular
commutation and the remaining (6H) conclusions, is still required.

Natural panel markings, odd linear degree and faithful Borel remain
explicit. OriginalPerpendicularFrattini applies the results to the original
root parameters and the literal Q.q image of the original two-core.
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
/-- The narrower perpendicular product support holds also in the binary row. -/
theorem source_perpendicular_product_support
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (z : X ⧸ Q.D)
    (hz : z ∈ ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆) :
    z ∈ (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  let V := simpleRemainder Q split 1
  let F := (frattini V).map V.subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let s := (representative (Q.simple 0) : X ⧸ Q.D)
  let e := (MulAut.conj s).symm
  have hPF : Endpoint Q 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    source_frattini_parabolic_normalizes Q split 1 m μ hB
  have hAF : simpleRoot Q split 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    (simpleRoot_le Q split 1).trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hPF))
  have hHF : Q.tits.B ⊓ Q.tits.N ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    (inf_le_left.trans (Q.tits.B_le_standardParabolic _)).trans hPF
  have hphi : ⁅V,V⁆ ≤ F := by
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
  have hzF : e z ∈ F := by
    have hh := he_mem _ hz
    change e z ∈ rightConjugate ⁅simpleRoot Q split 1,E⁆ s at hh
    rw [show rightConjugate ⁅simpleRoot Q split 1,E⁆ s =
      ⁅rootAt Q split 1 (Q.simple 0),rightConjugate E s⁆ from right_comm Q _ _ _,hE] at hh
    exact hphi ((commutator_mono (root_remainder Q split hm 2) (root_remainder Q split hm 3)) hh)
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,rfl⟩ := distance_four_commutator_support Q split hm 1 0
    (by decide) (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) z hz
  have hlin := internal_linear_le_frattini Q split n hn m ν T hC μ hB hm hcore hc
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
    have he_cF : e c ∈ F := by
      have hh := F.mul_mem (F.inv_mem (hlin.1 he_b)) (F.mul_mem hzF (F.inv_mem (hlin.2 he_d)))
      simpa only [map_mul,mul_inv_cancel_right,inv_mul_cancel_left] using hh
    have hwhole : E ≤ F := suzuki_rootAt_le_of_invariant_of_square_ne_one Q split 1 m μ hB _ F hHF
      (e c) he_c he_cF (fun heq => hc2 (e.injective (by simpa only [map_pow,map_one] using heq)))
    have hzPhi : b*c*d ∈ F := ((commutator_mono le_rfl hwhole).trans
      (le_normalizer_iff_commutator_le_right.mp hAF)) hz
    have hBC : ⁅rootAt Q split 0 (Q.simple 1),rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥ := by
      have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
        (adjacent_commutator_eq_bot Q split hm 0 1 (by decide)
          (marked_linear_remainder_le_kernel Q split 0 ν T hC)
          (marked_suzuki_remainder_le_kernel Q split 1 m μ hB))
      simpa only [right_comm,right_bot,right_rep,right_simple] using hh
    have hBD : ⁅rootAt Q split 0 (Q.simple 1),rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
      have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
        (source_linear_near_commute Q split n hn m ν T hC μ hB hm hcore hc)
      simpa only [right_comm,right_bot,right_rep,right_simple,mul_assoc] using hh
    have hbc : Commute b c :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBC hb) c hc').symm
    have hbd : Commute b d :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBD hb) d hd).symm
    have hcd : Commute c d :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (source_shifted_pair_commute Q split 1 0 m μ hB ν T hC hm (by decide)) hc') d hd).symm
    have hbd2 : (b*d)^2 = 1 := by
      rw [hbd.mul_pow,linear_square Q split n ν T hC _ b hb,
        linear_square Q split n ν T hC _ d hd,mul_one]
    have hcp : Commute c (b*d) := hbc.symm.mul_right hcd
    have hpF : c*(b*d) ∈ F := by
      rw [←mul_assoc,←hbc.eq]
      exact hzPhi
    have hp2 : (c*(b*d))^2 ≠ 1 := by simpa only [hcp.mul_pow,hbd2,mul_one] using hc2
    have hlarge := frattini_product_order_four_forces_card Q split 1
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) m μ hB hc hm 0 (by decide)
      (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2 ⟨c,hc'⟩ (b*d) hcp hbd2 hpF hp2
    have hcard : Nat.card (simpleRoot Q split 0) = 2^(2*m+1) := by
      rw [Nat.card_congr (linearRootEquiv Q split 0 ν T hC).toEquiv,
        Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 n hn.pos.ne',
        ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
    rw [hcard] at hlarge
    exact (Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2))
      (by decide : 4 < 6)).not_ge hlarge
  exact ⟨b*c,⟨b,hb,c,hΩ,rfl⟩,d,hd,rfl⟩

include ν hC μ hB hn in
/-- The simple Omega moves the perpendicular root only into the shifted
Omega. This is the pre-normalization step in the all-parameter (6H)(d) proof. -/
theorem source_omega_perpendicular_le
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
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
  obtain ⟨bc,⟨b,hb,c,hc',rfl⟩,d,hd,hz⟩ := source_perpendicular_product_support
    Q split n hn m ν T hC μ hB hm hcore hc ⁅a,y⁆ (commutator_mem_commutator ha hy)
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


include ν hC μ hB hn in
/-- The genuine reflection--Omega product preserves the perpendicular image modulo Φ(V). -/
theorem source_mover_normalizes_perpendicular_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (frattiniMover Q split 1 m μ hB : X ⧸ Q.D) ∈ normalizer
      (((frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ⊔
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  let F := (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let K := F ⊔ E
  have hPF : Endpoint Q 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    source_frattini_parabolic_normalizes Q split 1 m μ hB
  have hΩF : omegaOneAmbient (simpleRoot Q split 1) ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    (omegaOneAmbient_le _).trans ((simpleRoot_le Q split 1).trans
      (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hPF)))
  have hΩE : ⁅omegaOneAmbient (simpleRoot Q split 1),E⁆ ≤ F :=
    (source_omega_perpendicular_le Q split n hn m ν T hC μ hB hm hcore hc).trans
      (source_omega_le_frattini Q split 1 m μ hB _ (root_remainder Q split hm 3))
  have hΩK : omegaOneAmbient (simpleRoot Q split 1) ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal K F E (omegaOneAmbient (simpleRoot Q split 1)) K
      le_normalizer le_sup_left le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp hΩF).trans le_sup_left
    · rw [commutator_comm]
      exact hΩE.trans le_sup_left
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  have hsK : (s.val : X ⧸ Q.D) ∈ normalizer (K : Set (X ⧸ Q.D)) :=
    normalizer_inf_normalizer_le_normalizer_sup F E
      ⟨hPF ((rankOne_le_parabolic Q split 1) s.mem_rankOne),
        perpendicular_root_normalizes Q split hm 1 0 (by decide) s.val s.class_eq⟩
  have hu : (suzukiParameter Q split 1 m μ hB 0 1 : X ⧸ Q.D) ∈
      omegaOneAmbient (simpleRoot Q split 1) := by
    rw [←suzukiOmegaParameter_range Q split 1 m μ hB]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  exact (normalizer (K : Set (X ⧸ Q.D))).mul_mem hsK (hΩK hu)

omit m μ hB in
include ν hC hn in
/-- The actual binary quintic action has at most four fixed points on V/Φ(V). -/
theorem source_binary_mover_frattini_fixed_card_le
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    Nat.card (quotientAut (frattini (simpleRemainder Q split 1))
      ((radicalSection Q split 1 (marked_suzuki_remainder_le_kernel Q split 1 0 μ hB)).numeratorAction
        (frattiniMover Q split 1 0 μ hB))).fixedSubgroup ≤ 4 := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
  let d := radicalSection Q split 1 hV
  let c := frattiniMover Q split 1 0 μ hB
  let a := quotientAut (frattini d.numerator) (d.numeratorAction c)
  have hcomm := (source_six_three Q split 1 0 0 μ hB ν T hC hm (by decide)).2
  have ho := binary_frattiniMover_order Q split 1 hV μ hB hm 0 (by decide) hcomm
  have ha5 : a^5 = 1 := by rw [←map_pow,←map_pow,←ho,pow_orderOf_eq_one,map_one,map_one]
  have hindex := quintic_fixed_index_ge (d.isTwo.to_quotient (frattini d.numerator)) a ha5
    (binary_mover_frattini_quotient_ne_one Q split 1 hV μ hB hc hm 0 (by decide) hcomm)
  have hsize : Nat.card (simpleRoot Q split 0) ≤ 2^(2*0+1) := by
    rw [Nat.card_congr (linearRootEquiv Q split 0 ν T hC).toEquiv,
      Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 n hn.pos.ne',
      ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hbound := (radical_two_layers_card_le Q split 1 hV 0 μ hB hc hm 0 (by decide) hcomm hsize).1
  have he := a.fixedSubgroup.index_mul_card
  change a.fixedSubgroup.index*Nat.card a.fixedSubgroup =
    Nat.card (d.numerator ⧸ frattini d.numerator) at he
  change Nat.card a.fixedSubgroup ≤ 4
  change Nat.card (d.numerator ⧸ frattini d.numerator) ≤ _ at hbound
  norm_num at hbound
  nlinarith

private theorem quintic_fixes_small_invariant {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 2 W) (a : MulAut W) (ha : a^5 = 1)
    (M : Subgroup W) (hM : M.map a.toMonoidHom ≤ M) (hcard : Nat.card M ≤ 4) :
    M ≤ a.fixedSubgroup := by
  have he : M.map a.toMonoidHom = M := eq_of_le_of_card_ge hM
    (le_of_eq (card_map_of_injective a.injective).symm)
  let b : MulAut M := (a.subgroupMap M).trans (MulEquiv.subgroupCongr he)
  have hbpow (k : ℕ) (x : M) : ((b^k) x : W) = (a^k) (x : W) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',pow_succ',MulAut.mul_apply,MulAut.mul_apply]
      change a ((b^k) x : W) = a ((a^k) (x : W))
      rw [ih]
  have hb5 : b^5 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hbpow,ha]
    rfl
  have hb : b = 1 := by
    by_contra hne
    have hi := quintic_fixed_index_ge (hW.to_subgroup M) b hb5 hne
    have hc := b.fixedSubgroup.index_mul_card
    have hp := Nat.card_pos (α := b.fixedSubgroup)
    nlinarith
  intro x hx
  apply (MulAut.mem_fixedSubgroup a x).mpr
  exact congrArg (fun f : MulAut M => (f ⟨x,hx⟩ : W)) hb

omit m μ hB in
include ν hC hn in
/-- The perpendicular root image in V/Φ(V) is fixed by the genuine binary quintic element. -/
theorem source_binary_perpendicular_frattini_fixed
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (v : simpleRemainder Q split 1)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) :
    quotientAut (frattini (simpleRemainder Q split 1))
      ((radicalSection Q split 1 (marked_suzuki_remainder_le_kernel Q split 1 0 μ hB)).numeratorAction
        (frattiniMover Q split 1 0 μ hB)) (QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v) =
      QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
  let d := radicalSection Q split 1 hV
  let V := d.numerator
  let F := (frattini V).map V.subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let K := F ⊔ E
  let c := frattiniMover Q split 1 0 μ hB
  let a := quotientAut (frattini V) (d.numeratorAction c)
  let q := QuotientGroup.mk' (frattini V)
  let M := (E.subgroupOf V).map q
  have hEV : E ≤ V := root_remainder Q split hm 4
  have hPF : Endpoint Q 1 ≤ normalizer (F : Set (X ⧸ Q.D)) :=
    source_frattini_parabolic_normalizes Q split 1 0 μ hB
  have hEF : E ≤ normalizer (F : Set (X ⧸ Q.D)) := hEV.trans
    (inf_le_left.trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hPF)))
  have hcardE : Nat.card E = 4 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = 4
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 0 μ hB).toEquiv,matrixRoot_card]
    norm_num
  have hcardM : Nat.card M ≤ 4 := by
    have hle := Nat.card_le_card_of_surjective (q.subgroupMap (E.subgroupOf V))
      (q.subgroupMap_surjective (E.subgroupOf V))
    have hle' := Nat.card_le_card_of_injective
      (fun x : E.subgroupOf V => (⟨x.val.val,x.property⟩ : E))
      (fun x y h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : E => (z : X ⧸ Q.D)) h)
    exact hle.trans (hle'.trans hcardE.le)
  have hcn := source_mover_normalizes_perpendicular_frattini Q split n hn 0 ν T hC μ hB hm hcore hc
  have hM : M.map a.toMonoidHom ≤ M := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxK : (x : X ⧸ Q.D) ∈ K := (show E ≤ K from le_sup_right) hx
    have hcxK : (c : X ⧸ Q.D)*(x : X ⧸ Q.D)*(c : X ⧸ Q.D)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp hcn _).mp hxK
    change (c : X ⧸ Q.D)*(x : X ⧸ Q.D)*(c : X ⧸ Q.D)⁻¹ ∈ (K : Set (X ⧸ Q.D)) at hcxK
    rw [show (K : Set (X ⧸ Q.D)) = (F : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D)) from
      coe_mul_of_right_le_normalizer_left F E hEF] at hcxK
    obtain ⟨p,⟨t,ht,htp⟩,y,hy,hpy⟩ := hcxK
    have hxy : q (d.numeratorAction c x) = q ⟨y,hEV hy⟩ := by
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hdiv : d.numeratorAction c x / (⟨y,hEV hy⟩ : V) = t := by
        apply Subtype.ext
        change ((c : X ⧸ Q.D)*(x : X ⧸ Q.D)*(c : X ⧸ Q.D)⁻¹)/y = t
        rw [←hpy,←htp,mul_div_cancel_right]
        rfl
      rw [hdiv]
      exact ht
    change a (q x) ∈ M
    rw [show a (q x) = q (d.numeratorAction c x) from quotientAut_apply_mk _ _ _,hxy]
    exact mem_map_of_mem q hy
  have hcomm := (source_six_three Q split 1 0 0 μ hB ν T hC hm (by decide)).2
  have ho := binary_frattiniMover_order Q split 1 hV μ hB hm 0 (by decide) hcomm
  have ha5 : a^5 = 1 := by rw [←map_pow,←map_pow,←ho,pow_orderOf_eq_one,map_one,map_one]
  exact (MulAut.mem_fixedSubgroup a (q v)).mp
    (quintic_fixes_small_invariant (d.isTwo.to_quotient (frattini V)) a ha5 M hM hcardM
      (mem_map_of_mem q hv))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
