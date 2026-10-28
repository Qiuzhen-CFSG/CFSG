module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SeparatedProducts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositivePerpendicularBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryTerminal
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FiveRootIntervals

/-!
# Both positive near-commutator branches on the marked octagon

Coordinate separation on the actual radical Frattini quotient restricts the
perpendicular coordinate of the four-root commutator product to Omega.
This Omega centralizes its own root, giving the three-subgroup argument
when (6.4) is nonzero. If (6.4) also vanishes, the five-root interval makes
the perpendicular commutator centralize the simple Suzuki root. Its derived
subgroup is Omega, so the three-subgroup lemma again gives the required
Omega centralization. Generation and (6.1) close both positive branches.

The final theorem combines this with the proved binary branch, for every
m>=0. It retains the natural panel markings, odd linear degree and faithful
Borel. Pairing, odd degree and the remaining (6H) are not asserted here.

Source: Fong--Seitz I (1973), (6H)(b), pp.52--54. The nonzero branch uses
only the proved Omega support, preserving the Sz(8) obstruction to the
printed whole-root centrality claim. OriginalSeparatedNear and Section10Near
retain the original endpoint, literal Q.q and every actual N-conjugate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private def supportKind : Fin 4 → Fin 2 := ![1,0,1,0]
private def supportWord : Fin 4 → Weyl Q :=
  ![Q.simple 0,Q.simple 1*Q.simple 0,Q.simple 0*Q.simple 1*Q.simple 0,
    Q.simple 1*Q.simple 0*Q.simple 1]

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem sinv (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)

set_option linter.unusedSimpArgs false in
private theorem support_root_le (hm : rotationOrder Q = 8) (t : Fin 4) :
    rootAt Q split (supportKind t) (supportWord Q t) ≤ simpleRemainder Q split 1 := by
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
  fin_cases t <;> dsimp [supportKind,supportWord] <;>
    apply rootAt_le_remainder Q split _ 1 _ <;>
    simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple 0) (Q.simple 0),
      ←mul_assoc (Q.simple 1) (Q.simple 1),ssq,one_mul,mul_one,←mul_assoc,
      Q.tits.wordLength_one,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,
      h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2]

set_option linter.unusedSimpArgs false in
private theorem support_reflections_distinct (hm : rotationOrder Q = 8) :
    Pairwise fun t u : Fin 4 =>
      (supportWord Q t)⁻¹*Q.simple (supportKind t)*(supportWord Q t) ≠
        (supportWord Q u)⁻¹*Q.simple (supportKind u)*(supportWord Q u) := by
  intro t u htu he
  have hh := congrArg (weylEquiv Q) he
  simp only [map_mul,map_inv,supportWord,supportKind] at hh
  fin_cases t <;> fin_cases u <;> try exact htu rfl
  all_goals
    simp [map_mul,map_inv,weylEquiv_simple_zero,weylEquiv_simple_one] at hh
    rw [hm] at hh
    norm_num [DihedralGroup.sr_mul_sr,DihedralGroup.r_mul_sr,DihedralGroup.sr_mul_r] at hh
    revert hh
    decide

include ν hC μ hB hn in
/-- The full four-root product has only Omega support in its perpendicular
coordinate under the vanishing near-commutator assumption. -/
theorem source_positive_four_product_perpendicular_support
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥)
    (a : rootAt Q split 1 (Q.simple 0))
    (b : rootAt Q split 0 (Q.simple 1*Q.simple 0))
    (c : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))
    (d : rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1))
    (hz : (a : X ⧸ Q.D)*b*c*d ∈
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype) :
    (c : X ⧸ Q.D) ∈ omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let z (t : Fin 4) : rootAt Q split (supportKind t) (supportWord Q t) :=
    ⟨(![(a : X ⧸ Q.D),(b : X ⧸ Q.D),(c : X ⧸ Q.D),(d : X ⧸ Q.D)] : Fin 4 → X ⧸ Q.D) t,by
      fin_cases t
      · exact a.property
      · exact b.property
      · exact c.property
      · exact d.property⟩
  have hz' := source_ordered_frattini_product_support Q split n hn m ν T hC μ hB
    hm hcore hmpos 1 supportKind (supportWord Q) (support_root_le Q split hm)
    (support_reflections_distinct Q hm) z (by
      simpa [z,List.ofFn_succ,mul_assoc] using hz)
  have hcp : (c : X ⧸ Q.D) ∈
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := hz' 2
  have hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1) := by
    rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
      (UnitarySource.actorReflection Q split) hcore]
  exact (source_positive_perpendicular_frattini_of_near_trivial Q split 1 0 m μ hB n hn.pos ν T hC
    hmpos hc hm (by decide) hsize hnear).le ⟨hcp,c.property⟩

set_option linter.unusedSimpArgs false in
include ν hC μ hB hn in
/-- The distance-five commutator has Omega, rather than whole-root, support
in the perpendicular factor of its ordered product. -/
theorem source_positive_distance_five_omega_support
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥)
    (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆) :
    x ∈ (rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  have hJV : simpleRoot Q split 0 ≤ simpleRemainder Q split 1 := by
    have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
    have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
    have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one] at h0 h1 h10
    rw [←rootAt_one Q split 0]
    apply rootAt_le_remainder Q split 0 1 1 <;>
      simp only [inv_one,mul_one,one_mul,Q.tits.wordLength_one,h0,h1,h10]
  let V := simpleRemainder Q split 1
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hPhi : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hxp := hPhi ((commutator_mono hJV
    (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.1) hx)
  obtain ⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc',rfl⟩,d,hd,rfl⟩ :=
    distance_five_commutator_support Q split hm 0 1 (by decide)
      (marked_linear_remainder_le_kernel Q split 0 ν T hC)
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) x hx
  have hΩ := source_positive_four_product_perpendicular_support Q split n hn m ν T hC μ hB
    hm hcore hmpos hc hnear ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc'⟩ ⟨d,hd⟩ hxp
  exact ⟨a*b*c,⟨a*b,⟨a,ha,b,hb,rfl⟩,c,hΩ,rfl⟩,d,hd,rfl⟩
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot]
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) =
      rootAt Q split k w := rfl
private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)
private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate, comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _


include ν hC μ hB hn in
private theorem positive_omega_perpendicular_of_near_trivial_of_six_four
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥)
    (hfour : ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1))) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ := by
  have hKi := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  have hKj := marked_linear_remainder_le_kernel Q split 0 ν T hC
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hCE : ⁅rootAt Q split 1 (Q.simple 0),E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) hnear
    simpa only [right_comm,right_bot,right_simple,right_rep] using hh
  have hDE : ⁅rootAt Q split 0 (Q.simple 1*Q.simple 0),E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 0 1 (by decide) hKj hKi)
    simpa only [right_comm,right_bot,right_simple,right_rep,←mul_assoc] using hh
  have hED : ⁅E,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 1 0 (by decide) hKi hKj)
    rw [right_comm,right_bot,right_simple,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).1] at hh
    exact hh
  have hΩE : omegaOneAmbient E ≤ centralizer (E : Set (X ⧸ Q.D)) := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (commutator_eq_bot_iff_le_centralizer.mpr (suzukiOmega_centralizes Q split 1 m μ hB))
    rw [right_comm,right_bot,right_omega,right_simple] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hbase : ⁅⁅simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆,E⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    obtain ⟨bcd,⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ :=
      source_positive_distance_five_omega_support Q split n hn m ν T hC μ hB hm hcore hmpos hc hnear x hx
    exact (centralizer (E : Set (X ⧸ Q.D))).mul_mem
      ((centralizer (E : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (E : Set (X ⧸ Q.D))).mul_mem
          (commutator_eq_bot_iff_le_centralizer.mp hCE hb)
          (commutator_eq_bot_iff_le_centralizer.mp hDE hc))
        (hΩE hd))
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hED) he)
  have hrot : ⁅⁅rootAt Q split 0 (Q.simple 1),rootAt Q split 1 (Q.simple 0)⁆,E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hbase
    rw [right_comm,right_comm,right_bot,right_simple,
      show rightConjugate E (representative (Q.simple 1) : X ⧸ Q.D) = E from
        perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _),right_rep] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  have htriple : ⁅⁅E,rootAt Q split 0 (Q.simple 1)⁆,rootAt Q split 1 (Q.simple 0)⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrot (by rw [hCE,commutator_bot_left])
  have hfour' : ⁅E,rootAt Q split 0 (Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) hfour
    rw [right_comm,right_simple,right_omega,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.1,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.2] at hh
    exact hh
  rw [hfour'] at htriple
  have hh := congrArg (fun A => rightConjugate A
    (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D)) htriple
  simpa only [right_comm,right_bot,right_omega,right_rep,mul_assoc,
    ←mul_assoc (Q.simple 1) (Q.simple 1),ssq,one_mul,mul_one,rootAt_one] using hh


include ν hC μ hB hn in
/-- The positive-parameter nonzero-(6.4) branch of the near equality.
The proof uses the precise perpendicular Omega product support. -/
theorem source_positive_near_eq_of_six_four_nonzero
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hne : ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ ≠ ⊥) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = rootAt Q split 0 (Q.simple 1) := by
  by_cases hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥
  · have hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1) := by
      rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore]
    have hsmall : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6 :=
      (Nat.pow_le_pow_left hsize 4).trans_lt
        (Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide))
    have hfour := source_six_four_eq_of_nonzero Q split 1 0 m μ hB n hn.pos ν T hC hc hm (by decide) hsmall hne
    exact source_positive_near_eq_of_omega_perpendicular_commutes Q split 1 0 m μ hB n hn.pos ν T hC
      hmpos hc hm (by decide) hsize
      (positive_omega_perpendicular_of_near_trivial_of_six_four Q split n hn m ν T hC μ hB
        hm hcore hmpos hc hnear hfour)
  · exact source_near_eq_of_nonzero Q split 1 0 m μ hB n hn.pos ν T hC hm (by decide) hnear

include μ hB ν hC in
private theorem positive_omega_perpendicular_of_both_trivial
    (hm : rotationOrder Q = 8) (hmpos : 0 < m)
    (hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥)
    (hfour : ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ := by
  let A := simpleRoot Q split 1
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hAB := adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
    (marked_linear_remainder_le_kernel Q split 0 ν T hC)
  have hbase : ⁅⁅A,E⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    obtain ⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,rfl⟩ := distance_four_commutator_support Q split hm 1 0 (by decide)
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) x hx
    exact (centralizer (A : Set (X ⧸ Q.D))).mul_mem
      ((centralizer (A : Set (X ⧸ Q.D))).mul_mem
        (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hAB) hb)
        (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hnear) hc))
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hfour) hd)
  have htriple : ⁅⁅A,A⁆,E⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hbase
    (by rwa [commutator_comm E A])
  have hΩ : ⁅A,A⁆ = omegaOneAmbient A := by
    rw [←map_subtype_commutator]
    change (_root_.commutator (simpleRoot Q split 1)).map (simpleRoot Q split 1).subtype = _
    rw [suzuki_derived_eq_frattini Q split 1 m μ hB hmpos,suzuki_frattini_image Q split 1 m μ hB]
  rwa [hΩ] at htriple

include ν hC μ hB hn in
/-- Both terminal positive-parameter branches of the near commutator equality.
No commutator or perpendicular support premise remains. -/
theorem source_positive_near_eq
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = rootAt Q split 0 (Q.simple 1) := by
  by_cases hnear : ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥
  · by_cases hfour : ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥
    · have hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1) := by
        rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
          (UnitarySource.actorReflection Q split) hcore]
      exact source_positive_near_eq_of_omega_perpendicular_commutes Q split 1 0 m μ hB n hn.pos ν T hC
        hmpos hc hm (by decide) hsize
        (positive_omega_perpendicular_of_both_trivial Q split n m ν T hC μ hB hm hmpos hnear hfour)
    · exact source_positive_near_eq_of_six_four_nonzero Q split n hn m ν T hC μ hB hm hcore hmpos hc hfour
  · exact source_near_eq_of_nonzero Q split 1 0 m μ hB n hn.pos ν T hC hm (by decide) hnear

include ν hC μ hB hn in
/-- The source near-commutator equality for every Suzuki parameter. The
natural panel markings, odd linear degree and faithful Borel remain the
preceding source inputs; both terminal commutator cases are proved. -/
theorem source_near_eq_of_odd_degree
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = rootAt Q split 0 (Q.simple 1) := by
  by_cases hm0 : m = 0
  · subst m
    have hsize : Nat.card (BinaryGaloisField n) ≤ 2 := by
      rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore]
      norm_num
    exact source_binary_near_eq Q split 1 0 μ hB n hn.pos ν T hC hc hm (by decide) hsize
  · exact source_positive_near_eq Q split n hn m ν T hC μ hB hm hcore (by omega) hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
