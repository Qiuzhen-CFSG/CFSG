module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedProduct
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.InvariantLayer

/-!
# The third commutator and the remaining mixed root clauses

The exact five-factor radical is a faithful Suzuki module of order q⁵.
Its third commutator is proper by nilpotence and contains the fixed
perpendicular Omega subgroup of order q. The prime-index bound therefore
identifies the third commutator with that Omega subgroup. Reflection then
kills the remaining perpendicular linear commutator in (6H)(d).

The same identity bounds the last Omega commutator. If it vanished,
five ordered root factors of total order q⁷ would centralize the simple
Omega subgroup, contradicting the q⁶ bound in (6.1). Cartan transitivity
then gives the full equality in (6H)(e), including q=2.
OriginalThirdCommutator and Section10ThirdCommutator retain the original
quotient maps and discharge the corresponding literal Section 10 clauses.
The full center identities, pairing and odd-degree inputs remain open.
Source: Fong--Seitz I (1973), (6H)(d,e,g), pp.55--56.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
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

private theorem third_ne_derived (V : Subgroup (X ⧸ Q.D))
    [Group.IsNilpotent V] (hne : ⁅V,V⁆ ≠ ⊥) : ⁅V,⁅V,V⁆⁆ ≠ ⁅V,V⁆ := by
  intro he
  have hs (k : ℕ) : V.lowerCentralSeries (k+1) = ⁅V,V⁆ := by
    induction k with
    | zero => rw [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
    | succ k ih =>
      rw [Nat.succ_add,Subgroup.lowerCentralSeries_succ,ih,commutator_comm]
      exact he
  obtain ⟨k,hk⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries V).mp inferInstance
  have hle := V.lowerCentralSeries_antitone (Nat.le_succ k)
  rw [hs,hk] at hle
  exact hne (bot_unique hle)

include ν hC μ hB hn in
private theorem perpendicular_omega_le_third
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
      ⁅simpleRemainder Q split 1,⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆⁆ := by
  have hD : rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
    rw [source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm hcore hc]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D))
    (source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc)
  have hOmega (A : Subgroup (X ⧸ Q.D)) :
      rightConjugate (omegaOneAmbient A) (representative (Q.simple 0) : X ⧸ Q.D) =
        omegaOneAmbient (rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm']
    exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _
  rw [right_comm,right_simple,hOmega,
    perpendicular_root_stable Q split hm 0 1 (by decide) _ (representative_spec _),right_rep] at hh
  exact hh.symm.le.trans (commutator_mono (root_remainder Q split hm 2) hD)

include ν hC μ hB hn in
/-- The third commutator subgroup is precisely the perpendicular Omega root. -/
theorem source_radical_third_eq_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRemainder Q split 1,⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let V := simpleRemainder Q split 1
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let d := frattiniRadicalSection Q split 1 hV
  let D := d.numerator
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let Z := omegaOneAmbient E
  let K := ⁅V,D⁆
  have hD : D = ⁅V,V⁆ := (source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc).symm
  have hKD : K ≤ D := by
    apply le_normalizer_iff_commutator_le_right.mp
    exact V.le_normalizer.trans (normalizer_le_normalizer_characteristic_image V (frattini V))
  have hZK : Z ≤ K := by
    rw [show K = ⁅V,⁅V,V⁆⁆ from congrArg (fun R => ⁅V,R⁆) hD]
    exact perpendicular_omega_le_third Q split n hn m ν T hC μ hB hm hcore hc
  have hDn : D ≠ ⊥ := by
    intro he
    have hcard := (source_radical_derived_data Q split n hn m ν T hC μ hB hm hcore hc).2
    rw [←hD,he,Subgroup.card_bot] at hcard
    have hq : 1 < (2^(2*m+1))^5 := Nat.one_lt_pow (by decide)
      (Nat.one_lt_pow (by omega) (by decide))
    exact hq.ne hcard
  have hKne : K ≠ D := by
    let : Group.IsNilpotent V := (split.isTwo.to_le (show V ≤ split.U from inf_le_left)).isNilpotent
    rw [show K = ⁅V,⁅V,V⁆⁆ from congrArg (fun R => ⁅V,R⁆) hD,hD]
    exact third_ne_derived Q V (hD ▸ hDn)
  let e := suzukiActorEquiv Q split 1 m μ hB
  let f : SuzukiMatrixGroup m →* MulAut D := d.numeratorAction.comp e.symm.toMonoidHom
  have hfaith := frattiniRadical_effectiveAction_injective Q split 1 hV m μ hB hm 0 (by decide)
    (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2
  have hf : Function.Injective f := by
    intro a b hab
    apply e.symm.injective
    apply hfaith
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [d.effectiveAction_mk,d.effectiveAction_mk]
      exact congrArg QuotientGroup.mk (congrArg (fun t : MulAut D => t z) hab)
  have hKN : rankOne Q split 1 ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split 1 hV
        (rankOne_le_parabolic Q split 1 hr)),
      mem_normalizer_iff_map_conj_eq.mp (d.normalized hr)]
  have hKinv (g : SuzukiMatrixGroup m) : (K.subgroupOf D).map (f g).toMonoidHom = K.subgroupOf D := by
    apply map_injective D.subtype_injective
    have heq : D.subtype.comp (f g).toMonoidHom =
        (MulAut.conj (e.symm g : X ⧸ Q.D)).toMonoidHom.comp D.subtype := by
      ext x
      exact d.numeratorAction_apply (e.symm g) x
    rw [map_map,heq,←map_map,map_subgroupOf_eq_of_le hKD]
    exact mem_normalizer_iff_map_conj_eq.mp (hKN (e.symm g).property)
  have hfix (g : SuzukiMatrixGroup m) : Z.subgroupOf D ≤ (f g).fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D)⁻¹ = x
    have hcentral := (source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).ge
      (omegaOneAmbient_le E hx)
    have hh := mem_centralizer_iff.mp hcentral.2 (e.symm g : X ⧸ Q.D) (e.symm g).property
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D) = (x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D) at hh
    rw [hh,mul_inv_cancel_right]
  have hDcard : Nat.card D = (2^(2*m+1))^5 := by
    rw [hD]
    exact (source_radical_derived_data Q split n hn m ν T hC μ hB hm hcore hc).2
  have hZcard : Nat.card (Z.subgroupOf D) = 2^(2*m+1) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZK.trans hKD)).toEquiv]
    let a := (MulAut.conj (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)).symm
    have he : (simpleRoot Q split 1).map a.toMonoidHom = E := by
      simp only [E,rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
    change Nat.card (omegaOneAmbient E) = _
    rw [←he,←map_omegaOneAmbient_injective a.toMonoidHom a.injective,card_map_of_injective a.injective]
    exact suzukiOmega_card Q split 1 m μ hB
  have hKtop : K.subgroupOf D ≠ ⊤ := by
    intro he
    have hh := congrArg (fun R : Subgroup D => R.map D.subtype) he
    rw [map_subgroupOf_eq_of_le hKD,←MonoidHom.range_eq_map,D.range_subtype] at hh
    exact hKne hh
  have he := suzuki_proper_invariant_eq_fixed_layer d.isTwo m f hf (Z.subgroupOf D) (K.subgroupOf D)
    (subgroupOf_mono D hZK) hKtop hfix hKinv hDcard hZcard
  have hh := congrArg (fun R : Subgroup D => R.map D.subtype) he
  rw [map_subgroupOf_eq_of_le hKD,map_subgroupOf_eq_of_le (hZK.trans hKD)] at hh
  simpa only [K,hD] using hh

include ν hC μ hB hn in
/-- The remaining perpendicular linear commutator in (6H)(d) is trivial. -/
theorem source_linear_perpendicular_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
  let C := ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let G := rootAt Q split 1 (Q.simple 0)
  let w := Q.simple 1*Q.simple 0*Q.simple 1
  have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
  have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
  have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
  have h01 := wordLength_alternatingWord Q false (n := 2) (by omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one] at h0 h1 h10 h01
  have hHV : simpleRoot Q split 0 ≤ simpleRemainder Q split 1 := by
    rw [←rootAt_one Q split 0]
    apply rootAt_le_remainder Q split 0 1 1 <;>
      simp only [inv_one,mul_one,one_mul,Q.tits.wordLength_one,h0,h1,h10]
  have hDJ : rootAt Q split 0 w ≤ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
    rw [source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm hcore hc]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hCE : C ≤ E := ((commutator_mono hHV hDJ).trans_eq
    (source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm hcore hc)).trans (omegaOneAmbient_le E)
  have hCG : C ≤ G := by
    have hh := comap_mono (f := (MulAut.conj (representative w : X ⧸ Q.D)).toMonoidHom) hCE
    change rightConjugate C (representative w : X ⧸ Q.D) ≤ rightConjugate E (representative w : X ⧸ Q.D) at hh
    have hww : w*w = 1 := by
      dsimp only [w]
      simp only [mul_assoc,←mul_assoc (Q.simple 1) (Q.simple 1),
        ←mul_assoc (Q.simple 0) (Q.simple 0),ssq,one_mul]
    change rightConjugate ⁅simpleRoot Q split 0,rootAt Q split 0 w⁆ _ ≤ _ at hh
    rw [right_comm,right_simple,right_rep,hww,rootAt_one,commutator_comm,
      (four_interval_reflection Q split hm 0 1 (by decide) _ (representative_spec w)).2.2] at hh
    exact hh
  have hGE : Disjoint G E := by
    apply rootAt_disjoint Q split 1 (Q.simple 0) (Q.simple 0*Q.simple 1*Q.simple 0)
    simp only [mul_inv_rev,sinv,←mul_assoc,ssq,one_mul,h0,h01]
  exact bot_unique ((le_inf hCG hCE).trans hGE.le_bot)

private theorem seven_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split true 7 =
      [simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0),rootAt Q split 1 (Q.simple 0)] := by
  have h0 := perpendicular_root_stable Q split hm 0 1 (by decide)
    (representative (Q.simple 0)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm 1 0 (by decide)
    (representative (Q.simple 1)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) h0
  have h6 := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)) h1
  simp only [right_rep,mul_assoc,ssq,mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    List.map_cons,List.map_nil,right_simple,right_rep]
  rw [h1,h5,h6]
  simp only [mul_assoc,ssq,mul_one]

private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _

include ν hC μ hB hn in
/-- The upper bound in the last Omega commutator clause of (6H). -/
theorem source_omega_far_linear_le
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ ≤
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  have hJ : omegaOneAmbient (rootAt Q split 1 (Q.simple 0)) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
    rw [source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm hcore hc]
    exact le_sup_right
  have hh := (commutator_mono hJ (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1).trans_eq
    ((commutator_comm _ _).trans (source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm hcore hc))
  have ht := comap_mono (f := (MulAut.conj (representative (Q.simple 0) : X ⧸ Q.D)).toMonoidHom) hh
  change rightConjugate _ (representative (Q.simple 0) : X ⧸ Q.D) ≤ rightConjugate _ (representative (Q.simple 0) : X ⧸ Q.D) at ht
  simpa only [right_comm,right_omega,right_rep,mul_assoc,ssq,mul_one,rootAt_one] using ht

include ν hC μ hB hn in
/-- The last Omega commutator is nonzero: otherwise five full root factors
would violate the source Omega-centralizer bound (6.1). -/
theorem source_omega_far_linear_ne_bot
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ ≠ ⊥ := by
  intro hz
  let V := simpleRemainder Q split 1
  let A := omegaOneAmbient (simpleRoot Q split 1)
  let B := rootAt Q split 0 (Q.simple 1)
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let F := rootAt Q split 0 (Q.simple 1*Q.simple 0)
  let Z := V ⊓ centralizer (A : Set (X ⧸ Q.D))
  have hBV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1
  have hCV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.1
  have hEV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
  have hBz : B ≤ Z := le_inf hBV (le_centralizer_iff.mp
    ((omegaOneAmbient_le _).trans (commutator_eq_bot_iff_le_centralizer.mp
      (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC)))))
  have hCz : C ≤ Z := le_inf hCV (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2))
  have hDz : D ≤ Z := le_inf (root_remainder Q split hm 1) (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (source_six_four_support_of_odd_degree Q split hc hm n hn m ν T hC μ hB hcore).2))
  have hEz : E ≤ Z := le_inf hEV (le_centralizer_iff.mp
    ((omegaOneAmbient_le _).trans (commutator_eq_bot_iff_le_centralizer.mp
      (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc))))
  have hFz : F ≤ Z := le_inf (root_remainder Q split hm 0) (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hz))
  let f : B × C × D × E × F → Z := fun p =>
    ⟨(p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2.1*p.2.2.2.2,
      mul_mem (mul_mem (mul_mem (mul_mem (hBz p.1.property) (hCz p.2.1.property))
        (hDz p.2.2.1.property)) (hEz p.2.2.2.1.property)) (hFz p.2.2.2.2.property)⟩
  have hf : Function.Injective f := by
    have hi : Function.Injective (rootProduct (orderedRoots Q split true 7)) := by
      intro p q he
      apply (orderedCoordinates Q split true 7 (by omega)).injective
      apply Subtype.ext
      simpa only [orderedCoordinates_apply] using he
    rw [seven_list Q split hm] at hi
    intro p q he
    have hh := hi
      (a₁ := (1,p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2,1,PUnit.unit))
      (a₂ := (1,q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2,1,PUnit.unit))
      (by simpa only [f,rootProduct,coe_one,one_mul,mul_one,mul_assoc] using congrArg Subtype.val he)
    exact congrArg (fun z => (z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1)) hh
  let q := 2^(2*m+1)
  have hl (w : Weyl Q) : Nat.card (rootAt Q split 0 w) = q := by
    rw [linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hs (w : Weyl Q) : Nat.card (rootAt Q split 1 w) = q^2 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1) (representative w : X ⧸ Q.D)) = _
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1) (representative w)).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]
  have hdom : Nat.card (B × C × D × E × F) = q^7 := by
    simp only [Nat.card_prod,B,C,D,E,F,hl,hs]
    ring
  have hcard : Nat.card (BinaryGaloisField n) = q := by
    rw [GaloisField.card 2 n hn.pos.ne',
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hbound := (source_six_one Q split 1 0 ν T hC m μ hB hc hm (by decide) hcard.le).2
  rw [hcard] at hbound
  have hge := Nat.card_le_card_of_injective f hf
  rw [hdom] at hge
  exact (Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2))
    (by decide : 6 < 7)).not_ge (hge.trans (hbound.trans_eq (by dsimp [q]; ring)))

include ν hC μ hB hn in
/-- The full last commutator equality (6H)(e), including the binary row. -/
theorem source_omega_far_linear_eq
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  have hle := source_omega_far_linear_le Q split n hn m ν T hC μ hB hm hcore hc
  have hne := source_omega_far_linear_ne_bot Q split n hn m ν T hC μ hB hm hcore hc
  apply le_antisymm hle
  obtain ⟨⟨a,ha⟩,han⟩ := ne_bot_iff_exists_ne_one.mp hne
  apply suzuki_rootAt_omega_le_of_invariant Q split 1 m μ hB _ _ ?_ a (hle ha) ha
    (fun he => han (Subtype.ext he))
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    map_omegaOneAmbient_injective _ (MulEquiv.injective _),
    mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split 1 hh),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split 0 _ hh)]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
