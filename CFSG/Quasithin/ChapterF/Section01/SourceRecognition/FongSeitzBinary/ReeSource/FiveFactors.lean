module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Centralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedFrattini
public import Theory.ElementaryAbelian.Join

/-!
# The five elementary factors in the source derived radical

The two internal linear roots and three Suzuki Omega roots commute, by
conjugating (6H)(b),(c),(d) on the same marked octagon. Their product has
unique ordered coordinates and is an elementary abelian subgroup J of
order q⁵ contained in [V,V], where V=U_s₂. The exported equivalence uses
literal multiplication of these five factors in the order of II (10.3).

The perpendicular root E centralizes J and meets it exactly in Omega(E).
Consequently |JE|=q⁶ and Omega(JE)=J. The existing effective-module bound
|[V,V]|≤q⁶ now proves the precise reductio alternative: E≤[V,V] implies
[V,V]=JE and Omega([V,V])=J. Excluding this alternative and proving
[V,V]=J remain source obligations; neither is assumed here.

All statements include m=0, retaining natural panel markings and odd linear
degree. OriginalFiveFactors and Section10FiveFactors apply the subgroup
and reductio calculations to the original two-core and literal N-conjugates.
Source: Fong--Seitz I (1973), proof of (6H)(f), printed p.55;
II (1974), (10.3), printed p.221.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
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

private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _


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

/-- The five root factors in the order used by (10.3). -/
def fiveDerivedFactor (k : Fin 5) : Subgroup (X ⧸ Q.D) :=
  (![omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)),
    rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)),
    rootAt Q split 0 (Q.simple 1*Q.simple 0),
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0))] : Fin 5 → Subgroup (X ⧸ Q.D)) k

/-- The join of the five factors whose equality with the derived radical is (6H)(f). -/
def fiveDerivedSubgroup : Subgroup (X ⧸ Q.D) :=
  (((fiveDerivedFactor Q split 0 ⊔ fiveDerivedFactor Q split 1) ⊔
    fiveDerivedFactor Q split 2) ⊔ fiveDerivedFactor Q split 3) ⊔ fiveDerivedFactor Q split 4

include ν hC μ hB in
private theorem factor_square (k : Fin 5) (x : X ⧸ Q.D)
    (hx : x ∈ fiveDerivedFactor Q split k) : x^2 = 1 := by
  fin_cases k
  · exact omega_square_one Q split m μ hB _ x hx
  · exact linear_square Q split n ν T hC _ x hx
  · exact omega_square_one Q split m μ hB _ x hx
  · exact linear_square Q split n ν T hC _ x hx
  · exact omega_square_one Q split m μ hB _ x hx

private theorem elementary_of_square {Y : Type*} [Group Y]
    (hs : ∀ x : Y, x^2 = 1) : IsElementaryAbelian 2 Y := by
  have hi (x : Y) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  calc
    x*y = (x*y)⁻¹ := (hi _).symm
    _ = y*x := by rw [mul_inv_rev,hi,hi]

include ν hC μ hB hn in
private theorem outer_factor_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅fiveDerivedFactor Q split 0,fiveDerivedFactor Q split 1⁆ = ⊥ ∧
    ⁅fiveDerivedFactor Q split 0,fiveDerivedFactor Q split 3⁆ = ⊥ ∧
    ⁅fiveDerivedFactor Q split 0,fiveDerivedFactor Q split 4⁆ = ⊥ ∧
    ⁅fiveDerivedFactor Q split 1,fiveDerivedFactor Q split 3⁆ = ⊥ ∧
    ⁅fiveDerivedFactor Q split 1,fiveDerivedFactor Q split 4⁆ = ⊥ ∧
    ⁅fiveDerivedFactor Q split 3,fiveDerivedFactor Q split 4⁆ = ⊥ := by
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let F := rootAt Q split 0 (Q.simple 1*Q.simple 0)
  let G := rootAt Q split 1 (Q.simple 0)
  have hD : rightConjugate D (representative (Q.simple 0) : X ⧸ Q.D) = D :=
    perpendicular_root_stable Q split hm 0 1 (by decide) _ (representative_spec _)
  have hDF : rightConjugate D (representative (Q.simple 1) : X ⧸ Q.D) = F := by
    simp only [D,F,right_rep,mul_assoc,ssq,mul_one]
  have hCG : rightConjugate C (representative (Q.simple 1) : X ⧸ Q.D) = G := by
    simp only [C,G,right_rep,mul_assoc,ssq,mul_one]
  have hGF : ⁅G,F⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC))
    simpa only [right_comm,right_bot,right_simple,right_rep] using hh
  have hCD : ⁅C,D⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 1) : X ⧸ Q.D)) hGF
    simpa only [C,D,F,G,right_comm,right_bot,right_rep,mul_assoc] using hh
  have hGD : ⁅omegaOneAmbient G,D⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0) : X ⧸ Q.D))
      (source_six_four_support_of_odd_degree Q split hc hm n hn m ν T hC μ hB hcore).2
    rw [right_comm,right_bot,right_omega,right_simple] at hh
    change ⁅omegaOneAmbient G,rightConjugate D (representative (Q.simple 0) : X ⧸ Q.D)⁆ = ⊥ at hh
    rwa [hD] at hh
  have hCF : ⁅omegaOneAmbient C,F⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 1) : X ⧸ Q.D)) hGD
    simpa only [G,C,right_comm,right_bot,right_omega,right_rep,hDF] using hh
  have hCGc : ⁅C,G⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)
    simpa only [right_comm,right_bot,right_simple,right_rep,mul_assoc,
      ←mul_assoc (Q.simple 0) (Q.simple 0),ssq,one_mul,mul_one] using hh
  have hFD : ⁅F,D⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (source_linear_near_commute Q split n hn m ν T hC μ hB hm hcore hc)
    rw [right_comm,right_bot,right_simple,right_rep] at hh
    have ht : rootAt Q split 0 ((Q.simple 1*Q.simple 0)*(Q.simple 1*Q.simple 0)) = D := by
      rw [←mul_assoc,←right_rep]
      exact hD
    rw [ht] at hh
    exact hh
  have hsub {A B C D : Subgroup (X ⧸ Q.D)} (hA : A ≤ C) (hB : B ≤ D) (h : ⁅C,D⁆ = ⊥) : ⁅A,B⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono hA hB).trans h.le)
  exact ⟨hsub (omegaOneAmbient_le _) le_rfl hCD,hCF,
    hsub (omegaOneAmbient_le _) (omegaOneAmbient_le _) hCGc,
    (commutator_comm _ _).trans hFD,(commutator_comm _ _).trans hGD,
    (commutator_comm _ _).trans (hsub (omegaOneAmbient_le _) le_rfl hGF)⟩

include ν hC μ hB hn in
private theorem factor_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ∀ k : Fin 5, fiveDerivedFactor Q split k ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  intro k
  have hle := source_radical_five_product_le_derived Q split n hn m ν T hC μ hB hm hcore hc
  intro x hx
  apply hle
  fin_cases k <;> dsimp [fiveDerivedFactor] at hx
  · exact ⟨_,⟨_,⟨_,⟨x,hx,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  · exact ⟨_,⟨_,⟨_,⟨1,one_mem _,x,hx,one_mul _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  · exact ⟨_,⟨_,⟨_,⟨1,one_mem _,1,one_mem _,one_mul _⟩,x,hx,one_mul _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  · exact ⟨_,⟨_,⟨_,⟨1,one_mem _,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,x,hx,one_mul _⟩,1,one_mem _,mul_one _⟩
  · exact ⟨_,⟨_,⟨_,⟨1,one_mem _,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,x,hx,one_mul _⟩

include ν hC μ hB hn in
private theorem factor_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ∀ k l : Fin 5, ⁅fiveDerivedFactor Q split k,fiveDerivedFactor Q split l⁆ = ⊥ := by
  have hV (k : Fin 5) : fiveDerivedFactor Q split k ≤ split.U :=
    (factor_le_derived Q split n hn m ν T hC μ hB hm hcore hc k).trans
      ((commutator_le_self _).trans inf_le_left)
  have hZ (k : Fin 5) : ⁅fiveDerivedFactor Q split 2,fiveDerivedFactor Q split k⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((source_perpendicular_omega_centralizes_unipotent Q split n hn m ν T hC μ hB hm hcore hc).trans
        (centralizer_le (hV k)))
  have hself (k : Fin 5) : ⁅fiveDerivedFactor Q split k,fiveDerivedFactor Q split k⁆ = ⊥ := by
    let : IsElementaryAbelian 2 (fiveDerivedFactor Q split k) := elementary_of_square
      (fun x => Subtype.ext (factor_square Q split n m ν T hC μ hB k x x.property))
    exact commutator_self_eq_bot_iff.mpr inferInstance
  obtain ⟨h01,h03,h04,h13,h14,h34⟩ := outer_factor_commute Q split n hn m ν T hC μ hB hm hcore hc
  intro k l
  fin_cases k <;> fin_cases l
  · exact hself 0
  · exact h01
  · exact (commutator_comm _ _).trans (hZ 0)
  · exact h03
  · exact h04
  · exact (commutator_comm _ _).trans h01
  · exact hself 1
  · exact (commutator_comm _ _).trans (hZ 1)
  · exact h13
  · exact h14
  · exact hZ 0
  · exact hZ 1
  · exact hself 2
  · exact hZ 3
  · exact hZ 4
  · exact (commutator_comm _ _).trans h03
  · exact (commutator_comm _ _).trans h13
  · exact (commutator_comm _ _).trans (hZ 3)
  · exact hself 3
  · exact h34
  · exact (commutator_comm _ _).trans h04
  · exact (commutator_comm _ _).trans h14
  · exact (commutator_comm _ _).trans (hZ 4)
  · exact (commutator_comm _ _).trans h34
  · exact hself 4


include ν hC μ hB hn in
/-- The literal five-factor product is an elementary abelian subgroup. -/
theorem source_five_derived_elementary_product
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) ∧
      (fiveDerivedSubgroup Q split : Set (X ⧸ Q.D)) =
        (fiveDerivedFactor Q split 0 : Set (X ⧸ Q.D)) * fiveDerivedFactor Q split 1 *
          fiveDerivedFactor Q split 2 * fiveDerivedFactor Q split 3 * fiveDerivedFactor Q split 4 := by
  let A := fiveDerivedFactor Q split
  have hz (i j : Fin 5) : A i ≤ centralizer (A j : Set (X ⧸ Q.D)) :=
    commutator_eq_bot_iff_le_centralizer.mp (factor_commute Q split n hn m ν T hC μ hB hm hcore hc i j)
  let inst (k : Fin 5) : IsElementaryAbelian 2 (A k) := elementary_of_square
    (fun x => Subtype.ext (factor_square Q split n m ν T hC μ hB k x x.property))
  let h01 : IsElementaryAbelian 2 (A 0 ⊔ A 1 : Subgroup (X ⧸ Q.D)) :=
    IsElementaryAbelian.sup_of_le_centralizer (hz 1 0)
  have h2 : A 2 ≤ centralizer ((A 0 ⊔ A 1 : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (sup_le (hz 0 2) (hz 1 2))
  let h012 : IsElementaryAbelian 2 ((A 0 ⊔ A 1) ⊔ A 2 : Subgroup (X ⧸ Q.D)) :=
    IsElementaryAbelian.sup_of_le_centralizer h2
  have h3 : A 3 ≤ centralizer (((A 0 ⊔ A 1) ⊔ A 2 : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (sup_le (sup_le (hz 0 3) (hz 1 3)) (hz 2 3))
  let h0123 : IsElementaryAbelian 2 (((A 0 ⊔ A 1) ⊔ A 2) ⊔ A 3 : Subgroup (X ⧸ Q.D)) :=
    IsElementaryAbelian.sup_of_le_centralizer h3
  have h4 : A 4 ≤ centralizer ((((A 0 ⊔ A 1) ⊔ A 2) ⊔ A 3 : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (sup_le (sup_le (sup_le (hz 0 4) (hz 1 4)) (hz 2 4)) (hz 3 4))
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer h4,?_⟩
  change (↑((((A 0 ⊔ A 1) ⊔ A 2) ⊔ A 3) ⊔ A 4) : Set (X ⧸ Q.D)) = _
  rw [coe_mul_of_right_le_normalizer_left _ _ (h4.trans (Subgroup.centralizer_le_normalizer _)),
    coe_mul_of_right_le_normalizer_left _ _ (h3.trans (Subgroup.centralizer_le_normalizer _)),
    coe_mul_of_right_le_normalizer_left _ _ (h2.trans (Subgroup.centralizer_le_normalizer _)),
    coe_mul_of_right_le_normalizer_left _ _ ((hz 1 0).trans (Subgroup.centralizer_le_normalizer _))]

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

/-- The direct product of the five literal root factors. -/
abbrev FiveDerivedTuple := fiveDerivedFactor Q split 0 × fiveDerivedFactor Q split 1 ×
  fiveDerivedFactor Q split 2 × fiveDerivedFactor Q split 3 × fiveDerivedFactor Q split 4

private theorem five_product_injective (hm : rotationOrder Q = 8) :
    Function.Injective (fun p : FiveDerivedTuple Q split =>
      (p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2.1*p.2.2.2.2) := by
  have hi : Function.Injective (rootProduct (orderedRoots Q split true 7)) := by
    intro p q he
    apply (orderedCoordinates Q split true 7 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [seven_list Q split hm] at hi
  intro p q he
  have hh := hi
    (a₁ := (1,1,inclusion (omegaOneAmbient_le _) p.1,p.2.1,
      inclusion (omegaOneAmbient_le _) p.2.2.1,p.2.2.2.1,
      inclusion (omegaOneAmbient_le _) p.2.2.2.2,PUnit.unit))
    (a₂ := (1,1,inclusion (omegaOneAmbient_le _) q.1,q.2.1,
      inclusion (omegaOneAmbient_le _) q.2.2.1,q.2.2.2.1,
      inclusion (omegaOneAmbient_le _) q.2.2.2.2,PUnit.unit))
    (by simpa only [rootProduct,coe_one,coe_inclusion,one_mul,mul_one,mul_assoc] using he)
  refine Prod.ext (Subtype.ext (congrArg (fun z => (z.2.2.1 : X ⧸ Q.D)) hh))
    (Prod.ext (congrArg (fun z => z.2.2.2.1) hh)
      (Prod.ext (Subtype.ext (congrArg (fun z => (z.2.2.2.2.1 : X ⧸ Q.D)) hh))
        (Prod.ext (congrArg (fun z => z.2.2.2.2.2.1) hh)
          (Subtype.ext (congrArg (fun z => (z.2.2.2.2.2.2.1 : X ⧸ Q.D)) hh)))))

private theorem factor_le (k : Fin 5) : fiveDerivedFactor Q split k ≤ fiveDerivedSubgroup Q split := by
  fin_cases k <;> dsimp only [fiveDerivedSubgroup]
  · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

/-- Multiplication of the five factors into their actual join. -/
def fiveDerivedProduct (p : FiveDerivedTuple Q split) : fiveDerivedSubgroup Q split :=
  ⟨(p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2.1*p.2.2.2.2,
    by exact mul_mem (mul_mem (mul_mem (mul_mem (factor_le Q split 0 p.1.property)
      (factor_le Q split 1 p.2.1.property)) (factor_le Q split 2 p.2.2.1.property))
      (factor_le Q split 3 p.2.2.2.1.property)) (factor_le Q split 4 p.2.2.2.2.property)⟩

include ν hC μ hB hn in
/-- The five-factor product has unique coordinates on the marked source quotient. -/
theorem source_five_derived_bijective
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    Function.Bijective (fiveDerivedProduct Q split) := by
  refine ⟨fun p q h => five_product_injective Q split hm (congrArg Subtype.val h),?_⟩
  intro x
  have hx := x.property
  change (x : X ⧸ Q.D) ∈ (fiveDerivedSubgroup Q split : Set (X ⧸ Q.D)) at hx
  rw [(source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).2] at hx
  obtain ⟨_,⟨_,⟨_,⟨a,ha,b,hb,rfl⟩,c,hc',rfl⟩,d,hd,rfl⟩,e,he,hx⟩ := hx
  exact ⟨(⟨a,ha⟩,⟨b,hb⟩,⟨c,hc'⟩,⟨d,hd⟩,⟨e,he⟩),Subtype.ext hx⟩

include ν hC μ hB hn in
/-- The actual direct-product equivalence underlying (6H)(f)'s five factors. -/
def fiveDerivedEquiv
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    FiveDerivedTuple Q split ≃* fiveDerivedSubgroup Q split := by
  let : IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  let j (k : Fin 5) : fiveDerivedFactor Q split k →* fiveDerivedSubgroup Q split :=
    inclusion (by exact factor_le Q split k)
  let f : FiveDerivedTuple Q split →* fiveDerivedSubgroup Q split :=
    (j 0).coprod ((j 1).coprod ((j 2).coprod ((j 3).coprod (j 4))))
  have he : (f : FiveDerivedTuple Q split → fiveDerivedSubgroup Q split) = fiveDerivedProduct Q split := by
    funext p
    apply Subtype.ext
    simp only [f,j,MonoidHom.coprod_apply,coe_mul,coe_inclusion,fiveDerivedProduct,mul_assoc]
  exact MulEquiv.ofBijective f (he.symm ▸ source_five_derived_bijective Q split n hn m ν T hC μ hB hm hcore hc)

@[simp] theorem fiveDerivedEquiv_apply
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (p : FiveDerivedTuple Q split) :
    (fiveDerivedEquiv Q split n hn m ν T hC μ hB hm hcore hc p : X ⧸ Q.D) =
      (p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2.1*p.2.2.2.2 := by
  simp only [fiveDerivedEquiv,MulEquiv.ofBijective_apply,MonoidHom.coprod_apply,coe_mul,coe_inclusion,mul_assoc]


include μ hB in
private theorem omega_card (w : Weyl Q) :
    Nat.card (omegaOneAmbient (rootAt Q split 1 w)) = 2^(2*m+1) := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]
  exact suzukiOmega_card Q split 1 m μ hB

include ν hC μ hB hn in
/-- The five-factor subgroup has the exact source order q⁵, including q=2. -/
theorem source_five_derived_card
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    Nat.card (fiveDerivedSubgroup Q split) = (2^(2*m+1))^5 := by
  have hlin (w : Weyl Q) : Nat.card (rootAt Q split 0 w) = 2^(2*m+1) := by
    rw [linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore]
  have hf (k : Fin 5) : Nat.card (fiveDerivedFactor Q split k) = 2^(2*m+1) := by
    fin_cases k
    · exact omega_card Q split m μ hB _
    · exact hlin _
    · exact omega_card Q split m μ hB _
    · exact hlin _
    · exact omega_card Q split m μ hB _
  rw [←Nat.card_congr (fiveDerivedEquiv Q split n hn m ν T hC μ hB hm hcore hc).toEquiv]
  change Nat.card (fiveDerivedFactor Q split 0 × fiveDerivedFactor Q split 1 ×
    fiveDerivedFactor Q split 2 × fiveDerivedFactor Q split 3 × fiveDerivedFactor Q split 4) = _
  simp only [Nat.card_prod,hf]
  ring

include ν hC μ hB hn in
/-- The elementary abelian five-factor subgroup lies in the actual derived radical. -/
theorem source_five_derived_le
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    fiveDerivedSubgroup Q split ≤ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  have h := factor_le_derived Q split n hn m ν T hC μ hB hm hcore hc
  exact sup_le (sup_le (sup_le (sup_le (h 0) (h 1)) (h 2)) (h 3)) (h 4)

include ν hC μ hB hn in
/-- Its intersection with the full perpendicular root is exactly that root's Omega. -/
theorem source_five_derived_inf_perpendicular
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    fiveDerivedSubgroup Q split ⊓ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let : IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  apply le_antisymm
  · intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx.2
      (elemPow_eq_one_of_isElementaryAbelian x hx.1)
  · exact le_inf (factor_le Q split 2) (omegaOneAmbient_le _)

include ν hC μ hB in
/-- The full perpendicular Suzuki root centralizes each of the five factors. -/
theorem source_five_derived_centralizes_perpendicular
    (hm : rotationOrder Q = 8) :
    fiveDerivedSubgroup Q split ≤
      centralizer (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) := by
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let F := rootAt Q split 0 (Q.simple 1*Q.simple 0)
  let G := rootAt Q split 1 (Q.simple 0)
  have hCE : ⁅omegaOneAmbient C,E⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2
    rw [right_comm,right_bot,right_omega,right_simple,right_rep] at hh
    have ht : rootAt Q split 1 ((Q.simple 0*Q.simple 1)*(Q.simple 0*Q.simple 1)) = E := by
      rw [←mul_assoc,←right_rep]
      exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    rwa [ht] at hh
  have hGE : ⁅omegaOneAmbient G,E⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0) : X ⧸ Q.D))
      (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2
    simpa only [right_comm,right_bot,right_omega,right_simple,right_rep] using hh
  have hDE : ⁅D,E⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC))
    rw [right_comm,right_bot,right_simple,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).1] at hh
    exact (commutator_comm _ _).trans hh
  have hFE : ⁅F,E⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 1) : X ⧸ Q.D)) hDE
    have ht : rightConjugate E (representative (Q.simple 1) : X ⧸ Q.D) = E :=
      perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    simpa only [right_comm,right_bot,ht,D,F,right_rep,mul_assoc,ssq,mul_one] using hh
  have hEE : ⁅omegaOneAmbient E,E⁆ = ⊥ := by
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (commutator_eq_bot_iff_le_centralizer.mpr (suzukiOmega_centralizes Q split 1 m μ hB))
    simpa only [right_comm,right_bot,right_omega,right_simple] using hh
  exact sup_le (sup_le (sup_le (sup_le
    (commutator_eq_bot_iff_le_centralizer.mp hCE)
    (commutator_eq_bot_iff_le_centralizer.mp hDE))
    (commutator_eq_bot_iff_le_centralizer.mp hEE))
    (commutator_eq_bot_iff_le_centralizer.mp hFE))
    (commutator_eq_bot_iff_le_centralizer.mp hGE)


include ν hC μ hB hn in
/-- Adjoining the full perpendicular root gives a subgroup of exact order q⁶. -/
theorem source_perpendicular_five_join_card
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    Nat.card (fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) :
      Subgroup (X ⧸ Q.D)) = (2^(2*m+1))^6 := by
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hnorm : E ≤ normalizer (fiveDerivedSubgroup Q split : Set (X ⧸ Q.D)) :=
    (le_centralizer_iff.mp (source_five_derived_centralizes_perpendicular Q split n m ν T hC μ hB hm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes (fiveDerivedSubgroup Q split) E hnorm
  have hE : Nat.card E = (2^(2*m+1))^2 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = _
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]
  rw [source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc,hE,
    source_five_derived_inf_perpendicular Q split n hn m ν T hC μ hB hm hcore hc,
    omega_card Q split m μ hB] at h
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(2*m+1))
  exact h.symm.trans (by ring)

include ν hC μ hB hn in
/-- In the enlarged subgroup, all involutions lie in exactly the five-factor subgroup. -/
theorem source_perpendicular_five_join_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    omegaOneAmbient (fiveDerivedSubgroup Q split ⊔
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) = fiveDerivedSubgroup Q split := by
  let J := fiveDerivedSubgroup Q split
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let : IsElementaryAbelian 2 J :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  have hcent : J ≤ centralizer (E : Set (X ⧸ Q.D)) :=
    source_five_derived_centralizes_perpendicular Q split n m ν T hC μ hB hm
  have hprod : (↑(J ⊔ E) : Set (X ⧸ Q.D)) = (J : Set (X ⧸ Q.D)) * E :=
    coe_mul_of_left_le_normalizer_right J E (hcent.trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    change x ∈ (↑(J ⊔ E) : Set (X ⧸ Q.D)) at hx
    rw [hprod] at hx
    obtain ⟨j,hj,e,he,rfl⟩ := hx
    have hje : Commute j e := (mem_centralizer_iff.mp (hcent hj) e he).symm
    have he2 : e^2 = 1 := by
      simpa only [hje.mul_pow,elemPow_eq_one_of_isElementaryAbelian j hj,one_mul] using hx2
    exact mul_mem hj (factor_le Q split 2 ((omegaOneAmbient_le_iff E _).mp le_rfl e he he2))
  · intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x (show x ∈ J ⊔ E from (show J ≤ J ⊔ E from le_sup_left) hx)
      (elemPow_eq_one_of_isElementaryAbelian x hx)

include ν hC μ hB hn in
/-- The source order bounds leave at most one additional q-sized layer beyond the five factors. -/
theorem source_radical_derived_card_bounds
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (2^(2*m+1))^5 ≤ Nat.card (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ : Subgroup (X ⧸ Q.D)) ∧
      Nat.card (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ : Subgroup (X ⧸ Q.D)) ≤ (2^(2*m+1))^6 := by
  constructor
  · rw [←source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc]
    exact Nat.card_le_card_of_injective (inclusion (source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc))
      (inclusion_injective _)
  · rw [source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc,
      card_map_of_injective (simpleRemainder Q split 1).subtype_injective]
    have hh := suzuki_radical_frattini_card_le Q split 1 0 m μ hB
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB) hc hm (by decide)
    have hcard : Nat.card (simpleRoot Q split 0) = 2^(2*m+1) := by
      rw [←rootAt_one Q split 0,linear_rootAt_card Q split 0 n ν T hC hn.pos,
        ree_common_field_exponent Q split hm n hn m ν T hC μ hB
          (UnitarySource.actorReflection Q split) hcore]
    rw [hcard] at hh
    exact hh.trans_eq (by ring)

include ν hC μ hB hn in
/-- The precise structural alternative used in the p.55 exclusion argument.
This is a consequence of the hypothetical whole-root containment, not its exclusion. -/
theorem source_perpendicular_in_derived_case
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆) :
    ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ =
        fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ∧
      omegaOneAmbient ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ =
        fiveDerivedSubgroup Q split := by
  have he : fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
    apply eq_of_le_of_card_ge (sup_le (source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc) hE)
    rw [source_perpendicular_five_join_card Q split n hn m ν T hC μ hB hm hcore hc]
    exact (source_radical_derived_card_bounds Q split n hn m ν T hC μ hB hm hcore hc).2
  refine ⟨he.symm,?_⟩
  rw [←he]
  exact source_perpendicular_five_join_omega Q split n hn m ν T hC μ hB hm hcore hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
