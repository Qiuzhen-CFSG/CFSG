module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedInvolutions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedFrattini
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Excluding the whole perpendicular root from the derived radical

Write V=U_s₂, E=U₂^(s₁s₂s₁), and J for the five elementary factors.
If E≤[V,V], the proved enlarged-product calculation gives [V,V]=JE and
Omega([V,V])=J. Hence the whole parabolic normalizes J. Ordered-root
uniqueness and this invariance put the two remaining mixed commutators
in J. The Cartan-adjusted involutions from DerivedInvolutions also put
the outer linear commutator in J. Every pair of the seven roots generating
V therefore commutes modulo J, with normality used only inside V.
It follows that [V,V]≤J, contradicting |JE|=q⁶ and |J|=q⁵.

The exact intersection [V,V]∩E=Omega(E) follows from the literal Suzuki
root action and its invariant-subgroup alternative. No positive-parameter
restriction is used; m=0 is retained. The original natural panel markings,
odd linear degree, faithful Borel and local characteristic-two hypothesis
remain the earlier inputs. The five-factor equality and full center
identities remain later steps, followed by source recognition.

OriginalDerivedInvolutions and Section10DerivedInvolutions apply both
conclusions to the original two-core, literal Q.q and all N-conjugates.
Source: Fong--Seitz I (1973), proof of (6H)(f), printed p.55.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
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

private theorem radical_seven (hm : rotationOrder Q = 8) :
    rootIntersection split (longest Q) (alternatingWord Q false 7)⁻¹ =
      simpleRemainder Q split 1 := by
  have hw : longest Q = Q.simple 1*alternatingWord Q false 7 := by
    have hh := (alternatingWord_longest Q true).symm
    rw [hm] at hh
    exact hh
  change split.U ⊓ unipotentConjugate split (longest Q*(alternatingWord Q false 7)⁻¹) = _
  rw [hw,mul_inv_cancel_right]
  rfl

private theorem radical_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split false 7 =
      [simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),rootAt Q split 0 (Q.simple 1)] := by
  have h0 := perpendicular_root_stable Q split hm 0 1 (by decide)
    (representative (Q.simple 0)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm 1 0 (by decide)
    (representative (Q.simple 1)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) h1
  have h6 := congrArg (fun A => rightConjugate A (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D)) h0
  simp only [right_rep,mul_assoc,ssq,mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    List.map_cons,List.map_nil,right_simple,right_rep]
  rw [h0,h5,h6]
  simp only [mul_assoc,ssq,mul_one]


private theorem factor_le (k : Fin 5) : fiveDerivedFactor Q split k ≤ fiveDerivedSubgroup Q split := by
  fin_cases k <;> dsimp only [fiveDerivedSubgroup]
  · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

include ν hC μ hB hn in
private theorem five_normalized
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆) :
    normalizer (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) ≤
      normalizer (fiveDerivedSubgroup Q split : Set (X ⧸ Q.D)) := by
  intro r hr
  rw [←(source_perpendicular_in_derived_case Q split n hn m ν T hC μ hB hm hcore hc hE).2,
    mem_normalizer_iff_map_conj_eq,map_omegaOneAmbient_injective _ (MulEquiv.injective _),
    map_commutator,mem_normalizer_iff_map_conj_eq.mp hr]

include ν hC μ hB hn in
private theorem far_mixed_le_five
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆) :
    ⁅rootAt Q split 1 (Q.simple 0),rootAt Q split 0 (Q.simple 1)⁆ ≤ fiveDerivedSubgroup Q split := by
  let J := fiveDerivedSubgroup Q split
  let A := simpleRoot Q split 1
  let F := rootAt Q split 0 (Q.simple 1*Q.simple 0)
  have hAN : A ≤ normalizer (J : Set (X ⧸ Q.D)) := by
    apply le_trans _ (five_normalized Q split n hn m ν T hC μ hB hm hcore hc hE)
    intro a ha
    exact remainder_parabolic_normalizes Q split 1 (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
      (rankOne_le_parabolic Q split 1 (show a ∈ rankOne Q split 1 from (show A ≤ rankOne Q split 1 from le_sup_left) ha))
  have hAFJ : ⁅A,F⁆ ≤ J := (commutator_mono le_rfl (factor_le Q split 3)).trans
    (le_normalizer_iff_commutator_le_right.mp hAN)
  let f := (MulAut.conj (representative (Q.simple 0) : X ⧸ Q.D)).symm
  have hmap (R : Subgroup (X ⧸ Q.D)) : R.map f.toMonoidHom =
      rightConjugate R (representative (Q.simple 0) : X ⧸ Q.D) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hrot : ⁅A,F⁆.map f.toMonoidHom =
      ⁅rootAt Q split 1 (Q.simple 0),rootAt Q split 0 (Q.simple 1)⁆ := by
    rw [hmap,right_comm,right_simple,right_rep]
    simp only [mul_assoc,ssq,mul_one]
  rw [←hrot]
  rintro z ⟨a,ha,rfl⟩
  have haJ := hAFJ ha
  have hprod := (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).2
  have hap : a ∈ (fiveDerivedFactor Q split 0 : Set (X ⧸ Q.D))*fiveDerivedFactor Q split 1*
      fiveDerivedFactor Q split 2*fiveDerivedFactor Q split 3*fiveDerivedFactor Q split 4 := by
    rw [←hprod]; exact haJ
  obtain ⟨_,⟨_,⟨_,⟨c,hc',d,hd,rfl⟩,e,he,rfl⟩,t,ht,rfl⟩,g,hg,hap⟩ := hap
  obtain ⟨_,⟨_,⟨b,hb,c',hc'',rfl⟩,d',hd',rfl⟩,e',he',hape⟩ :=
    distance_five_commutator_support Q split hm 1 0 (by decide)
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
      (marked_linear_remainder_le_kernel Q split 0 ν T hC) a ha
  have hi : Function.Injective (rootProduct (orderedRoots Q split true 7)) := by
    intro p q heq
    apply (orderedCoordinates Q split true 7 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using heq
  rw [seven_list Q split hm] at hi
  have heq := hi
    (a₁ := (1,1,⟨c,omegaOneAmbient_le _ hc'⟩,⟨d,hd⟩,⟨e,omegaOneAmbient_le _ he⟩,
      ⟨t,ht⟩,⟨g,omegaOneAmbient_le _ hg⟩,PUnit.unit))
    (a₂ := (1,⟨b,hb⟩,⟨c',hc''⟩,⟨d',hd'⟩,⟨e',he'⟩,1,1,PUnit.unit))
    (by simpa only [rootProduct,coe_one,one_mul,mul_one,mul_assoc] using hap.trans hape.symm)
  have ht1 : t = 1 := congrArg (fun p => (p.2.2.2.2.2.1 : X ⧸ Q.D)) heq
  have hg1 : g = 1 := congrArg (fun p => (p.2.2.2.2.2.2.1 : X ⧸ Q.D)) heq
  simp only [ht1,hg1,mul_one] at hap
  have hfC : (fiveDerivedFactor Q split 0).map f.toMonoidHom = fiveDerivedFactor Q split 2 := by
    rw [hmap]
    change rightConjugate (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1))) _ = _
    rw [right_omega,right_rep]; rfl
  have hfD : (fiveDerivedFactor Q split 1).map f.toMonoidHom = fiveDerivedFactor Q split 1 := by
    rw [hmap]
    exact perpendicular_root_stable Q split hm 0 1 (by decide) _ (representative_spec _)
  have hfE : (fiveDerivedFactor Q split 2).map f.toMonoidHom = fiveDerivedFactor Q split 0 := by
    rw [hmap]
    change rightConjugate (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) _ = _
    rw [right_omega,right_rep]
    simp only [mul_assoc,ssq,mul_one]; rfl
  rw [←hap,map_mul,map_mul]
  exact mul_mem (mul_mem (factor_le Q split 2 (hfC ▸ mem_map_of_mem f.toMonoidHom hc'))
    (factor_le Q split 1 (hfD ▸ mem_map_of_mem f.toMonoidHom hd)))
    (factor_le Q split 0 (hfE ▸ mem_map_of_mem f.toMonoidHom he))


include μ hB in
private theorem suzuki_self_le_omega (w : Weyl Q) :
    ⁅rootAt Q split 1 w,rootAt Q split 1 w⁆ ≤ omegaOneAmbient (rootAt Q split 1 w) := by
  let A := simpleRoot Q split 1
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split 1)⟩
  have h : ⁅A,A⁆ ≤ omegaOneAmbient A := by
    rw [←map_subtype_commutator,←suzuki_frattini_image Q split 1 m μ hB]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  let f := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have hr := map_mono (f := f.toMonoidHom) h
  rw [map_commutator,map_omegaOneAmbient_injective f.toMonoidHom f.injective] at hr
  simpa only [f,A,rootAt,rightConjugate,comap_equiv_eq_map_symm'] using hr

include ν hC μ hB hn in
/-- The whole perpendicular Suzuki root is not contained in the derived
radical: the source involution argument excludes the enlarged JE case. -/
theorem source_perpendicular_not_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ¬ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  intro hE
  let V := simpleRemainder Q split 1
  let J := fiveDerivedSubgroup Q split
  let H := simpleRoot Q split 0
  let G := rootAt Q split 1 (Q.simple 0)
  let F := rootAt Q split 0 (Q.simple 1*Q.simple 0)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let B := rootAt Q split 0 (Q.simple 1)
  let R : Fin 7 → Subgroup (X ⧸ Q.D) := ![H,G,F,E,D,C,B]
  have hRlist : ∀ k : Fin 7, R k ∈ orderedRoots Q split false 7 := by
    rw [radical_list Q split hm]
    intro k
    fin_cases k <;> simp [R,H,G,F,E,D,C,B]
  have hRV (k : Fin 7) : R k ≤ V := by
    change R k ≤ simpleRemainder Q split 1
    rw [←radical_seven Q split hm]
    exact orderedRoots_le Q split false 7 (by omega) _ (hRlist k)
  have hV : V = ⨆ k : Fin 7, R k := by
    apply le_antisymm _ (iSup_le hRV)
    intro v hv
    obtain ⟨p,hp⟩ := (orderedCoordinates Q split false 7 (by omega)).surjective
      ⟨v,by rw [radical_seven Q split hm]; exact hv⟩
    have hh : ∀ A ∈ orderedRoots Q split false 7, A ≤ ⨆ k : Fin 7, R k := by
      rw [radical_list Q split hm]
      intro A hA
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact le_iSup R 0
      · exact le_iSup R 1
      · exact le_iSup R 2
      · exact le_iSup R 3
      · exact le_iSup R 4
      · exact le_iSup R 5
      · exact le_iSup R 6
    have hmemb := rootProduct_mem _ _ hh p
    have heq := (orderedCoordinates_apply Q split false 7 (by omega) p).symm.trans (congrArg Subtype.val hp)
    change rootProduct (orderedRoots Q split false 7) p = v at heq
    rwa [heq] at hmemb
  have hVN : V ≤ normalizer (J : Set (X ⧸ Q.D)) :=
    V.le_normalizer.trans (five_normalized Q split n hn m ν T hC μ hB hm hcore hc hE)
  have hsmall {A B : Subgroup (X ⧸ Q.D)} (hAJ : A ≤ J) (hBV : B ≤ V) : ⁅A,B⁆ ≤ J := by
    rw [commutator_comm]
    exact (commutator_mono hBV hAJ).trans (le_normalizer_iff_commutator_le_right.mp hVN)
  have hHself : ⁅H,H⁆ ≤ J := by
    have hh : IsElementaryAbelian 2 H := by
      change IsElementaryAbelian 2 (simpleRoot Q split 0)
      rw [←rootAt_one Q split 0]
      exact linear_rootAt_elementary Q split 0 n ν T hC 1
    exact (commutator_self_eq_bot_iff.mpr hh.toIsMulCommutative).le.trans bot_le
  have hBself : ⁅B,B⁆ ≤ J := by
    let : IsElementaryAbelian 2 B := linear_rootAt_elementary Q split 0 n ν T hC _
    exact (commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le
  have hGself : ⁅G,G⁆ ≤ J := (suzuki_self_le_omega Q split m μ hB _).trans (factor_le Q split 4)
  have hCself : ⁅C,C⁆ ≤ J := (suzuki_self_le_omega Q split m μ hB _).trans (factor_le Q split 0)
  have hEself : ⁅E,E⁆ ≤ J := (suzuki_self_le_omega Q split m μ hB _).trans (factor_le Q split 2)
  have hHG : ⁅H,G⁆ ≤ J := (adjacent_commutator_eq_bot Q split hm 0 1 (by decide)
    (marked_linear_remainder_le_kernel Q split 0 ν T hC)
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)).le.trans bot_le
  have hCB : ⁅C,B⁆ ≤ J := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 0 1 (by decide)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB))
    rw [right_comm,right_bot,right_simple,right_rep] at hh
    exact (commutator_comm _ _).trans_le (hh.le.trans bot_le)
  have hGE : ⁅G,E⁆ ≤ J := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D))
      (source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc)
    rw [right_comm,right_simple,right_rep,right_rep] at hh
    exact hh.le.trans (factor_le Q split 3)
  have hCE : ⁅C,E⁆ ≤ J := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
      (show ⁅G,E⁆ = F from by
        have ht := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D))
          (source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc)
        simpa only [right_comm,right_simple,right_rep] using ht)
    rw [right_comm,right_rep,perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _),right_rep] at hh
    exact hh.le.trans (factor_le Q split 1)
  have hGC : ⁅G,C⁆ ≤ J := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)
    simp only [right_comm,right_bot,right_simple,right_rep,mul_assoc,
      ←mul_assoc (Q.simple 0) (Q.simple 0),ssq,one_mul,mul_one] at hh
    exact (commutator_comm _ _).trans_le (hh.le.trans bot_le)
  have hEB : ⁅E,B⁆ = omegaOneAmbient C := by
    let w := Q.simple 0*Q.simple 1*Q.simple 0
    have hh := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D))
      (source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc)
    rw [right_comm,right_simple,right_omega,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.1,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.2] at hh
    exact hh
  have hEH : ⁅E,H⁆ ≤ J := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hEB
    rw [right_comm,right_omega,perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)] at hh
    simp only [B,C,right_rep,mul_assoc,ssq,mul_one,rootAt_one] at hh
    simpa only [E,H,J,mul_assoc] using hh.le.trans (factor_le Q split 4)
  have hEBJ : ⁅E,B⁆ ≤ J := hEB.le.trans (factor_le Q split 0)
  have hGB : ⁅G,B⁆ ≤ J := far_mixed_le_five Q split n hn m ν T hC μ hB hm hcore hc hE
  have hHC : ⁅H,C⁆ ≤ J := by
    let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
    have hsN : (s.val : X ⧸ Q.D) ∈ normalizer (J : Set (X ⧸ Q.D)) :=
      five_normalized Q split n hn m ν T hC μ hB hm hcore hc hE
        (remainder_parabolic_normalizes Q split 1 (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
          (rankOne_le_parabolic Q split 1 s.mem_rankOne))
    have hh := map_mono (f := (MulAut.conj (s.val : X ⧸ Q.D)).symm.toMonoidHom) hGB
    have hr (A : Subgroup (X ⧸ Q.D)) : A.map (MulAut.conj (s.val : X ⧸ Q.D)).symm.toMonoidHom =
        rightConjugate A (s.val : X ⧸ Q.D) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']
    rw [hr,hr,rightConjugate_eq_self J hsN] at hh
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator] at hh
    have hG : rightConjugate G (s.val : X ⧸ Q.D) = C := rootAt_right Q split 1 _ _ s.val s.class_eq
    have hB : rightConjugate B (s.val : X ⧸ Q.D) = H := by
      rw [rootAt_right Q split 0 _ _ s.val s.class_eq,ssq,rootAt_one]
    rw [hr,hr] at hh
    rw [hG,hB] at hh
    exact (commutator_comm _ _).trans_le hh
  have hHB : ⁅H,B⁆ ≤ J := source_far_linear_le_five_of_perpendicular_le_derived Q split n hn m ν T hC μ hB hm hcore hc hE
  have hpair (k l : Fin 7) : ⁅R k,R l⁆ ≤ J := by
    fin_cases k <;> fin_cases l
    · exact hHself
    · exact hHG
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 3) (hRV 0))
    · exact (commutator_comm _ _).trans_le hEH
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 1) (hRV 0))
    · exact hHC
    · exact hHB
    · exact (commutator_comm _ _).trans_le hHG
    · exact hGself
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 3) (hRV 1))
    · exact hGE
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 1) (hRV 1))
    · exact hGC
    · exact hGB
    · exact hsmall (factor_le Q split 3) (hRV 0)
    · exact hsmall (factor_le Q split 3) (hRV 1)
    · exact hsmall (factor_le Q split 3) (hRV 2)
    · exact hsmall (factor_le Q split 3) (hRV 3)
    · exact hsmall (factor_le Q split 3) (hRV 4)
    · exact hsmall (factor_le Q split 3) (hRV 5)
    · exact hsmall (factor_le Q split 3) (hRV 6)
    · exact hEH
    · exact (commutator_comm _ _).trans_le hGE
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 3) (hRV 3))
    · exact hEself
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 1) (hRV 3))
    · exact (commutator_comm _ _).trans_le hCE
    · exact hEBJ
    · exact hsmall (factor_le Q split 1) (hRV 0)
    · exact hsmall (factor_le Q split 1) (hRV 1)
    · exact hsmall (factor_le Q split 1) (hRV 2)
    · exact hsmall (factor_le Q split 1) (hRV 3)
    · exact hsmall (factor_le Q split 1) (hRV 4)
    · exact hsmall (factor_le Q split 1) (hRV 5)
    · exact hsmall (factor_le Q split 1) (hRV 6)
    · exact (commutator_comm _ _).trans_le hHC
    · exact (commutator_comm _ _).trans_le hGC
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 3) (hRV 5))
    · exact hCE
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 1) (hRV 5))
    · exact hCself
    · exact hCB
    · exact (commutator_comm _ _).trans_le hHB
    · exact (commutator_comm _ _).trans_le hGB
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 3) (hRV 6))
    · exact (commutator_comm _ _).trans_le hEBJ
    · exact (commutator_comm _ _).trans_le (hsmall (factor_le Q split 1) (hRV 6))
    · exact (commutator_comm _ _).trans_le hCB
    · exact hBself
  have hVV : ⁅V,V⁆ ≤ J := by
    rw [hV]
    apply commutator_iSup_le_of_relative_normal V _ J R hVN hRV
    intro k
    rw [commutator_comm]
    apply commutator_iSup_le_of_relative_normal V _ J R hVN hRV
    exact fun l => hpair l k
  have hJ := source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc
  have hbig := source_perpendicular_five_join_card Q split n hn m ν T hC μ hB hm hcore hc
  have heq : J ⊔ E = J := sup_eq_left.mpr (hE.trans hVV)
  change Nat.card (J ⊔ E : Subgroup (X ⧸ Q.D)) = _ at hbig
  rw [heq,hJ] at hbig
  have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
  exact (Nat.pow_lt_pow_right hq (by decide : 5 < 6)).ne hbig


include ν hC μ hB hn in
/-- The actual derived radical meets the perpendicular root in exactly its
Omega subgroup, with no near-zero or whole-root alternative left. -/
theorem source_derived_inf_perpendicular_eq_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ⊓
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hN : Q.tits.B ⊓ Q.tits.N ≤ normalizer
      ((⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split 1
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (Q.tits.B_le_standardParabolic _ hh.1))]
  apply le_antisymm
  · exact suzuki_rootAt_intersection_le_omega_of_not_le Q split 1 m μ hB _ _ hN
      (source_perpendicular_not_le_derived Q split n hn m ν T hC μ hB hm hcore hc)
  · exact le_inf ((factor_le Q split 2).trans
      (source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc)) (omegaOneAmbient_le _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
