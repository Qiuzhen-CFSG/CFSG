module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule

/-!
# The regular element and moving normalizer in MS93 (3.7)(6)

For an order-q-squared subgroup of the plane radical, select an invertible
symmetric shear whose centralizer in the determinant-one plane group fails
to normalize that subgroup. If the subgroup contains a nonzero alternating
shear, its centralizer is the whole plane-local group; the classification
of invariant radical subgroups gives the contradiction. Otherwise diagonal
projection is bijective. After a special-linear change of coordinates, upper
unipotents fixing the selected shear would produce a nonzero alternating
shear in the subgroup, again a contradiction. This works for additive
subgroups without assuming linearity over the larger field.

The source application constructs the plane cover from the original
saturated distance-two hypotheses. The midpoint index proves that the same
critical image has order q squared. Lift the selection through the original
onto endpoint quotient, with its entire core as kernel. The cover's fixed
lifting and the full central midpoint supplement give C_Z(x) = Z_t for this
same x. The selected conjugator normalizes the common radical and x Q_a,
but moves Z_z Q_a. No non-normalization premise is retained.

This supplies the two initial selections on printed p.876. The induced
midpoint automorphism, the ensuing critical-pair contradiction, and the
field-four endgame remain subsequent source obligations.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(6), printed p.876. The symmetric-matrix calculation uses the
existing Plane extension, central quotient and invariant-subgroup theorems.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymplecticFour
open Plane
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def sym (a b c : F) : symmetricMatrices F :=
  ⟨!![a,b;b,c],by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
private def upper (s : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,s;0,1],by simp⟩
private def congruenceEquiv (g : SpecialLinearGroup (Fin 2) F) :
    symmetricMatrices F ≃+ symmetricMatrices F :=
  { toFun := congruence g
    invFun := congruence g⁻¹
    left_inv := by
      intro B
      apply Subtype.ext
      change g⁻¹.val * (g.val * B.val * g.valᵀ) * g⁻¹.valᵀ = B.val
      have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
      calc
        _ = (g⁻¹.val*g.val)*B.val*(g⁻¹.val*g.val)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hi]; simp
    right_inv := by
      intro B
      apply Subtype.ext
      change g.val * (g⁻¹.val * B.val * g⁻¹.valᵀ) * g.valᵀ = B.val
      have hi : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
      calc
        _ = (g.val*g⁻¹.val)*B.val*(g.val*g⁻¹.val)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hi]; simp
    map_add' := by
      intro B C
      apply Subtype.ext
      exact by simp [congruence, Matrix.mul_add, Matrix.add_mul] }

omit [Finite F] in
private theorem upper_diff (s : F) (B : symmetricMatrices F) :
    congruence (upper s) B - B = sym (s*s*B.val 1 1) (s*B.val 1 1) 0 := by
  let a : F := B.val 0 0
  let b : F := B.val 0 1
  let c : F := B.val 1 1
  have hB : B=sym a b c := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 1) B.property
    · rfl
  change congruence (upper s) B - B = sym (s*s*c) (s*c) 0
  rw [hB]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [congruence,upper,sym,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
      CharTwo.sub_eq_add] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem no_upper_invariant_complement
    (A : AddSubgroup (symmetricMatrices F)) (hF : 2 < Nat.card F)
    (hsurj : ∀ c : F, ∃ B ∈ A, B.val 1 1=c)
    (hinj : ∀ B ∈ A, (∀ i, B.val i i=0) → B=0)
    (hnorm : ∀ s : F, ∀ B ∈ A, congruence (upper s) B ∈ A) : False := by
  obtain ⟨t,ht0,ht1⟩ : ∃ t : F, t≠0 ∧ t≠1 := by
    apply ENat.exists_ne_ne_of_three_le
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast (show 3 ≤ Nat.card F by omega)
  obtain ⟨B,hB,hBc⟩ := hsurj 1
  obtain ⟨C,hC,hCc⟩ := hsurj (t*t)
  have hD := A.sub_mem (A.sub_mem (hnorm t B hB) hB) (A.sub_mem (hnorm 1 C hC) hC)
  rw [upper_diff,upper_diff,hBc,hCc] at hD
  have he : sym (t*t*1) (t*1) 0 - sym (1*1*(t*t)) (1*(t*t)) 0 = sym 0 (t-t*t) 0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym]
  rw [he] at hD
  have hz := hinj _ hD (by intro i; fin_cases i <;> rfl)
  have hz' : t-t*t=0 := congrArg (fun B : symmetricMatrices F => B.val 0 1) hz
  have ht : t*(1-t) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1))
  exact ht (by linear_combination hz')


omit [Finite F] [CharP F 2] in
private theorem congruence_mul (g k : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) : congruence (g*k) B=congruence g (congruence k B) := by
  apply Subtype.ext
  change (g.val*k.val)*B.val*(g.val*k.val)ᵀ=g.val*(k.val*B.val*k.valᵀ)*g.valᵀ
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

omit [Finite F] in
private theorem diagonal_zero_congruence (g : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) (hB : ∀ i, B.val i i=0) :
    ∀ i, (congruence g B).val i i=0 := by
  intro i
  rw [congruence_diagonal,hB,hB]
  simp

omit [CharP F 2] in
private theorem diagonal_surjective
    (A : AddSubgroup (symmetricMatrices F)) (hc : Nat.card F^2 ≤ Nat.card A)
    (hinj : ∀ B ∈ A, (∀ i, B.val i i=0) → B=0) :
    ∀ v : Fin 2 → F, ∃ B ∈ A, ∀ i, B.val i i=v i := by
  let f : A →+ (Fin 2 → F) :=
    { toFun := fun B i => B.val.val i i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    apply (AddMonoidHom.ker_eq_bot_iff f).mp
    apply _root_.eq_bot_iff.mpr
    intro B hB
    apply Subtype.ext
    exact hinj B.val B.property (congrFun hB)
  have hf' := (hf.bijective_of_nat_card_le (by simpa [Nat.card_fun] using hc)).2
  intro v
  obtain ⟨B,hB⟩ := hf' v
  exact ⟨B.val,B.property,congrFun hB⟩

private theorem complement_normalizer_escape
    (A : AddSubgroup (symmetricMatrices F)) (hF : 2 < Nat.card F)
    (hc : Nat.card F^2 ≤ Nat.card A)
    (hinj : ∀ B ∈ A, (∀ i, B.val i i=0) → B=0)
    (B : symmetricMatrices F) (hB : B ∈ A) (hB0 : B≠0) :
    ∃ g : SpecialLinearGroup (Fin 2) F, congruence g B=B ∧
      ∃ C ∈ A, congruence g C ∉ A := by
  have hv : untwistedDiagonal B ≠ 0 := by
    intro hv
    apply hB0
    apply hinj B hB
    intro i
    have hi := congrFun hv i
    change (frobeniusEquiv F 2).symm (B.val i i)=0 at hi
    exact (map_eq_zero_iff _ (frobeniusEquiv F 2).symm.injective).mp hi
  obtain ⟨k,hk⟩ := natural_transitive hv (show (Pi.single 0 (1 : F) : Fin 2 → F)≠0 by
    intro hh; have hi := congrFun hh 0; simp at hi)
  let A' := A.map (congruenceEquiv k).toAddMonoidHom
  have hi' : ∀ C ∈ A', (∀ i, C.val i i=0) → C=0 := by
    rintro _ ⟨C,hC,rfl⟩ hdiag
    have hh := diagonal_zero_congruence k⁻¹ (congruence k C) hdiag
    change ∀ i, ((congruenceEquiv k).symm ((congruenceEquiv k) C)).val i i=0 at hh
    rw [AddEquiv.symm_apply_apply] at hh
    have hz := hinj C hC hh
    simp only [hz,map_zero]
  have hc' : Nat.card F^2 ≤ Nat.card A' := by
    rw [AddSubgroup.card_map_of_injective (congruenceEquiv k).injective]
    exact hc
  have hs : ∀ c : F, ∃ C ∈ A', C.val 1 1=c := by
    intro c
    obtain ⟨C,hC,hh⟩ := diagonal_surjective A' hc' hi' (fun _ => c)
    exact ⟨C,hC,hh 1⟩
  have hB11 : (congruence k B).val 1 1=0 := by
    have hi := congrFun ((untwistedDiagonal_congruence k B).trans hk) 1
    change (frobeniusEquiv F 2).symm ((congruence k B).val 1 1)=0 at hi
    exact (map_eq_zero_iff _ (frobeniusEquiv F 2).symm.injective).mp hi
  by_contra! hn
  apply no_upper_invariant_complement A' hF hs hi'
  intro s C hC
  obtain ⟨D,hD,rfl⟩ := hC
  let g := k⁻¹*upper s*k
  have hfix : congruence g B=B := by
    have hh := upper_diff s (congruence k B)
    rw [hB11,mul_zero,mul_zero] at hh
    have hz : sym (0:F) 0 0=0 := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hz,sub_eq_zero] at hh
    dsimp only [g]
    rw [congruence_mul,congruence_mul,hh]
    exact (congruenceEquiv k).symm_apply_apply B
  have hmem := hn g hfix D hD
  refine ⟨congruence g D,hmem,?_⟩
  change congruence k (congruence (k⁻¹*upper s*k) D)=congruence (upper s) (congruence k D)
  rw [←congruence_mul,←congruence_mul]
  congr 1
  group


private def shearHom : Multiplicative (symmetricMatrices F) →* planeLocal (F := F) :=
  radical.subtype.comp radicalEquiv.symm.toMonoidHom

omit [Finite F] [CharP F 2] in
private theorem shear_injective : Function.Injective (shear (F := F)) := by
  intro B C h
  apply Subtype.ext
  exact congrArg (fun q : planeLocal (F := F) => q.val.val.toBlocks₁₂) h

private def shearCoordinates (W : Subgroup (planeLocal (F := F))) :
    AddSubgroup (symmetricMatrices F) := (W.comap shearHom).toAddSubgroup'

omit [Finite F] [CharP F 2] in
private theorem shear_coordinates_card (W : Subgroup (planeLocal (F := F))) (hW : W ≤ radical) :
    Nat.card (shearCoordinates W)=Nat.card W := by
  let f : shearCoordinates W → W := fun B => ⟨shear B.val,B.property⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · intro B C hh
    apply Subtype.ext
    exact shear_injective (congrArg Subtype.val hh)
  · intro q
    let r : radical (F := F) := ⟨q.val,hW q.property⟩
    have he : shear (radicalEquiv r).toAdd=q.val :=
      congrArg Subtype.val (radicalEquiv.symm_apply_apply r)
    exact ⟨⟨(radicalEquiv r).toAdd,show shear (radicalEquiv r).toAdd ∈ W from he.symm ▸ q.property⟩,
      Subtype.ext he⟩

private theorem central_radical_card_bound (W : Subgroup (planeLocal (F := F)))
    (hW : W ≤ radical) (hcent : W ≤ center (planeLocal (F := F))) :
    Nat.card W ≤ Nat.card F := by
  rw [←shear_coordinates_card W hW]
  let A := shearCoordinates W
  have hz (B : A) (i : Fin 2) : B.val.val i i=0 := by
    exact (mem_center_subgroupOf_iff_diagonal_zero
      (radicalEquiv.symm (Multiplicative.ofAdd B.val))).mp (hcent B.property) i
  apply Nat.card_le_card_of_injective (fun B : A => B.val.val 0 1)
  intro B C he
  apply Subtype.ext
  apply Subtype.ext
  have hs (B : A) : B.val.val 1 0=B.val.val 0 1 :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 1) B.val.property
  ext i j
  fin_cases i <;> fin_cases j
  · rw [hz,hz]
  · exact he
  · exact (hs B).trans (he.trans (hs C).symm)
  · rw [hz,hz]

private theorem plane_normalizer_selection {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (W : Subgroup (planeLocal (F := F))) (hW : W ≤ radical)
    (hc : Nat.card W=Nat.card F^2) :
    ∃ B : symmetricMatrices F, shear B ∈ W ∧ B.val.det≠0 ∧
      ∃ g : planeLocal (F := F), g*shear B*g⁻¹=shear B ∧
        g ∉ normalizer (W : Set (planeLocal (F := F))) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn
  let A := shearCoordinates W
  have hAc : Nat.card A=Nat.card F^2 := (shear_coordinates_card W hW).trans hc
  by_cases hcentral : ∃ x ∈ W, x ∈ center (planeLocal (F := F)) ∧ x≠1
  · obtain ⟨x,hx,hxz,hx1⟩ := hcentral
    let r : radical (F := F) := ⟨x,hW hx⟩
    let B := (radicalEquiv r).toAdd
    have hB : shear B=x := congrArg Subtype.val (radicalEquiv.symm_apply_apply r)
    have hd := (mem_center_subgroupOf_iff_diagonal_zero r).mp hxz
    have h01 : B.val 0 1≠0 := by
      intro hh
      have hz : B=0 := by
        apply Subtype.ext
        have hs : B.val 1 0=B.val 0 1 :=
          congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 1) B.property
        ext i j
        fin_cases i <;> fin_cases j
        · exact hd 0
        · exact hh
        · exact hs.trans hh
        · exact hd 1
      apply hx1
      rw [←hB,hz,shear_zero]
    have hdet : B.val.det≠0 := by
      have hs : B.val 1 0=B.val 0 1 :=
        congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 1) B.property
      rw [Matrix.det_fin_two,hd 0,hd 1,zero_mul,zero_sub,hs]
      exact neg_ne_zero.mpr (mul_ne_zero h01 h01)
    have hex : ∃ g : planeLocal (F := F), g ∉ normalizer (W : Set (planeLocal (F := F))) := by
      by_contra! hall
      let : W.Normal := ⟨fun x hx g => (mem_normalizer_iff.mp (hall g) x).mp hx⟩
      rcases normal_radical_le_center_or_eq hF hn W hW with hz | hz
      · have hh := central_radical_card_bound W hW hz
        rw [hc] at hh
        nlinarith
      · have hrc : Nat.card (radical (F := F))=Nat.card F^3 := by
          have hh := SymplecticConjugatePair.card_planeRadical (F := F)
          change Nat.card (radical.map (planeLocal (F := F)).subtype)=_ at hh
          rwa [card_map_of_injective (planeLocal (F := F)).subtype_injective] at hh
        rw [hz,hrc] at hc
        nlinarith [sq_pos_of_pos (show 0<Nat.card F by omega)]
    obtain ⟨g,hg⟩ := hex
    refine ⟨B,hB.symm ▸ hx,hdet,g,?_,hg⟩
    rw [hB,(mem_center_iff.mp hxz) g,mul_assoc,mul_inv_cancel,mul_one]
  · have hi : ∀ B ∈ A, (∀ i, B.val i i=0) → B=0 := by
      intro B hB hd
      have hz : shear B ∈ center (planeLocal (F := F)) :=
        (mem_center_subgroupOf_iff_diagonal_zero
          (radicalEquiv.symm (Multiplicative.ofAdd B))).mpr hd
      have h1 : shear B=1 := by
        by_contra hh
        exact hcentral ⟨shear B,hB,hz,hh⟩
      apply shear_injective
      rw [h1,shear_zero]
    obtain ⟨B,hB,hdet⟩ := LargePlaneGeneration.exists_invertible_shear
      (W.map (planeLocal (F := F)).subtype) (map_mono hW)
      (by rw [card_map_of_injective (planeLocal (F := F)).subtype_injective,hc]; nlinarith)
    have hBW : shear B ∈ W := by
      obtain ⟨x,hx,he⟩ := hB
      have he' : x=shear B := Subtype.ext he
      exact he' ▸ hx
    have hB0 : B≠0 := by
      intro hz
      apply hdet
      rw [hz]
      exact Matrix.det_zero
    obtain ⟨g,hfix,C,hC,hescape⟩ := complement_normalizer_escape A hq hAc.ge hi B hBW hB0
    refine ⟨B,hBW,hdet,levi g,?_,?_⟩
    · rw [conjugate_shear,quotientMap_levi,hfix]
    · intro hnorm
      apply hescape
      have hm := (mem_normalizer_iff.mp hnorm (shear C)).mp hC
      rwa [conjugate_shear,quotientMap_levi] at hm


private theorem ambient_plane_selection {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (W : Subgroup (Sp F)) (hW : W ≤ planeRadicalAmbient)
    (hc : Nat.card W=Nat.card F^2) :
    ∃ B : symmetricMatrices F, shearSp B ∈ W ∧ B.val.det≠0 ∧
      ∃ g ∈ planeLocal (F := F), g*shearSp B*g⁻¹=shearSp B ∧
        g ∉ normalizer (W : Set (Sp F)) := by
  have hWL : W ≤ planeLocal := hW.trans (by rintro _ ⟨q,hq,rfl⟩; exact q.property)
  let W' := W.subgroupOf planeLocal
  have hW' : W' ≤ radical := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hW hx
    have he' : y=x := Subtype.ext he
    exact he' ▸ hy
  have hc' : Nat.card W'=Nat.card F^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv]
    exact hc
  obtain ⟨B,hB,hdet,g,hfix,hnorm⟩ := plane_normalizer_selection hF hn W' hW' hc'
  refine ⟨B,hB,hdet,g.val,g.property,congrArg Subtype.val hfix,?_⟩
  intro hg
  apply hnorm
  exact W.le_normalizer_comap planeLocal.subtype hg

omit [Finite F] [CharP F 2] in
private theorem shear_regular_fixed (B : symmetricMatrices F) (hB : B.val.det≠0)
    (v : Vector F) (hv : shearSp B • v=v) :
    ∀ u ∈ planeRadicalAmbient (F := F), u • v=v := by
  have hz : B.val *ᵥ (fun i => v (.inr i))=0 := by
    ext i
    have hi := congrFun hv (.inl i)
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,
      shearSp,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks] at hi ⊢ <;> linear_combination hi
  have hz' : (fun i => v (.inr i))=0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB)))
    rw [Matrix.mulVec_zero]
    exact hz
  intro u hu
  obtain ⟨C,rfl⟩ := (SymplecticConjugatePair.mem_planeRadical_iff u).mp hu
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,
      shearSp,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,show v (.inr 0)=0 from congrFun hz' 0,
      show v (.inr 1)=0 from congrFun hz' 1]

private theorem lifted_plane_selection {G : Type*} [Group G] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ψ : G →* Sp F) (hψ : Function.Surjective ψ)
    (T A : Subgroup G) (hk : ψ.ker ≤ T) (hAT : A ≤ T)
    (hT : T.map ψ=planeRadicalAmbient) (hc : Nat.card (A.map ψ)=Nat.card F^2) :
    ∃ x ∈ A, (∀ v : Vector F, ψ x • v=v → ∀ t ∈ T, ψ t • v=v) ∧
      ∃ y ∈ normalizer (T : Set G),
        x⁻¹*(y*x*y⁻¹) ∈ ψ.ker ∧ y ∉ normalizer ((A ⊔ ψ.ker : Subgroup G) : Set G) := by
  obtain ⟨B,⟨x,hx,hBx⟩,hdet,u,hu,hux,huN⟩ := ambient_plane_selection hF hn (A.map ψ)
    ((map_mono hAT).trans_eq hT) hc
  obtain ⟨y,rfl⟩ := hψ u
  have hyT : y ∈ normalizer (T : Set G) := by
    have hN : ψ y ∈ normalizer (planeRadicalAmbient (F := F) : Set (Sp F)) := by
      rw [planeRadicalAmbient_normalizer hF hn]
      exact planeLocal_le hu
    have hh : y ∈ (normalizer (T.map ψ : Set (Sp F))).comap ψ := hT.symm ▸ hN
    rwa [comap_normalizer_eq_of_surjective _ hψ,comap_map_eq_self hk] at hh
  refine ⟨x,hx,?_,y,hyT,?_,?_⟩
  · intro v hv t ht
    rw [hBx] at hv
    exact shear_regular_fixed B hdet v hv (ψ t) (hT ▸ mem_map_of_mem ψ ht)
  · change ψ (x⁻¹*(y*x*y⁻¹))=1
    simp only [map_mul,map_inv,hBx,hux,inv_mul_cancel]
  · intro hy
    apply huN
    have hh := (A ⊔ ψ.ker).le_normalizer_map ψ (mem_map_of_mem ψ hy)
    have he : (A ⊔ ψ.ker).map ψ=A.map ψ := by
      rw [Subgroup.map_sup,Subgroup.map_ker_self,sup_bot_eq]
    rwa [he] at hh


omit [Field F] [Finite F] [CharP F 2] in
private theorem coset_normalizer_of_conjugate {G : Type*} [Group G]
    (Q : Subgroup G) (x y : G) (hy : y ∈ normalizer (Q : Set G))
    (hxy : x⁻¹*(y*x*y⁻¹) ∈ Q) : y ∈ normalizer (x • (Q : Set G)) := by
  apply mem_set_normalizer_iff.mpr
  intro z
  rw [Set.mem_smul_set_iff_inv_smul_mem,Set.mem_smul_set_iff_inv_smul_mem]
  change x⁻¹*z ∈ Q ↔ x⁻¹*(y*z*y⁻¹) ∈ Q
  have he : x⁻¹*(y*z*y⁻¹)=(x⁻¹*(y*x*y⁻¹))*(y*(x⁻¹*z)*y⁻¹) := by group
  rw [he,Q.mul_mem_cancel_left hxy]
  exact mem_normalizer_iff.mp hy _

open Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology.SymplecticFour
private theorem regular_fixed_lift
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (U T : Subgroup G) (x : T)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := E))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hreg : ∀ v : Vector E, (β x).val • v=v → ∀ t : T, (β t).val • v=v) :
    U ⊓ centralizer ({x.val} : Set G)=U ⊓ centralizer (T : Set G) := by
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr x.property)))
  rintro u ⟨hu,hux⟩
  refine ⟨hu,?_⟩
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
  have hxw : σ (β x) w.toAdd=w.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact]
    change x.val*j w*x.val⁻¹=j w
    rw [(mem_centralizer_singleton_iff.mp hux).symm,mul_inv_cancel_right]
  have hxp : (β x).val • p w.toAdd=p w.toAdd := by
    change binaryNatural (β x) (p w.toAdd)=_
    rw [←p.isIntertwining,hxw]
  intro t ht
  have htw := cover_fixed_of_projection_fixed p hp (β ⟨t,ht⟩) w.toAdd
    (hreg (p w.toAdd) hxp ⟨t,ht⟩)
  have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) htw
  rw [hact,ofAdd_toAdd,mul_inv_eq_iff_eq_mul] at hh
  exact hh

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H : Type*} [Group H] [Finite H]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Source (6)'s regular element and moving conjugator, selected on the
same full endpoint quotient. No non-normalization premise is assumed. -/
theorem source_six_exists_moving_regular_element
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, y ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
        y ∈ normalizer (x • (Q d.radical a : Set (FreeAmalgam d.radical))) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let := replacementComponent_normal h d
  obtain ⟨⟨cv⟩,_,hai,hzi,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,⟨k,hk⟩⟩
  change Q d.radical t →* L (K := E.Carrier) at β
  change Sp E.Carrier at k
  change ∀ u : Q d.radical t, (e.groupEquiv.symm (β u) : _) = κ (inclusion hTS u) at hβmark
  change ∀ (u : Q d.radical t) (w : (replacementMovedSection h d).space.toSubmodule),
    j (Multiplicative.ofAdd (MovedSection.coverAction (replacementMovedSection h d) e (β u) w)) =
      u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ at hact
  change ((commutator (Sp E.Carrier)).subtype.comp β).range.map
    (MulAut.conj k).toMonoidHom=planeRadicalAmbient at hk
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let S := stabilizer d.radical a
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  let ψ := (MulAut.conj k).toMonoidHom.comp ((commutator (Sp E.Carrier)).subtype.comp γ)
  have hγ (u : Q d.radical t) : γ (inclusion hTS u)=β u := by
    apply e.groupEquiv.symm.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (e.groupEquiv.symm_apply_apply
      (κC (inclusion hTS u)))).trans (hβmark u).symm
  have hψt (u : Q d.radical t) : ψ (inclusion hTS u)=k*α u*k⁻¹ := by
    change k*(γ (inclusion hTS u)).val*k⁻¹=_
    rw [hγ]
    rfl
  have hκC_onto : Function.Surjective κC := by
    intro x
    obtain ⟨u,hu⟩ := hκ x.val
    exact ⟨u,Subtype.ext hu⟩
  have hγonto : Function.Surjective γ := e.groupEquiv.surjective.comp hκC_onto
  have hSponto : Function.Surjective (commutator (Sp E.Carrier)).subtype := by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    rw [LargeField.commutator_eq_top (by rw [hFc]; exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.nonbinary)]
    trivial
  have hψonto : Function.Surjective ψ :=
    (MulAut.conj k).surjective.comp (hSponto.comp hγonto)
  have hψker : ψ.ker=(Q d.radical a).subgroupOf S := by
    dsimp only [ψ,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj k).injective,
      MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      MonoidHom.ker_codRestrict,←hκQ,subgroupOf_map_subtype_eq]
  let T := (Q d.radical t).subgroupOf S
  let A := (Z d.radical z).subgroupOf S
  have hZzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)).trans (omegaCenter_le _)
  have hZzT := hZzQ.trans c'.core_le_edge
  have hZzS := hZzT.trans hTS
  have hTmap : T.map ψ=planeRadicalAmbient := by
    rw [←hk,←MonoidHom.range_comp]
    apply le_antisymm
    · rintro _ ⟨u,hu,rfl⟩
      exact ⟨⟨u.val,hu⟩,(hψt ⟨u.val,hu⟩).symm⟩
    · rintro _ ⟨u,rfl⟩
      exact ⟨inclusion hTS u,u.property,hψt u⟩
  have hreverse : (2^n)^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    by_contra hn
    have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
    let rev : CriticalPath d.radical g z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse d.radical g hedge a path.start_color
          (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)
          z path.end_color path.critical }
    have hh' := (replacement_critical_indices_eq_field_of_small h d rev (by omega) (lt_of_not_ge hn)).2
    rw [hh'] at hcritical
    nlinarith
  have hZtQa : Z d.radical t ≤ Q d.radical a :=
    (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)).trans (omegaCenter_le _))
  have hAc : Nat.card (A.map ψ)=Nat.card E.Carrier^2 := by
    rw [←relIndex_ker,hψker,relIndex_subgroupOf hZzS,hFc]
    apply le_antisymm ?_ hreverse
    exact (relIndex_le_of_le_left hZtQa (by rw [hzi]; positivity)).trans_eq hzi
  obtain ⟨x,hx,hreg,y,hyT,hcoset,hmove⟩ := lifted_plane_selection hFc h.nonbinary ψ hψonto T A
    (by rw [hψker]; exact subgroupOf_mono _ c.core_le_edge)
    (subgroupOf_mono _ hZzT) hTmap hAc
  have hyT' : y.val ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hh := T.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hyT)
    rwa [map_subgroupOf_eq_of_le hTS] at hh
  have hmove' : y.val ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    intro hh
    apply hmove
    have hh' := (Z d.radical z ⊔ Q d.radical a).le_normalizer_comap S.subtype hh
    change y ∈ normalizer (((Z d.radical z ⊔ Q d.radical a).subgroupOf S) : Set S) at hh'
    rwa [subgroupOf_sup hZzS (show Q d.radical a ≤ S from fun _ hx => hx.1),←hψker] at hh'
  have hxT : x.val ∈ Q d.radical t := hZzT hx
  have hreg' (v : Vector E.Carrier) (hv : (β ⟨x.val,hxT⟩).val • v=v)
      (u : Q d.radical t) : (β u).val • v=v := by
    have hxψ : ψ x • (k • v)=k • v := by
      change ψ (inclusion hTS ⟨x.val,hxT⟩) • (k • v)=k • v
      rw [hψt ⟨x.val,hxT⟩]
      change (k*(β ⟨x.val,hxT⟩).val*k⁻¹) • (k • v)=_
      rw [mul_smul,mul_smul,inv_smul_smul,hv]
    have hh := hreg (k • v) hxψ (inclusion hTS u) u.property
    rw [hψt] at hh
    change (k*(β u).val*k⁻¹) • (k • v)=k • v at hh
    apply (toLinear k).injective
    simpa only [mul_smul,inv_smul_smul,toLinear_apply] using hh
  have hC := regular_fixed_lift
    (MovedSection.coverAction (replacementMovedSection h d) e)
    (MovedSection.coverProjection (replacementMovedSection h d) e) he
    (U d.radical a) (Q d.radical t) ⟨x.val,hxT⟩ j hj hjr
    β hact hreg'
  have hZaX := g.omega_bound a path.start_color
    (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)
  have hZaT := hZaX.trans ((omegaCenter_le _).trans c.core_le_edge)
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcent : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  let := g.Z_elementary (by omega) a path.start_color
  have hnorm : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have heq : Z d.radical a ⊓ centralizer ({x.val} : Set (FreeAmalgam d.radical))=Z d.radical t := by
    apply le_antisymm
    · rintro y ⟨hy,hyx⟩
      have hy' : y ∈ Z d.radical a := hy
      rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat,
        ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hy'
      obtain ⟨u,hu,v,hv,rfl⟩ := hy'
      have hux : u ∈ centralizer ({x.val} : Set (FreeAmalgam d.radical)) := by
        apply mem_centralizer_singleton_iff.mpr
        have hvx := hcent hv x.val hxT
        have hh := mem_centralizer_singleton_iff.mp hyx
        apply mul_right_cancel (b := v)
        calc
          u*x*v = u*(x*v) := mul_assoc _ _ _
          _ = u*(v*x) := by rw [hvx]
          _ = (u*v)*x := (mul_assoc _ _ _).symm
          _ = x*(u*v) := hh
          _ = x*u*v := (mul_assoc _ _ _).symm
      have huT := (hC.le ⟨hu,hux⟩).2
      rw [hZt]
      exact mem_omegaCenter_iff.mpr ⟨hZaT hy,(mem_omegaCenter_iff.mp (hZaX hy)).2.1,
        (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).mul_mem huT (hcent hv)⟩
    · exact le_inf (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
        (fun y hy => mem_centralizer_singleton_iff.mpr (hcent hy x.val hxT).symm)
  have hcoset' : x.val⁻¹*(y.val*x.val*y.val⁻¹) ∈ Q d.radical a := by
    have hh : x⁻¹*(y*x*y⁻¹) ∈ (Q d.radical a).subgroupOf S := hψker ▸ hcoset
    exact hh
  refine ⟨x.val,hx,?_,heq,y.val,y.property,hyT',
    coset_normalizer_of_conjugate (Q d.radical a) x.val y.val
      (Q_normalized d.radical a y.property) hcoset',hcoset',hmove'⟩
  · intro hxQ
    have hZa : Z d.radical a ≤ Z d.radical t := by
      rw [←heq]
      refine le_inf le_rfl ?_
      intro u hu
      exact mem_centralizer_singleton_iff.mpr
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)
          hu x.val hxQ).symm
    rw [relIndex_eq_one.mpr hZa] at hai
    nlinarith

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
