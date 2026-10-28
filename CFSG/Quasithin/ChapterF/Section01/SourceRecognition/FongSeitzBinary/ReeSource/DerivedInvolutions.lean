module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.FiveFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedFrattini
public import Theory.ElementaryAbelian.Join

/-!
# The involution obstruction in the source derived radical

Let V=U_s₂, E=U₂^(s₁s₂s₁), and let J be the five-factor elementary
subgroup. The four factors of J outside E have trivial intersection with E,
by the actual ordered-root coordinates. A lift of s₂ permutes those four
factors. If it centralizes E, any element of JE that it inverts has square one
and therefore belongs to J.

The inverted Cartan factor of s₂ acts regularly on U₁ minus its identity:
independent-root kernel separation makes this action faithful and its order
is q-1. This constructs, for each nonidentity x,y in U₁, an actual involution
h s₂ exchanging x and y^s₂ and centralizing E. Under the reductio premise
E≤[V,V], the previously proved [V,V]=JE now forces [U₁,U₁^s₂]≤J.
All parameters m≥0 are included. Panel markings and odd linear degree remain
explicit; exclusion of the whole-root reductio case is a later source step.

OriginalDerivedInvolutions applies this calculation to the original two-core
Frattini image and literal Q.q; Section10DerivedInvolutions retains every
N-conjugate in the Section 10 conventions.
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

/-- The four outer elementary factors, omitting the perpendicular Omega root. -/
def outerDerivedSubgroup : Subgroup (X ⧸ Q.D) :=
  ((fiveDerivedFactor Q split 0 ⊔ fiveDerivedFactor Q split 1) ⊔
    fiveDerivedFactor Q split 3) ⊔ fiveDerivedFactor Q split 4

private theorem outer_le_five : outerDerivedSubgroup Q split ≤ fiveDerivedSubgroup Q split := by
  dsimp only [outerDerivedSubgroup,fiveDerivedSubgroup]
  exact sup_le_sup (sup_le_sup (le_sup_left : _ ≤ _ ⊔ fiveDerivedFactor Q split 2) le_rfl) le_rfl

private theorem five_le_outer_perpendicular : fiveDerivedSubgroup Q split ≤
    outerDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
  dsimp only [fiveDerivedSubgroup,outerDerivedSubgroup]
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · exact (omegaOneAmbient_le _).trans le_sup_right
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left

include ν hC μ hB hn in
private theorem outer_product
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (outerDerivedSubgroup Q split : Set (X ⧸ Q.D)) =
      (fiveDerivedFactor Q split 0 : Set (X ⧸ Q.D))*fiveDerivedFactor Q split 1*
        fiveDerivedFactor Q split 3*fiveDerivedFactor Q split 4 := by
  let J := fiveDerivedSubgroup Q split
  let : IsElementaryAbelian 2 J :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  have hcomm {A B : Subgroup (X ⧸ Q.D)} (hA : A ≤ outerDerivedSubgroup Q split)
      (hB : B ≤ outerDerivedSubgroup Q split) : B ≤ normalizer (A : Set (X ⧸ Q.D)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact eq_bot_iff.mpr ((commutator_mono (hB.trans (outer_le_five Q split))
      (hA.trans (outer_le_five Q split))).trans (commutator_self_eq_bot_iff.mpr inferInstance).le)
  let A := fiveDerivedFactor Q split
  change (↑(((A 0 ⊔ A 1) ⊔ A 3) ⊔ A 4) : Set (X ⧸ Q.D)) = _
  rw [coe_mul_of_right_le_normalizer_left _ _ (hcomm le_sup_left le_sup_right),
    coe_mul_of_right_le_normalizer_left _ _
      (hcomm (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)),
    coe_mul_of_right_le_normalizer_left _ _
      (hcomm (le_sup_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans (le_sup_left.trans le_sup_left)))]

include ν hC μ hB hn in
/-- The four outer factors meet the entire perpendicular root trivially. -/
theorem source_outer_derived_disjoint_perpendicular
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    Disjoint (outerDerivedSubgroup Q split)
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  apply disjoint_def.mpr
  intro z hz he
  have hp : z ∈ (fiveDerivedFactor Q split 0 : Set (X ⧸ Q.D))*fiveDerivedFactor Q split 1*
      fiveDerivedFactor Q split 3*fiveDerivedFactor Q split 4 := by
    rw [←outer_product Q split n hn m ν T hC μ hB hm hcore hc]; exact hz
  obtain ⟨_,⟨_,⟨c,hc',d,hd,rfl⟩,f,hf,rfl⟩,g,hg,hzprod⟩ := hp
  have hi : Function.Injective (rootProduct (orderedRoots Q split true 7)) := by
    intro p q heq
    apply (orderedCoordinates Q split true 7 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using heq
  rw [seven_list Q split hm] at hi
  have ht := hi
    (a₁ := (1,1,⟨c,omegaOneAmbient_le _ hc'⟩,⟨d,hd⟩,1,⟨f,hf⟩,
      ⟨g,omegaOneAmbient_le _ hg⟩,PUnit.unit))
    (a₂ := (1,1,1,1,⟨z,he⟩,1,1,PUnit.unit))
    (by simpa only [rootProduct,coe_one,one_mul,mul_one,mul_assoc] using hzprod)
  exact (congrArg (fun t => (t.2.2.2.2.1 : X ⧸ Q.D)) ht).symm

private theorem outer_reflection_stable (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r = Q.simple 1) :
    rightConjugate (outerDerivedSubgroup Q split) (r : X ⧸ Q.D) = outerDerivedSubgroup Q split := by
  let f := (MulAut.conj (r : X ⧸ Q.D)).symm
  have hmap (A : Subgroup (X ⧸ Q.D)) : rightConjugate A (r : X ⧸ Q.D) = A.map f.toMonoidHom := by
    simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hroot (k : Fin 2) (w : Weyl Q) :
      (rootAt Q split k w).map f.toMonoidHom = rootAt Q split k (w*Q.simple 1) := by
    rw [←hmap]; exact rootAt_right Q split k w _ r hr
  change rightConjugate (((omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ⊔
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) ⊔
      rootAt Q split 0 (Q.simple 1*Q.simple 0)) ⊔ omegaOneAmbient (rootAt Q split 1 (Q.simple 0))) _ =
    ((omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ⊔
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) ⊔
      rootAt Q split 0 (Q.simple 1*Q.simple 0)) ⊔ omegaOneAmbient (rootAt Q split 1 (Q.simple 0))
  simp only [hmap,Subgroup.map_sup,
    map_omegaOneAmbient_injective f.toMonoidHom f.injective,hroot,mul_assoc,ssq,mul_one]
  ac_rfl

include ν hC μ hB hn in
/-- A lift of the second reflection centralizing E cannot invert an element
of order four in the enlarged subgroup JE. This is the p.55 involution obstruction. -/
theorem source_perpendicular_join_inversion
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r = Q.simple 1)
    (hrE : (r : X ⧸ Q.D) ∈ centralizer
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)))
    (z : X ⧸ Q.D)
    (hz : z ∈ fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))
    (hinv : (r : X ⧸ Q.D)⁻¹*z*r = z⁻¹) : z ∈ fiveDerivedSubgroup Q split := by
  let W := outerDerivedSubgroup Q split
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let J := fiveDerivedSubgroup Q split
  let : IsElementaryAbelian 2 J :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  have hWE : W ≤ centralizer (E : Set (X ⧸ Q.D)) :=
    (outer_le_five Q split).trans (source_five_derived_centralizes_perpendicular Q split n m ν T hC μ hB hm)
  have hz' : z ∈ W ⊔ E := (sup_le (five_le_outer_perpendicular Q split) le_sup_right) hz
  have hp : z ∈ (W : Set (X ⧸ Q.D))*E := by
    rw [←coe_mul_of_left_le_normalizer_right W E (hWE.trans (Subgroup.centralizer_le_normalizer _))]
    exact hz'
  obtain ⟨a,ha,e,he,rfl⟩ := hp
  let f := (MulAut.conj (r : X ⧸ Q.D)).symm
  have hfa : f a ∈ W := by
    have h := outer_reflection_stable Q split r hr
    rw [rightConjugate,comap_equiv_eq_map_symm'] at h
    change f a ∈ outerDerivedSubgroup Q split
    rw [←h]
    exact mem_map_of_mem f.toMonoidHom ha
  have hfe : f e = e := by
    change (r : X ⧸ Q.D)⁻¹*e*r = e
    have h := mem_centralizer_iff.mp hrE e he
    rw [mul_assoc,h,inv_mul_cancel_left]
  have hae : Commute a e := (mem_centralizer_iff.mp (hWE ha) e he).symm
  have heq : f a*e = a⁻¹*e⁻¹ := by
    calc
      f a*e = f (a*e) := by rw [map_mul,hfe]
      _ = (a*e)⁻¹ := hinv
      _ = a⁻¹*e⁻¹ := by rw [hae.eq,mul_inv_rev]
  have hi := mul_injective_of_disjoint (source_outer_derived_disjoint_perpendicular
    Q split n hn m ν T hC μ hB hm hcore hc)
  have ht := hi (a₁ := (⟨f a,hfa⟩,⟨e,he⟩)) (a₂ := (⟨a⁻¹,inv_mem ha⟩,⟨e⁻¹,inv_mem he⟩)) heq
  have heinv : e = e⁻¹ := congrArg (fun t => (t.2 : X ⧸ Q.D)) ht
  have he2 : e^2 = 1 := by
    rw [pow_two]
    exact (congrArg (· * e) heinv).trans (inv_mul_cancel e)
  have hz2 : (a*e)^2 = 1 := by
    rw [hae.mul_pow,elemPow_eq_one_of_isElementaryAbelian a ((outer_le_five Q split) ha),he2,one_mul]
  rw [←source_perpendicular_five_join_omega Q split n hn m ν T hC μ hB hm hcore hc]
  exact (omegaOneAmbient_le_iff _ _).mp le_rfl (a*e) hz hz2


private theorem linear_perpendicular_independent (hm : rotationOrder Q = 8) :
    (1 : Weyl Q)⁻¹*Q.simple 0*1 ≠
      (Q.simple 0*Q.simple 1*Q.simple 0)⁻¹*Q.simple 1*(Q.simple 0*Q.simple 1*Q.simple 0) := by
  intro he
  have hh := congrArg (weylEquiv Q) he
  simp only [map_mul,map_inv,inv_one,one_mul,mul_one,
    weylEquiv_simple_zero,weylEquiv_simple_one,DihedralGroup.inv_sr,
    DihedralGroup.sr_mul_sr,DihedralGroup.r_mul_sr] at hh
  have heq := DihedralGroup.sr.inj hh
  rw [hm] at heq
  norm_num at heq
  exact (by decide : (3 : ZMod 8) ≠ 0) heq

include ν hC μ hB hn in
/-- The inverted Cartan factor for the Suzuki reflection is regular on the
nonidentity elements of the original linear root, including the binary case. -/
theorem source_suzuki_inverted_linear_regular
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (x y : simpleRoot Q split 0) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ h : reflectionInverted Q split 1,
      (h.val : X ⧸ Q.D)*x*(h.val : X ⧸ Q.D)⁻¹ = y := by
  let s := UnitarySource.actorReflection Q split
  let K := reflectionInverted Q split 1
  let ρ := (simpleRootAction Q split 0).comp K.subtype
  have hperp := (ree_perpendicular_kernels Q split hm n hn m ν T hC μ hB s hcore).2
  have hsep := ree_independent_root_centralizer_eq_bot Q split hm n hn m ν T hC μ hB s hcore
    0 1 1 (Q.simple 0*Q.simple 1*Q.simple 0) (linear_perpendicular_independent Q hm)
  have hinj : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro h hh
    have hh0 : h.val ∈ (simpleRootAction Q split 0).ker := hh
    change h.val ∈ (RootAction.action _ _ _).ker at hh0
    rw [RootAction.action_kernel] at hh0
    have hh1 : h.val ∈ (rootAction Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).ker :=
      hperp.symm ▸ h.property
    change h.val ∈ (RootAction.action _ _ _).ker at hh1
    rw [RootAction.action_kernel] at hh1
    have hz : (h.val : X ⧸ Q.D) ∈
        (((Q.tits.B ⊓ Q.tits.N) ⊓ centralizer (rootAt Q split 0 1 : Set (X ⧸ Q.D))) ⊓
          centralizer (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D))) := by
      rw [rootAt_one]
      exact ⟨⟨h.val.property,hh0⟩,hh1⟩
    rw [hsep] at hz
    exact Subtype.ext (Subtype.ext (mem_bot.mp hz))
  let : IsElementaryAbelian 2 (simpleRoot Q split 0) := by
    rw [←rootAt_one Q split 0]
    exact linear_rootAt_elementary Q split 0 n ν T hC 1
  let : IsCyclic K :=
    (invertedImageEquiv Q split 1 (suzuki_reflectionFixed_eq_kernel Q split 1 m μ hB (s 1))).isCyclic.mpr
      (suzuki_cartanImage_cyclic Q split 1 m μ hB (s 1))
  have hK : Nat.card K = 2^n-1 := by
    rw [ree_common_field_exponent Q split hm n hn m ν T hC μ hB s hcore]
    exact suzuki_inverted_card Q split 1 m μ hB (s 1)
  have hA : Nat.card (simpleRoot Q split 0) = 2^n := by
    rw [←rootAt_one Q split 0]
    exact linear_rootAt_card Q split 0 n ν T hC hn.pos 1
  obtain ⟨h,hh,_⟩ := RootAction.regular_of_card ρ hinj hn.pos hK hA x y hx hy
  exact ⟨h,congrArg Subtype.val hh⟩


include ν hC μ hB hn in
/-- The source Cartan constructs a genuine involution exchanging x and y^s₂,
with its literal Weyl class and centralization of the perpendicular root. -/
theorem source_linear_pair_involution
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (x y : simpleRoot Q split 0) (hx : x ≠ 1) (hy : y ≠ 1) :
    let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
    ∃ r : Q.tits.N,
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r = Q.simple 1 ∧
      (r : X ⧸ Q.D)^2 = 1 ∧
      (r : X ⧸ Q.D) ∈ centralizer
        (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) ∧
      (r : X ⧸ Q.D)⁻¹*x*r = (s.val : X ⧸ Q.D)⁻¹*y*s.val := by
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  obtain ⟨h,hxy⟩ := source_suzuki_inverted_linear_regular Q split n hn m ν T hC μ hB hm hcore x y hx hy
  let hN : Q.tits.N := ⟨h.val,h.val.property.2⟩
  let r : Q.tits.N := hN⁻¹*s.val
  have hs2 : (s.val : X ⧸ Q.D)^2 = 1 :=
    involutoryRootReflection_sq Q split 1 (UnitarySource.actorReflection Q split 1)
  have hsi : (s.val : X ⧸ Q.D)⁻¹ = s.val := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs2)
  have hsh : (s.val : X ⧸ Q.D)⁻¹*(h.val : X ⧸ Q.D)*s.val = (h.val : X ⧸ Q.D)⁻¹ := by
    have hh : simpleCartanAction Q split 1 h.val = h.val⁻¹ := h.property
    have he := congrArg Subtype.val hh
    rw [simpleCartanAction_apply Q split 1 s.val s.class_eq] at he
    exact he
  have hsh' : (s.val : X ⧸ Q.D)*(h.val : X ⧸ Q.D)⁻¹*s.val = h.val := by
    have he := congrArg Inv.inv hsh
    simpa only [mul_inv_rev,inv_inv,hsi,mul_assoc] using he
  have hhE : (h.val : X ⧸ Q.D) ∈ centralizer
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) := by
    have hh : h.val ∈ (rootAction Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).ker := by
      rw [(ree_perpendicular_kernels Q split hm n hn m ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore).2]
      exact h.property
    change h.val ∈ (RootAction.action _ _ _).ker at hh
    rw [RootAction.action_kernel] at hh
    exact hh
  have hsE : (s.val : X ⧸ Q.D) ∈ centralizer
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) := by
    apply mem_centralizer_iff.mpr
    intro e he
    have heR := ((source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).ge he).2
    exact (mem_centralizer_iff.mp heR s.val s.mem_rankOne).symm
  refine ⟨r,?_,?_,?_,?_⟩
  · change QuotientGroup.mk' _ (hN⁻¹*s.val) = _
    rw [map_mul,map_inv,s.class_eq]
    have hh : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) hN = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h.val.property
    rw [hh,inv_one,one_mul]
  · change ((h.val : X ⧸ Q.D)⁻¹*s.val)^2 = 1
    rw [pow_two,mul_assoc,←mul_assoc (s.val : X ⧸ Q.D),hsh',inv_mul_cancel]
  · exact mul_mem (inv_mem hhE) hsE
  · change ((h.val : X ⧸ Q.D)⁻¹*s.val)⁻¹*x*((h.val : X ⧸ Q.D)⁻¹*s.val) = _
    change ((h.val : X ⧸ Q.D)⁻¹*s.val)⁻¹*x*((h.val : X ⧸ Q.D)⁻¹*s.val) =
      (s.val : X ⧸ Q.D)⁻¹*y*s.val
    simp only [mul_inv_rev,inv_inv,mul_assoc]
    simpa only [mul_assoc] using congrArg (fun z : X ⧸ Q.D => (s.val : X ⧸ Q.D)⁻¹*z*s.val) hxy

include ν hC μ hB hn in
/-- Under the hypothetical whole-perpendicular-root containment, every
commutator of the two outer linear roots lies in the five elementary factors. -/
theorem source_far_linear_le_five_of_perpendicular_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1)⁆ ≤ fiveDerivedSubgroup Q split := by
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  have hs2 : (s.val : X ⧸ Q.D)^2 = 1 :=
    involutoryRootReflection_sq Q split 1 (UnitarySource.actorReflection Q split 1)
  have hsroot : rightConjugate (simpleRoot Q split 0) (s.val : X ⧸ Q.D) = rootAt Q split 0 (Q.simple 1) := by
    rw [←rootAt_one Q split 0,rootAt_right Q split 0 1 _ s.val s.class_eq,one_mul]
  have hHV : simpleRoot Q split 0 ≤ simpleRemainder Q split 1 := by
    have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
    have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
    have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_true,mul_one] at h0 h1 h10
    rw [←rootAt_one Q split 0]
    apply rootAt_le_remainder Q split 0 1 1 <;>
      simp only [inv_one,mul_one,one_mul,Q.tits.wordLength_one,h0,h1,h10]
  have hBV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1
  apply commutator_le.mpr
  intro x hx b hb
  by_cases hx1 : x = 1
  · simp only [hx1,commutatorElement_one_left,one_mem]
  by_cases hb1 : b = 1
  · simp only [hb1,commutatorElement_one_right,one_mem]
  let y : simpleRoot Q split 0 := ⟨(s.val : X ⧸ Q.D)*b*(s.val : X ⧸ Q.D)⁻¹,by
    rw [←hsroot] at hb
    exact hb⟩
  have hy1 : y ≠ 1 := by
    intro he
    apply hb1
    have hh := congrArg Subtype.val he
    exact (MulAut.conj (s.val : X ⧸ Q.D)).injective (hh.trans (map_one _).symm)
  obtain ⟨r,hr,hr2,hrE,hry⟩ := source_linear_pair_involution Q split n hn m ν T hC μ hB hm hcore hc
    ⟨x,hx⟩ y (fun he => hx1 (congrArg Subtype.val he)) hy1
  have hrx : (r : X ⧸ Q.D)⁻¹*x*r = b := by
    change (r : X ⧸ Q.D)⁻¹*x*r = (s.val : X ⧸ Q.D)⁻¹*y*s.val at hry
    simpa only [y,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hry
  have hri : (r : X ⧸ Q.D)⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr2)
  have hrb : (r : X ⧸ Q.D)⁻¹*b*r = x := by
    rw [←hrx,hri]
    have hrr : (r : X ⧸ Q.D)*r = 1 := by simpa only [pow_two] using hr2
    simp only [mul_assoc,←mul_assoc (r : X ⧸ Q.D) (r : X ⧸ Q.D),hrr,one_mul,mul_one]
  apply source_perpendicular_join_inversion Q split n hn m ν T hC μ hB hm hcore hc r hr hrE ⁅x,b⁆
  · rw [←(source_perpendicular_in_derived_case Q split n hn m ν T hC μ hB hm hcore hc hE).1]
    exact commutator_mem_commutator (hHV hx) (hBV hb)
  · let f := (MulAut.conj (r : X ⧸ Q.D)).symm
    change f ⁅x,b⁆ = ⁅x,b⁆⁻¹
    rw [map_commutatorElement]
    change ⁅(r : X ⧸ Q.D)⁻¹*x*r,(r : X ⧸ Q.D)⁻¹*b*r⁆ = _
    rw [hrx,hrb,commutatorElement_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
