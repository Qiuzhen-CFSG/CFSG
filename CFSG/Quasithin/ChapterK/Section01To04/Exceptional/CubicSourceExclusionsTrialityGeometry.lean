module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.Complete
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow

/-!
# Elementary triality actors avoiding the short-root class

In either actual parabolic radical, an elementary subgroup with no short-root
involutions has at most q² elements. In the arms radical the leading long
coordinate is a homomorphism; its kernel has no short coordinates. If its
image is nonzero, commutation kills the kernel's second long coordinate.
The central radical reduces to the same zero-leading calculation.
Source: GM04 Lemma 8.6 and Proposition 3.9; GLS3 §§2.4--2.6.
-/

public noncomputable section
open Triality.Standard Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.EvenInvolutionGeometry
open Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.TrialityGeometry
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group

private theorem central_factorization (P : Parameters) (hp : P.prime=2)
    (v : RootOrbitParameters P .central) :
    (coordinates P hp v).val = short P hp 0 (v.1 0) * short P hp 1 (v.1 1) *
      short P hp 2 (v.1 2) * long P hp 1 (v.2 0) * long P hp 2 (v.2 1) := by
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

private theorem central_image (P : Parameters) (hp : P.prime=2)
    (c d : ExtensionField P) (e f : fixedField P) :
    weylRepresentative P hp (.sr 1) * (armsCoordinates P hp (![c,d],![0,e,f])).val *
      (weylRepresentative P hp (.sr 1))⁻¹ =
      (coordinates P hp (![c,0,d],![f,e])).val := by
  rw [armsCoordinates_factorization,central_factorization]
  change weylRepresentative P hp (.sr 1) *
    (long P hp 0 0 * short P hp 1 c * short P hp 2 d * long P hp 1 e * long P hp 2 f) *
      (weylRepresentative P hp (.sr 1))⁻¹ =
    short P hp 0 c * short P hp 1 0 * short P hp 2 d * long P hp 1 f * long P hp 2 e
  simp only [long_zero,short_zero,one_mul,mul_one]
  rw [conjugate_mul,conjugate_mul,conjugate_mul,central_short_one,central_short_two,
    central_long_one,central_long_two]
  rw [mul_assoc _ _ (long P hp 1 f), (highest_commute_long P hp e 1 f).eq,
    ← mul_assoc]

private theorem rotation_image (P : Parameters) (hp : P.prime=2)
    (d : ExtensionField P) (b f : fixedField P) :
    weylRepresentative P hp (.r 5) * (armsCoordinates P hp (![0,d],![b,0,f])).val *
      (weylRepresentative P hp (.r 5))⁻¹ =
      (coordinates P hp (![fieldFrobenius P d,0,0],![f,b])).val := by
  rw [armsCoordinates_factorization,central_factorization]
  change weylRepresentative P hp (.r 5) *
    (long P hp 0 b * short P hp 1 0 * short P hp 2 d * long P hp 1 0 * long P hp 2 f) *
      (weylRepresentative P hp (.r 5))⁻¹ =
    short P hp 0 (fieldFrobenius P d) * short P hp 1 0 * short P hp 2 0 *
      long P hp 1 f * long P hp 2 b
  simp only [long_zero,short_zero,mul_one]
  rw [conjugate_mul,conjugate_mul,rotation_long_zero,rotation_short_two,rotation_long_two]
  rw [(highest_commute_short P hp b 0 (fieldFrobenius P d)).eq,mul_assoc,
    (highest_commute_long P hp b 1 f).eq,← mul_assoc]


private theorem short_of_isConj {n : ℕ} {hn : 0<n} {x y : BinaryCarrier n hn}
    (hx : IsShortRootInvolution n hn x) (h : IsConj x y) :
    IsShortRootInvolution n hn y := by
  obtain ⟨a,ha,hc⟩ := hx
  exact ⟨a,ha,hc.trans h⟩

private theorem order_two_of_square {G : Type*} [Group G] {x : G}
    (hs : x^2=1) (hn : x≠1) : orderOf x=2 := orderOf_eq_prime hs hn

variable (n : ℕ) (hn : 0<n)
local notation "P" => binaryParameters n hn

private theorem central_short_contradiction (x : BinaryCarrier n hn) (hs : x^2=1)
    (hno : ¬ IsShortRootInvolution n hn x) (v : RootOrbitParameters P .central)
    (ha : v.1 0≠0) (hc : IsConj x (coordinates P rfl v).val) : False := by
  have hne : (coordinates P rfl v).val≠1 := by
    intro he
    have he' : coordinates P rfl v = 1 := Subtype.ext he
    have hf := congrArg (fun u => (firstLayer P rfl u).1) he'
    rw [firstLayer_coordinates P rfl,firstLayer_one P rfl] at hf
    exact ha hf
  have hsq : (coordinates P rfl v).val^2=1 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    rw [←hg,conj_pow,hs,mul_one,mul_inv_cancel]
  apply hno
  exact short_of_isConj
    (ShortNormalization.isShortRoot_of_first_ne_zero n hn (coordinates P rfl v)
      (by rw [firstLayer_coordinates P rfl]; exact ha) (order_two_of_square hsq hne)) hc.symm

/-- With zero leading long coordinate, avoiding the short class kills both
cubic-field coordinates of an arms-radical involution. -/
theorem arms_short_coordinates_zero (v : ArmsParameters P) (hb : v.2 0=0)
    (hs : (armsCoordinates P rfl v).val^2=1)
    (hno : ¬ IsShortRootInvolution n hn (armsCoordinates P rfl v).val) :
    v.1 0=0 ∧ v.1 1=0 := by
  let : CharP (ExtensionField P) 2 := inferInstance
  let : CharP (fixedField P) 2 := inferInstance
  have hc : v.1 0=0 := by
    by_contra hc
    have hv : v=(![v.1 0,v.1 1],![0,v.2 1,v.2 2]) := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [hb]
    apply central_short_contradiction n hn _ hs hno
      (![v.1 0,0,v.1 1],![v.2 2,v.2 1]) hc
    exact isConj_iff.mpr ⟨weylRepresentative P rfl (.sr 1),by
      conv_lhs => rw [hv]
      exact central_image P rfl _ _ _ _⟩
  refine ⟨hc,?_⟩
  by_contra hd
  obtain ⟨a,ha⟩ := armsPairing_surjective_left P rfl (v.1 1) hd (v.2 1)
  have hw : shearParameters P a v = (![0,v.1 1],![0,0,v.2 2]) := by
    apply Prod.ext
    · funext i; fin_cases i <;>
        simp [shearParameters,hb,hc,higherCoefficient,-fieldFrobenius_apply]
    · funext i; fin_cases i <;>
        simp [shearParameters,hb,hc,ha,CharTwo.add_self_eq_zero,-fieldFrobenius_apply]
  have hconj : IsConj (armsCoordinates P rfl v).val
      (armsCoordinates P rfl (![0,v.1 1],![0,0,v.2 2])).val :=
    isConj_iff.mpr ⟨short P rfl 0 a, by rw [←hw]; exact short_shear P rfl a v⟩
  apply central_short_contradiction n hn _ hs hno
    (![fieldFrobenius P (v.1 1),0,0],![v.2 2,0])
    ((map_ne_zero (fieldFrobenius P)).mpr hd)
  exact hconj.trans (isConj_iff.mpr ⟨weylRepresentative P rfl (.r 5),
    rotation_image P rfl _ _ _⟩)

/-- A central-radical involution avoiding the short class has only the two
fixed-field long-root coordinates. -/
theorem central_short_coordinates_zero (v : RootOrbitParameters P .central)
    (hs : (coordinates P rfl v).val^2=1)
    (hno : ¬ IsShortRootInvolution n hn (coordinates P rfl v).val) : v.1=0 := by
  have ha : v.1 0=0 := by
    by_contra ha
    exact central_short_contradiction n hn _ hs hno v ha (IsConj.refl _)
  have he : (coordinates P rfl v).val =
      (armsCoordinates P rfl (![v.1 1,v.1 2],![0,v.2 0,v.2 1])).val := by
    rw [central_factorization P rfl,armsCoordinates_factorization P rfl]
    simp [ha,short_zero P rfl,long_zero P rfl]
  have hc := arms_short_coordinates_zero n hn
    (![v.1 1,v.1 2],![0,v.2 0,v.2 1]) rfl (he ▸ hs) (he ▸ hno)
  funext i
  fin_cases i
  · exact ha
  · exact hc.1
  · exact hc.2

private theorem arms_multiply (v w : ArmsParameters P) :
    armsCoordinates P rfl (armsMultiply P v w) =
      armsCoordinates P rfl v * armsCoordinates P rfl w := by
  let e := MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P rfl .arms).symm
  exact (congrArg e (armsEquiv_multiply P rfl v w)).trans (e.map_mul _ _)

private theorem arms_coordinates_one : (armsCoordinates P rfl).symm 1 = (0,0) := by
  apply (armsCoordinates P rfl).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [armsCoordinates_factorization P rfl]
  simp only [Pi.zero_apply,short_zero P rfl,long_zero P rfl,mul_one]
  rfl

private def armsLeading : radical P .arms →* Multiplicative (fixedField P) where
  toFun x := Multiplicative.ofAdd ((armsCoordinates P rfl).symm x).2 0
  map_one' := by rw [arms_coordinates_one]; rfl
  map_mul' x y := by
    obtain ⟨v,rfl⟩ := (armsCoordinates P rfl).surjective x
    obtain ⟨w,rfl⟩ := (armsCoordinates P rfl).surjective y
    rw [←arms_multiply,Equiv.symm_apply_apply,Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
    rfl

private theorem arms_commuting_equation (v w : ArmsParameters P)
    (h : Commute (armsCoordinates P rfl v) (armsCoordinates P rfl w)) :
    armsCocycle P v w = armsCocycle P w v := by
  have he := (armsCoordinates P rfl).injective
    ((arms_multiply n hn v w).trans (h.eq.trans (arms_multiply n hn w v).symm))
  have hh := congrArg (fun z : ArmsParameters P => z.2 2) he
  change v.2 2 + w.2 2 + armsCocycle P v w =
    w.2 2 + v.2 2 + armsCocycle P w v at hh
  linear_combination hh

/-- The central radical contains at most q² elements avoiding the short class. -/
theorem central_card_le (E : Subgroup (radical P .central))
    [IsElementaryAbelian 2 E]
    (hno : ∀ x : E, ¬ IsShortRootInvolution n hn x.val.val) :
    Nat.card E ≤ (binaryParameters n hn).q^2 := by
  let v : E → RootOrbitParameters P .central := fun x => (coordinates P rfl).symm x.val
  have hz (x : E) : (v x).1=0 := by
    apply central_short_coordinates_zero n hn
    · simpa only [v,Equiv.apply_symm_apply,Subgroup.coe_pow,Subgroup.coe_one] using
        congrArg (fun z : radical P .central => z.val) (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
    · simpa only [v,Equiv.apply_symm_apply] using hno x
  let f : E → (Fin 2 → fixedField P) := fun x => (v x).2
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (coordinates P rfl).symm.injective
    exact Prod.ext ((hz x).trans (hz y).symm) hxy
  simpa only [Nat.card_fun,Nat.card_fin,card_fixedField] using
    Nat.card_le_card_of_injective f hf

/-- The arms radical also contains at most q² elements avoiding the short class. -/
theorem arms_card_le (E : Subgroup (radical P .arms))
    [IsElementaryAbelian 2 E]
    (hno : ∀ x : E, ¬ IsShortRootInvolution n hn x.val.val) :
    Nat.card E ≤ (binaryParameters n hn).q^2 := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  let v : E → ArmsParameters P := fun x => (armsCoordinates P rfl).symm x.val
  have hz (x : E) (hx : (v x).2 0=0) : (v x).1=0 := by
    have hh := arms_short_coordinates_zero n hn (v x) hx
      (by simpa only [v,Equiv.apply_symm_apply,Subgroup.coe_pow,Subgroup.coe_one] using
        congrArg (fun z : radical P .arms => z.val) (elemPow_eq_one_of_isElementaryAbelian x.val x.property))
      (by simpa only [v,Equiv.apply_symm_apply] using hno x)
    funext i
    fin_cases i
    · exact hh.1
    · exact hh.2
  by_cases hall : ∀ x : E, (v x).2 0=0
  · let f : E → (Fin 2 → fixedField P) := fun x => ![(v x).2 1,(v x).2 2]
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply (armsCoordinates P rfl).symm.injective
      refine Prod.ext ((hz x (hall x)).trans (hz y (hall y)).symm) ?_
      funext i
      fin_cases i
      · exact (hall x).trans (hall y).symm
      · exact congrFun hxy 0
      · exact congrFun hxy 1
    simpa only [Nat.card_fun,Nat.card_fin,card_fixedField] using
      Nat.card_le_card_of_injective f hf
  · push Not at hall
    obtain ⟨x,hx⟩ := hall
    let f := (armsLeading n hn).comp E.subtype
    have hk0 (y : f.ker) : (v y.val).2 0=0 := congrArg Multiplicative.toAdd y.property
    have hk1 (y : f.ker) : (v y.val).2 1=0 := by
      have hv := hz y.val (hk0 y)
      have hc : Commute (armsCoordinates P rfl (v x))
          (armsCoordinates P rfl (v y.val)) := by
        simp only [v,Equiv.apply_symm_apply]
        exact congrArg (fun z : E => z.val) (mul_comm x y.val)
      have he := arms_commuting_equation n hn (v x) (v y.val) hc
      simp only [armsCocycle,hk0,hv,Pi.zero_apply,mul_zero,
        armsPairing_zero_left,armsPairing_zero_right,add_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_right hx
    let j : f.ker → fixedField P := fun y => (v y.val).2 2
    have hj : Function.Injective j := by
      intro y z hyz
      apply Subtype.ext
      apply Subtype.ext
      apply (armsCoordinates P rfl).symm.injective
      refine Prod.ext ((hz y.val (hk0 y)).trans (hz z.val (hk0 z)).symm) ?_
      funext i
      fin_cases i
      · exact (hk0 y).trans (hk0 z).symm
      · exact (hk1 y).trans (hk1 z).symm
      · exact hyz
    have hK : Nat.card f.ker ≤ (binaryParameters n hn).q := by
      simpa only [card_fixedField] using Nat.card_le_card_of_injective j hj
    have hR : Nat.card f.range ≤ (binaryParameters n hn).q := by
      simpa only [card_fixedField] using
        Nat.card_le_card_of_injective (fun z : f.range => z.val.toAdd)
          (Multiplicative.toAdd.injective.comp Subtype.val_injective)
    calc
      Nat.card E = Nat.card f.range * Nat.card f.ker := by
        rw [←Subgroup.index_ker f]
        exact f.ker.index_mul_card.symm
      _ ≤ (binaryParameters n hn).q * (binaryParameters n hn).q := Nat.mul_le_mul hR hK
      _ = (binaryParameters n hn).q^2 := (pow_two _).symm

/-- On the genuine binary triality group, avoiding the short class forces
an elementary subgroup to have order at most q². -/
theorem no_short_card_le (E : Subgroup (BinaryCarrier n hn))
    [IsElementaryAbelian 2 E]
    (hno : ∀ x ∈ E, ¬ IsShortRootInvolution n hn x) :
    Nat.card E ≤ 2^(2*n) := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (BinaryCarrier n hn) S (unipotentSylow P rfl)
  let f := MulAut.conj g
  have hmap : (S : Subgroup (BinaryCarrier n hn)).map f.toMonoidHom = unipotent P := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def,coe_unipotentSylow P rfl] at hh
    exact hh
  let B := E.map f.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f.toMonoidHom
  have hBU : B ≤ unipotent P := hmap ▸ Subgroup.map_mono hES
  have hnoB (x : BinaryCarrier n hn) (hx : x ∈ B) : ¬ IsShortRootInvolution n hn x := by
    obtain ⟨y,hy,rfl⟩ := hx
    intro hs
    exact hno y hy (short_of_isConj hs (isConj_iff.mpr ⟨g,rfl⟩).symm)
  let E0 := B.subgroupOf (unipotent P)
  let : IsElementaryAbelian 2 E0 := IsElementaryAbelian.subgroupOf hBU
  have hcover := TwoRank.elementary_unipotent_le_radical n hn E0 inferInstance
  have hE0 : E0.map (unipotent P).subtype = B := Subgroup.map_subgroupOf_eq_of_le hBU
  rw [hE0] at hcover
  have hbound (a : Node) (hBa : B ≤ radical P a) : Nat.card B ≤ (binaryParameters n hn).q^2 := by
    let J := B.subgroupOf (radical P a)
    let : IsElementaryAbelian 2 J := IsElementaryAbelian.subgroupOf hBa
    have hnoJ (x : J) : ¬ IsShortRootInvolution n hn x.val.val := hnoB _ x.property
    have hJ : Nat.card J ≤ (binaryParameters n hn).q^2 := by
      cases a
      · exact arms_card_le n hn J hnoJ
      · exact central_card_le n hn J hnoJ
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBa).toEquiv] at hJ
  have hB : Nat.card B ≤ (binaryParameters n hn).q^2 := hcover.elim (hbound .arms) (hbound .central)
  have he := Nat.card_congr (E.equivMapOfInjective f.toMonoidHom f.injective).toEquiv
  rw [←he] at hB
  simpa only [binaryParameters_q,←pow_mul,Nat.mul_comm n 2] using hB

end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.TrialityGeometry
