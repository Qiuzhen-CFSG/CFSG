module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.ProjectiveField
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveField
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows.Cases
public import Theory.FieldTheory.QuadraticFrobenius

/-!
# Field fusion through central covers of PSL₃(4)

The inverse image of the first root plane is elementary. Frobenius displacement
on it has at least four elements: the two root coordinates each have nonzero
trace. A fixed PSL₃(2) has index at most two in the full fixed group when the
covering kernel has order at most two, so it meets that displacement image
nontrivially. The unique involution class of PSL₃(2) then makes every one of
its involutions a coboundary in the original cover.

Coefficient transport converts the literal degree-two source field row to
standard Frobenius. The final theorem retains the original central quotient,
fixed component, and ambient actor, and returns an explicit conjugator.

Source: Aschbacher–Smith, Theorem 2.5.19(4), printed p.562, and the elementary
root-plane lifting argument of I.2.2(3b), printed pp.409–410.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Matrix.PSL3Four.FieldComponentFusion
open Matrix.PSL3Four
variable {E : Type*} [Group E] [Finite E]

private theorem exists_nontrivial_intersection
    (C B W : Subgroup E) (hWC : W ≤ C)
    (hi : B.relIndex C ≤ 2) (hW : 2 < Nat.card W) :
    ∃ x : E, x ∈ W ∧ x ∈ B ∧ x ≠ 1 := by
  have hn : W ⊓ B ≠ ⊥ := by
    intro he
    have hind : B.relIndex W = Nat.card W := by
      rw [← inf_relIndex_left W B, he, relIndex_bot_left]
    have hfinite : B.relIndex C ≠ 0 := by
      change Nat.card (C ⧸ B.subgroupOf C) ≠ 0
      exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
    have hh := relIndex_le_of_le_right (H := B) hWC hfinite
    rw [hind] at hh
    omega
  by_contra! h
  apply hn
  exact (eq_bot_iff_forall _).mpr (fun x hx => h x hx.1 hx.2)

private theorem fixed_card_bound
    (f : E →* PSL) (hc : Nat.card f.ker ≤ 2)
    (a : MulAut E) (hcomp : ∀ x, f (a x) = pslFrobenius (f x)) :
    Nat.card a.fixedSubgroup ≤ 336 := by
  let g := MulAut.fixedSubgroupMap a pslFrobenius f hcomp
  have hker : Nat.card g.ker ≤ 2 := by
    let j : g.ker → f.ker := fun x => ⟨x.val.val, by
      have hh := congrArg Subtype.val x.property
      exact hh⟩
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.ker => (z : E)) he
    exact (Nat.card_le_card_of_injective j hj).trans hc
  have himage : Nat.card g.range ≤ 168 := by
    have hcard : Nat.card pslFrobenius.fixedSubgroup = 168 :=
      (Nat.card_congr projectiveFieldFixedEquiv.toEquiv).trans Matrix.PSL3Two.card_PSL
    exact (Nat.card_le_card_of_injective g.range.subtype g.range.subtype_injective).trans_eq hcard
  have hm := g.ker.card_mul_index
  rw [index_ker] at hm
  calc
    Nat.card a.fixedSubgroup = Nat.card g.ker * Nat.card g.range := hm.symm
    _ ≤ 2 * 168 := Nat.mul_le_mul hker himage
    _ = 336 := rfl

private theorem fixed_component_index_le_two
    (f : E →* PSL) (hc : Nat.card f.ker ≤ 2)
    (a : MulAut E) (hcomp : ∀ x, f (a x) = pslFrobenius (f x))
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL) : B.index ≤ 2 := by
  have hB : Nat.card B = 168 := (Nat.card_congr eB.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hc := fixed_card_bound f hc a hcomp
  have hm := B.card_mul_index
  rw [hB] at hm
  omega
open Matrix.PSL3Four Matrix.PSL3Four.SylowModel
noncomputable section
private def planeMap : Multiplicative (F × F) →* PSL :=
  MatrixRealization.projective.comp axis₁

private theorem planeMap_injective : Function.Injective planeMap :=
  MatrixRealization.projective_injective.comp axis₁_injective

private theorem planeMap_frob (x : Multiplicative (F × F)) :
    pslFrobenius (planeMap x) =
      planeMap (Multiplicative.ofAdd (fieldFrobenius x.toAdd.1, fieldFrobenius x.toAdd.2)) := by
  change pslFrobenius (MatrixRealization.projective (axis₁ x)) = _
  rw [← MatrixRealization.projective_frob]
  apply congrArg MatrixRealization.projective
  apply U.ext <;> simp [frob,axis₁]

private instance : IsElementaryAbelian 2 planeMap.range :=
  IsElementaryAbelian.of_surjective planeMap.rangeRestrict planeMap.rangeRestrict_surjective

private theorem planeMap_trace (x c : F) :
    planeMap (Multiplicative.ofAdd (x,c)) *
      pslFrobenius (planeMap (Multiplicative.ofAdd (x,c))) =
      planeMap (Multiplicative.ofAdd (SylowModel.trace x, SylowModel.trace c)) := by
  rw [planeMap_frob, ← map_mul]
  rfl

private theorem trace_omega : SylowModel.trace omega = 1 := by
  rw [SylowModel.trace, omega_frobenius]
  simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]


private theorem displacement_exists
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hpow : ∀ z ∈ f.ker, z ^ 2 = 1)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (hcomp : ∀ x, f (a x) = pslFrobenius (f x)) :
    ∃ W : Subgroup E, W ≤ a.fixedSubgroup ∧ IsElementaryAbelian 2 W ∧
      2 < Nat.card W ∧ ∀ w ∈ W, ∃ v : E, w = v * (a v)⁻¹ := by
  let V := planeMap.range.comap f
  let : IsElementaryAbelian 2 V := ElementaryParabolic.elementary_comap f hf hk hpow _
  have hstable (v : E) (hv : v ∈ V) : a v ∈ V := by
    obtain ⟨x,hx⟩ := hv
    change f (a v) ∈ planeMap.range
    rw [hcomp, ← hx, planeMap_frob]
    exact ⟨_,rfl⟩
  let av : V →* V := (a.toMonoidHom.comp V.subtype).codRestrict V
    (fun v => hstable v v.property)
  let d : V →* E := V.subtype.comp ((MonoidHom.id V) * av)
  have hd (v : V) : d v = v.val * a v.val := rfl
  have haa (v : E) : a (a v) = v := by
    have h := DFunLike.congr_fun ha v
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hs (v : E) (hv : v ∈ V) : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have hi (v : E) (hv : v ∈ V) : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs v hv)
  have hVcomm (x y : E) (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
    congrArg Subtype.val (mul_comm (⟨x,hx⟩ : V) ⟨y,hy⟩)
  have hfixed : d.range ≤ a.fixedSubgroup := by
    rintro _ ⟨v,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [hd,map_mul,haa]
    exact hVcomm _ _ (hstable v v.property) v.property
  have hW : IsElementaryAbelian 2 d.range := by
    exact IsElementaryAbelian.of_surjective d.rangeRestrict d.rangeRestrict_surjective
  have hbig : 2 < Nat.card d.range := by
    obtain ⟨v₁,hv₁⟩ := hf (planeMap (Multiplicative.ofAdd (omega,0)))
    obtain ⟨v₂,hv₂⟩ := hf (planeMap (Multiplicative.ofAdd (0,omega)))
    have hv₁V : v₁ ∈ V := ⟨_,hv₁.symm⟩
    have hv₂V : v₂ ∈ V := ⟨_,hv₂.symm⟩
    let w₁ := d (⟨v₁,hv₁V⟩ : V)
    let w₂ := d (⟨v₂,hv₂V⟩ : V)
    have hw₁ : f w₁ = planeMap (Multiplicative.ofAdd (1,0)) := by
      rw [show w₁ = v₁*a v₁ from rfl,map_mul,hcomp,hv₁,planeMap_trace,trace_omega,SylowModel.trace_zero]
    have hw₂ : f w₂ = planeMap (Multiplicative.ofAdd (0,1)) := by
      rw [show w₂ = v₂*a v₂ from rfl,map_mul,hcomp,hv₂,planeMap_trace,trace_omega,SylowModel.trace_zero]
    have hn₁ : w₁ ≠ 1 := by
      intro h
      have hh : planeMap (Multiplicative.ofAdd (1,0)) = planeMap 1 := by rw [←hw₁,h,map_one,map_one]
      have hh := planeMap_injective hh
      exact one_ne_zero (congrArg (fun x : Multiplicative (F×F) => x.toAdd.1) hh)
    have hn₂ : w₂ ≠ 1 := by
      intro h
      have hh : planeMap (Multiplicative.ofAdd (0,1)) = planeMap 1 := by rw [←hw₂,h,map_one,map_one]
      have hh := planeMap_injective hh
      exact one_ne_zero (congrArg (fun x : Multiplicative (F×F) => x.toAdd.2) hh)
    have hn : w₁ ≠ w₂ := by
      intro he
      have hh := planeMap_injective (hw₁.symm.trans ((congrArg f he).trans hw₂))
      exact one_ne_zero (congrArg (fun x : Multiplicative (F×F) => x.toAdd.1) hh)
    let : Fintype d.range := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    apply Fintype.two_lt_card_iff.mpr
    exact ⟨1,⟨w₁,⟨_,rfl⟩⟩,⟨w₂,⟨_,rfl⟩⟩,
      fun hh => hn₁ (congrArg Subtype.val hh).symm,
      fun hh => hn₂ (congrArg Subtype.val hh).symm,
      fun hh => hn (congrArg Subtype.val hh)⟩
  refine ⟨d.range,hfixed,hW,hbig,?_⟩
  rintro w ⟨v,rfl⟩
  exact ⟨v,by rw [hi _ (hstable v v.property)];rfl⟩

end
/-- The marked field action fuses every involution of the actual fixed PSL₃(2)
component with its field translate, through the original central quotient. -/
theorem involution_coboundary
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hpow : ∀ z ∈ f.ker, z ^ 2 = 1)
    (hcard : Nat.card f.ker ≤ 2)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (hcomp : ∀ x, f (a x) = pslFrobenius (f x))
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL)
    (k : B) (hk2 : orderOf k = 2) :
    ∃ v : E, ((k : a.fixedSubgroup) : E) = v * (a v)⁻¹ := by
  obtain ⟨W,hWC,hW,hbig,hco⟩ := displacement_exists f hf hk hpow a ha hcomp
  let BM := B.map a.fixedSubgroup.subtype
  have hindex : BM.relIndex a.fixedSubgroup ≤ 2 := by
    change (BM.comap a.fixedSubgroup.subtype).index ≤ 2
    rw [show BM.comap a.fixedSubgroup.subtype = B from
      comap_map_eq_self_of_injective a.fixedSubgroup.subtype_injective B]
    exact fixed_component_index_le_two f hcard a hcomp B eB
  obtain ⟨w,hwW,hwB,hw1⟩ := exists_nontrivial_intersection _ BM W hWC hindex hbig
  let : IsElementaryAbelian 2 W := hW
  obtain ⟨u,hu,heu⟩ := hwB
  let uB : B := ⟨u,hu⟩
  have heu' : (u : E) = w := heu
  have hu2 : orderOf uB = 2 := by
    have hw2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hwW) hw1
    exact (orderOf_coe uB).symm.trans
      ((orderOf_coe u).symm.trans (by simpa only [heu'] using hw2))
  obtain ⟨g,hg⟩ := Matrix.PSL3Two.involutions_conjugate (eB uB) (eB k)
    ((eB.orderOf_eq uB).trans hu2) ((eB.orderOf_eq k).trans hk2)
  let b : B := eB.symm g
  have hb : b*uB*b⁻¹=k := by
    apply eB.injective
    simpa only [b,map_mul,map_inv,MulEquiv.apply_symm_apply,MulAut.conj_apply] using hg
  let bE : E := ((b : a.fixedSubgroup) : E)
  have hab : a bE = bE := (MulAut.mem_fixedSubgroup _ _).mp b.val.property
  obtain ⟨v,hv⟩ := hco w hwW
  refine ⟨bE*v,?_⟩
  have he : bE*w*bE⁻¹ = ((k : a.fixedSubgroup) : E) := by
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,bE,uB,heu'] using congrArg (fun x:B => ((x:a.fixedSubgroup):E)) hb
  rw [←he,hv,map_mul,hab]
  group

/-- A conjugate field marking merely changes the projective coordinates;
the actual quotient map and its kernel are retained. -/
theorem involution_coboundary_of_field_mark
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hpow : ∀ z ∈ f.ker, z ^ 2 = 1)
    (hcard : Nat.card f.ker ≤ 2)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (σ : MulAut PSL) (hcomp : ∀ x, f (a x) = σ (f x))
    (hmark : IsConj pslFrobenius σ)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL)
    (k : B) (hk2 : orderOf k = 2) :
    ∃ v : E, ((k : a.fixedSubgroup) : E) = v * (a v)⁻¹ := by
  obtain ⟨c,hc⟩ := isConj_iff.mp hmark
  let q := c.symm.toMonoidHom.comp f
  have hker : q.ker = f.ker := by
    ext x
    change c.symm (f x)=1 ↔ f x=1
    exact c.symm.map_eq_one_iff
  apply involution_coboundary q (c.symm.surjective.comp hf)
    (by simpa only [hker] using hk) (by simpa only [hker] using hpow)
    (by simpa only [hker] using hcard) a ha ?_ B eB k hk2
  intro x
  change c.symm (f (a x)) = pslFrobenius (c.symm (f x))
  rw [hcomp,←hc]
  simp

/-- Actual ambient conjugacy obtained from the marked cover, for the literal
fixed component and the actor inducing its field automorphism. -/
theorem ambient_fusion
    {G : Type*} [Group G] (ι : E →* G)
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hpow : ∀ z ∈ f.ker, z ^ 2 = 1)
    (hcard : Nat.card f.ker ≤ 2)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (σ : MulAut PSL) (hcomp : ∀ x, f (a x) = σ (f x))
    (hmark : IsConj pslFrobenius σ)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL)
    (k : B) (hk2 : orderOf k = 2)
    (t : G) (hact : ∀ x:E, ι (a x) = t*ι x*t⁻¹) :
    ∃ v : E, ι v*t*(ι v)⁻¹ = t*ι ((k:a.fixedSubgroup):E) := by
  obtain ⟨v,hv⟩ := involution_coboundary_of_field_mark f hf hk hpow hcard a ha σ
    hcomp hmark B eB k hk2
  have hkt : t*ι ((k:a.fixedSubgroup):E) = ι ((k:a.fixedSubgroup):E)*t := by
    have he := (MulAut.mem_fixedSubgroup _ _).mp k.val.property
    have hh := hact ((k:a.fixedSubgroup):E)
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
  refine ⟨v,?_⟩
  rw [hkt,hv,map_mul,map_inv,hact]
  group


open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable

/-- Coefficient transport intertwines the degree-two field action. -/
theorem fieldEquivPSL_field {K : Type*} [Field K]
    (e : K ≃+* F) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (x : PSL(3,K)) :
    Atlas.fieldEquivPSL 3 e (Matrix.PSL3.OuterSolvable.fieldAction K σ x) =
      pslFrobenius (Atlas.fieldEquivPSL 3 e x) := by
  have hmk (A : SL(3,K)) : Atlas.fieldEquivPSL 3 e (A : PSL(3,K)) =
      (Atlas.fieldEquivSL 3 e A : PSL) := Atlas.fieldEquivPSL_mk 3 e A
  obtain ⟨A,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,K)) x
  simp only [QuotientGroup.mk'_apply, fieldAction_mk, hmk, pslFrobenius_mk]
  congr 1
  apply Subtype.ext
  ext i j
  change e (σ (A.val i j)) = (e (A.val i j)) ^ 2
  rw [hσ,map_pow]

/-- The literal source field row over any field of order four admits a
marking intertwining its actor with the standard Frobenius action. -/
theorem exists_field_marking {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : MulAut PSL(3,K))
    (hσ : Matrix.PSL3Even.InvolutionResidualRows.FieldCase 2 σ) :
    ∃ d : PSL(3,K) ≃* PSL, ∀ x, d (σ x) = pslFrobenius (d x) := by
  obtain ⟨g,τ,ht1,he,ht2,⟨c,hc⟩,hr⟩ := hσ
  let : Fintype K := Fintype.ofFinite K
  let : Fintype F := Fintype.ofFinite F
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [← Nat.card_eq_fintype_card] using hK)
  have ht : ∀ x : K, τ x = x ^ 2 := by
    have hτ := FiniteField.involution_eq_frobenius_of_card_square
      (p := 2) (by simpa using hK) τ
      (orderOf_eq_prime ht2 ht1)
    intro x
    rw [hτ]
    rfl
  let e : K ≃+* F := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hK,card_F])
  refine ⟨(linearConj K c).trans (Atlas.fieldEquivPSL 3 e), fun x => ?_⟩
  have hx := DFunLike.congr_fun hc (linearConj K c x)
  change linearConj K c (σ ((linearConj K c).symm (linearConj K c x))) =
    Matrix.PSL3.OuterSolvable.fieldAction K τ (linearConj K c x) at hx
  rw [MulEquiv.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 e (linearConj K c (σ x)) = _
  rw [hx]
  exact fieldEquivPSL_field e τ ht _

/-- The source's field-row mark yields the actual ambient fusion through its
original central quotient and its original fixed component. -/
theorem ambient_fusion_of_field_case
    {K G : Type*} [Field K] [Finite K] [Group G]
    (hK : Nat.card K = 4) (ι : E →* G)
    (f : E →* PSL(3,K)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hpow : ∀ z ∈ f.ker, z ^ 2 = 1)
    (hcard : Nat.card f.ker ≤ 2)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (σ : MulAut PSL(3,K)) (hcomp : ∀ x, f (a x) = σ (f x))
    (hmark : Matrix.PSL3Even.InvolutionResidualRows.FieldCase 2 σ)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL)
    (k : B) (hk2 : orderOf k = 2)
    (t : G) (hact : ∀ x:E, ι (a x) = t*ι x*t⁻¹) :
    ∃ v : E, ι v*t*(ι v)⁻¹ = t*ι ((k:a.fixedSubgroup):E) := by
  obtain ⟨d,hd⟩ := exists_field_marking hK σ hmark
  let q := d.toMonoidHom.comp f
  have hker : q.ker = f.ker := by
    ext x
    change d (f x) = 1 ↔ f x = 1
    exact d.map_eq_one_iff
  apply ambient_fusion ι q (d.surjective.comp hf)
    (by simpa only [hker] using hk) (by simpa only [hker] using hpow)
    (by simpa only [hker] using hcard) a ha pslFrobenius ?_ (IsConj.refl _) B eB k hk2 t hact
  intro x
  change d (f (a x)) = pslFrobenius (d (f x))
  rw [hcomp,hd]


/-- The source form: the given equivalence of the actual central quotient and
the marked quotient actor yield fusion in the ambient group. -/
theorem ambient_fusion_of_center_quotient
    {K G : Type*} [Field K] [Finite K] [Group G]
    (hK : Nat.card K = 4) (ι : E →* G)
    (e : (E ⧸ center E) ≃* PSL(3,K))
    (hpow : ∀ z ∈ center E, z ^ 2 = 1) (hcard : Nat.card (center E) ≤ 2)
    (a : MulAut E) (ha : a ^ 2 = 1)
    (hmark : Matrix.PSL3Even.InvolutionResidualRows.FieldCase 2
      (MulAut.congr e (quotientAut (center E) a)))
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* Matrix.PSL3Two.PSL)
    (k : B) (hk2 : orderOf k = 2)
    (t : G) (hact : ∀ x:E, ι (a x) = t*ι x*t⁻¹) :
    ∃ v : E, ι v*t*(ι v)⁻¹ = t*ι ((k:a.fixedSubgroup):E) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center E := by
    ext x
    change e (QuotientGroup.mk' (center E) x) = 1 ↔ x ∈ center E
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  apply ambient_fusion_of_field_case hK ι f hf (by rw [hker])
    (by simpa only [hker] using hpow) (by simpa only [hker] using hcard) a ha
    (MulAut.congr e (quotientAut (center E) a)) ?_ hmark B eB k hk2 t hact
  intro x
  change e (QuotientGroup.mk' (center E) (a x)) =
    e (quotientAut (center E) a (e.symm (e (QuotientGroup.mk' (center E) x))))
  rw [e.symm_apply_apply,quotientAut_apply_mk]

end Matrix.PSL3Four.FieldComponentFusion
