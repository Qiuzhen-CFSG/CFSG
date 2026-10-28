module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.TransvectionAutomorphisms
public import Theory.GroupTheory.QuaternionCentralProductFactorNormality
public import Theory.GroupTheory.QuaternionCentralProductInvertingAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.SpecificGroups.SL2.ThreeCoreAutomorphisms
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Group

/-!
# Sylow transvection lifts in a quaternion central product

An odd factor-sign involution in the full orthogonal quotient has an intrinsic
involutory automorphism lift. Correcting an ambient lift by an element of the
normal quaternion subgroup keeps it in the original Sylow subgroup. Its square
then lies in the original central involution subgroup. Fixing one quaternion
factor pointwise forces centralization of the corresponding actual SL2(3)
residual factor. Every outside element with central square is conjugate into
the coset of this chosen lift.

Source: Aschbacher–Smith, (2.4.29), printed p.546.
-/
@[expose] public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]
variable (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)

theorem correct_lift_in_sylow (T : Sylow 2 G) (t : G) (ht : t ∈ T)
    (β : MulAut Q)
    (he : d.quotientWreathAction β =
      d.quotientWreathAction (MulAut.conjNormal t)) :
    ∃ y ∈ T, (MulAut.conjNormal y : MulAut Q) = β := by
  let a : G →* MulAut Q := MulAut.conjNormal
  have hk : a t * β⁻¹ ∈ d.quotientWreathAction.ker := by
    change d.quotientWreathAction (a t * β⁻¹) = 1
    rw [map_mul, map_inv, he]
    exact mul_inv_cancel _
  rw [d.quotientWreathAction_ker] at hk
  obtain ⟨q, hq⟩ := hk
  have hat : a t = MulAut.conj q * β := by
    rw [hq]
    group
  have hQ : Q ≤ (T : Subgroup G) :=
    (IsPGroup.of_card (p := 2) (n := 5) (by rw [d.card]; norm_num)).le_sylow_of_normal T
  refine ⟨(q : G)⁻¹ * t, (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem
    (hQ q.property)) ht, ?_⟩
  change a ((q : G)⁻¹ * t) = β
  have haq : a (q : G) = MulAut.conj q := by
    ext x
    rfl
  rw [map_mul, map_inv, haq, hat]
  group

omit [Finite G] in
theorem central_square_of_action_square (hcent : centralizer (Q : Set G) ≤ Q)
    (y : G) (hy : (MulAut.conjNormal y : MulAut Q)^2 = 1) :
    y^2 ∈ (center Q).map Q.subtype := by
  have hc : y^2 ∈ centralizer (Q : Set G) := by
    intro q hq
    have h := congrArg (fun a : MulAut Q => (a ⟨q,hq⟩ : G)) hy
    have hh : y^2 * q * (y^2)⁻¹ = q := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.conjNormal_apply,
        MulAut.one_apply, mul_inv_rev, mul_assoc] using h
    exact (mul_inv_eq_iff_eq_mul).mp hh |>.symm
  have hm : y^2 ∈ Q := hcent hc
  refine ⟨⟨y^2,hm⟩, ?_, rfl⟩
  exact mem_center_iff.mpr fun q => Subtype.ext (hc q q.property)

theorem residual_factor_normalized
    (k : QuaternionResidualCentralProduct Q d) (y : G)
    (hl : d.left.map (MulAut.conjNormal y).toMonoidHom = d.left) :
    y ∈ normalizer (k.left : Set G) ∧ y ∈ normalizer (k.right : Set G) := by
  have hr := (d.map_left_eq_iff_map_right_eq (MulAut.conjNormal y)).mp hl
  have hn (R : Subgroup Q)
      (hR : R.map (MulAut.conjNormal y).toMonoidHom = R) :
      y ∈ normalizer (R.map Q.subtype : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_map]
    change R.map (Q.subtype.comp (MulAut.conjNormal y).toMonoidHom) = R.map Q.subtype
    rw [← map_map, hR]
  have hres : y ∈ normalizer (pResidual 2 G : Set G) := by
    rw [normalizer_eq_top]
    trivial
  rw [k.centralizer_descriptions.1, k.centralizer_descriptions.2]
  exact ⟨inf_normalizer_le_normalizer_inf ⟨hres,
    normalizer_le_normalizer_centralizer _ (hn d.right hr)⟩,
    inf_normalizer_le_normalizer_inf ⟨hres,
    normalizer_le_normalizer_centralizer _ (hn d.left hl)⟩⟩


theorem centralizes_left_residual_of_fixes_left
    (k : QuaternionResidualCentralProduct Q d) (y : G)
    (hfix : ∀ x : d.left, (MulAut.conjNormal y : MulAut Q) x = x) :
    y ∈ centralizer (k.left : Set G) := by
  have hl : d.left.map (MulAut.conjNormal y).toMonoidHom = d.left := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (MulAut.conjNormal y : MulAut Q) x ∈ _
      rw [hfix ⟨x,hx⟩]
      exact hx
    · intro hz
      exact ⟨z,hz,hfix ⟨z,hz⟩⟩
  have hn := (residual_factor_normalized Q d k y hl).1
  apply Matrix.SpecialLinearGroup.centralizes_of_normalizes_of_centralizes_twoCore
    k.left k.left_model.some y hn
  rw [k.left_core]
  rintro x ⟨q,hq,rfl⟩
  have hh := congrArg Subtype.val (hfix ⟨q,hq⟩)
  exact (mul_inv_eq_iff_eq_mul).mp hh |>.symm

theorem centralizes_right_residual_of_fixes_right
    (k : QuaternionResidualCentralProduct Q d) (y : G)
    (hfix : ∀ x : d.right, (MulAut.conjNormal y : MulAut Q) x = x) :
    y ∈ centralizer (k.right : Set G) := by
  have hr : d.right.map (MulAut.conjNormal y).toMonoidHom = d.right := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (MulAut.conjNormal y : MulAut Q) x ∈ _
      rw [hfix ⟨x,hx⟩]
      exact hx
    · intro hz
      exact ⟨z,hz,hfix ⟨z,hz⟩⟩
  have hl := (d.map_left_eq_iff_map_right_eq (MulAut.conjNormal y)).mpr hr
  have hn := (residual_factor_normalized Q d k y hl).2
  apply Matrix.SpecialLinearGroup.centralizes_of_normalizes_of_centralizes_twoCore
    k.right k.right_model.some y hn
  rw [k.right_core]
  rintro x ⟨q,hq,rfl⟩
  have hh := congrArg Subtype.val (hfix ⟨q,hq⟩)
  exact (mul_inv_eq_iff_eq_mul).mp hh |>.symm


/-- The canonical outer action has the original quaternion subgroup as kernel. -/
theorem ambientWreathAction_ker (hcent : centralizer (Q : Set G) ≤ Q) :
    (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q)).ker = Q := by
  rw [← MonoidHom.comap_ker, d.quotientWreathAction_ker,
    MulAut.conjNormal_comap_innerSubgroup, sup_eq_left.mpr hcent]

/-- A lift fixes one actual quaternion factor and centralizes its actual residual
SL2(3) factor; the action on the other quaternion factor is outer. -/
def IsResidualTransvection (k : QuaternionResidualCentralProduct Q d) (y : G) : Prop :=
  (((∀ x : d.left, (MulAut.conjNormal y : MulAut Q) (x : Q) = (x : Q)) ∧
      y ∈ centralizer (k.left : Set G) ∧
      ¬∃ b : d.right, ∀ x : d.right,
        (MulAut.conjNormal y : MulAut Q) (x : Q) = ((b*x*b⁻¹ : d.right) : Q)) ∨
   ((∀ x : d.right, (MulAut.conjNormal y : MulAut Q) (x : Q) = (x : Q)) ∧
      y ∈ centralizer (k.right : Set G) ∧
      ¬∃ b : d.left, ∀ x : d.left,
        (MulAut.conjNormal y : MulAut Q) (x : Q) = ((b*x*b⁻¹ : d.left) : Q)))

/-- The source transvection is chosen in the original Sylow subgroup and outside
its original factor-sign kernel. No involutory ambient lift is asserted. -/
theorem exists_sylow_transvection_lift
    (hcent : centralizer (Q : Set G) ≤ Q)
    (k : QuaternionResidualCentralProduct Q d)
    (T : Sylow 2 G) (S : Subgroup G)
    (hf : Function.Surjective
      (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q)))
    (hS : S = (T : Subgroup G) ⊓
      (BinaryFourPlus.factorSign.comp
        (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q))).ker) :
    ∃ y ∈ (T : Subgroup G), y ∉ S ∧ y^2 ∈ (center Q).map Q.subtype ∧
      (MulAut.conjNormal y : MulAut Q)^2 = 1 ∧ IsResidualTransvection Q d k y := by
  let f : G →* BinaryFourPlus.Wreath := d.quotientWreathAction.comp MulAut.conjNormal
  obtain ⟨t,ht,ht2,htout⟩ :=
    BinaryFourPlus.TransvectionCoset.exists_sylow_outside_kernel f hf T
  have hta : (d.quotientWreathAction (MulAut.conjNormal t))^2 = 1 := by
    change f (t^2) = 1 at ht2
    rwa [map_pow] at ht2
  have hts : BinaryFourPlus.factorSign (d.quotientWreathAction (MulAut.conjNormal t)) ≠ 1 := by
    intro hs
    exact htout ⟨ht,hs⟩
  obtain ⟨β,hβ,hβ2,hβcases⟩ := d.exists_transvection_involution
    (MulAut.conjNormal t) hta hts
  obtain ⟨y,hy,hey⟩ := correct_lift_in_sylow Q d T t ht β hβ
  have hfy : f y = f t := by
    change d.quotientWreathAction (MulAut.conjNormal y) = _
    rw [hey]
    exact hβ
  have hyout : y ∉ S := by
    rw [hS]
    intro hh
    have hsy : BinaryFourPlus.factorSign (f y) = 1 := hh.2
    rw [hfy] at hsy
    exact hts hsy
  have hy2 : (MulAut.conjNormal y : MulAut Q)^2 = 1 := hey ▸ hβ2
  refine ⟨y,hy,hyout,central_square_of_action_square Q hcent y hy2,hy2,?_⟩
  rcases hβcases with ⟨hfix,houter⟩ | ⟨hfix,houter⟩
  · have hfix' : ∀ x : d.left, (MulAut.conjNormal y : MulAut Q) x = x := hey ▸ hfix
    exact Or.inl ⟨hfix',centralizes_left_residual_of_fixes_left Q d k y hfix',hey ▸ houter⟩
  · have hfix' : ∀ x : d.right, (MulAut.conjNormal y : MulAut Q) x = x := hey ▸ hfix
    exact Or.inr ⟨hfix',centralizes_right_residual_of_fixes_right Q d k y hfix',hey ▸ houter⟩

/-- Every outside element with central square is conjugate into the coset of an
actual chosen transvection lift. The conclusion retains the original subgroup. -/
theorem conjugate_into_transvection_coset
    (hcent : centralizer (Q : Set G) ≤ Q)
    (T S : Subgroup G)
    (hf : Function.Surjective
      (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q)))
    (hS : S = T ⊓ (BinaryFourPlus.factorSign.comp
      (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q))).ker)
    (y : G) (hy : y ∈ T) (hyout : y ∉ S)
    (hy2 : (MulAut.conjNormal y : MulAut Q)^2 = 1)
    (t : G) (ht : t ∈ T) (htout : t ∉ S)
    (ht2 : t^2 ∈ (center Q).map Q.subtype) :
    ∃ m : G, m*t*m⁻¹*y⁻¹ ∈ Q := by
  let f : G →* BinaryFourPlus.Wreath := d.quotientWreathAction.comp MulAut.conjNormal
  have hk : f.ker = Q := ambientWreathAction_ker Q d hcent
  have htker : t^2 ∈ f.ker := by
    rw [hk]
    exact (map_subtype_le (center Q)) ht2
  have hfy2 : (f y)^2 = 1 := by
    change (d.quotientWreathAction (MulAut.conjNormal y))^2 = 1
    rw [← map_pow,hy2,map_one]
  have hfys : BinaryFourPlus.factorSign (f y) ≠ 1 := by
    intro hh
    exact hyout (hS ▸ ⟨hy,hh⟩)
  obtain ⟨m,hm⟩ := BinaryFourPlus.TransvectionCoset.conjugate_image_to_odd_involution
    f hf T t ht (hS ▸ htout) htker (f y) hfy2 hfys
  refine ⟨m,?_⟩
  rw [← hk]
  change f (m*t*m⁻¹*y⁻¹) = 1
  rw [map_mul,map_inv,hm,mul_inv_cancel]


omit [Finite G] in
/-- Restrict an actual involutory conjugation action to an invariant quaternion
factor, retaining the original ambient embedding and its outer action. -/
theorem ambient_factor_action (R : Subgroup Q) (y : G)
    (hR : R.map (MulAut.conjNormal y).toMonoidHom = R)
    (hy : (MulAut.conjNormal y : MulAut Q)^2 = 1)
    (ho : ¬∃ b : R, ∀ x : R,
      (MulAut.conjNormal y : MulAut Q) (x : Q) = ((b*x*b⁻¹ : R) : Q)) :
    ∃ α : MulAut (R.map Q.subtype), α^2 = 1 ∧
      (¬∃ b : R.map Q.subtype, ∀ x : R.map Q.subtype, α x = b*x*b⁻¹) ∧
      ∀ x : R.map Q.subtype, (α x : G) = y*x*y⁻¹ := by
  let a : MulAut Q := MulAut.conjNormal y
  let aR : MulAut R := (a.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  let e : R ≃* R.map Q.subtype := R.equivMapOfInjective Q.subtype Q.subtype_injective
  have haR (x : R) : (aR x : Q) = a (x : Q) := rfl
  have haR2 : aR^2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (aR (aR x) : Q) = (x : Q)
    rw [haR,haR]
    exact DFunLike.congr_fun hy (x : Q)
  let α : MulAut (R.map Q.subtype) := MulAut.congr e aR
  have he (x : R) : (e x : G) = (x : G) := rfl
  have hae (x : R) : α (e x) = e (aR x) := by
    change e (aR (e.symm (e x))) = e (aR x)
    rw [e.symm_apply_apply]
  refine ⟨α,?_,?_,?_⟩
  · change (MulAut.congr e aR)^2 = 1
    rw [←map_pow,haR2,map_one]
  · rintro ⟨b,hb⟩
    apply ho
    refine ⟨e.symm b,fun x => ?_⟩
    have hh := congrArg e.symm (hb (e x))
    rw [hae,e.symm_apply_apply,map_mul,map_mul,map_inv,e.symm_apply_apply] at hh
    exact congrArg (fun x : R => (x : Q)) hh
  · intro x
    obtain ⟨r,rfl⟩ := e.surjective x
    rw [hae,he]
    rfl

/-- The chosen element has both its local action and the quotient conjugacy
cover, expressed using the same Sylow subgroup and sign kernel. -/
theorem exists_sylow_transvection_with_conjugacy
    (hcent : centralizer (Q : Set G) ≤ Q)
    (k : QuaternionResidualCentralProduct Q d)
    (T : Sylow 2 G) (S : Subgroup G)
    (hf : Function.Surjective
      (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q)))
    (hS : S = (T : Subgroup G) ⊓
      (BinaryFourPlus.factorSign.comp
        (d.quotientWreathAction.comp (MulAut.conjNormal : G →* MulAut Q))).ker) :
    ∃ y ∈ (T : Subgroup G), y ∉ S ∧ y^2 ∈ (center Q).map Q.subtype ∧
      (MulAut.conjNormal y : MulAut Q)^2 = 1 ∧ IsResidualTransvection Q d k y ∧
      ∀ t ∈ (T : Subgroup G), t ∉ S → t^2 ∈ (center Q).map Q.subtype →
        ∃ m : G, m*t*m⁻¹*y⁻¹ ∈ Q := by
  obtain ⟨y,hy,hyout,hy2,hya,htrans⟩ := exists_sylow_transvection_lift Q d hcent k T S hf hS
  exact ⟨y,hy,hyout,hy2,hya,htrans,fun t ht hout h2 =>
    conjugate_into_transvection_coset Q d hcent T S hf hS y hy hyout hya t ht hout h2⟩


omit [Finite G] [Q.Normal] in
private theorem factor_map_eq_of_fixes (R : Subgroup Q) (a : MulAut Q)
    (hf : ∀ x : R, a (x : Q) = (x : Q)) : R.map a.toMonoidHom = R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change a z ∈ R
    rw [hf ⟨z,hz⟩]
    exact hz
  · intro hx
    exact ⟨x,hx,hf ⟨x,hx⟩⟩

/-- The two possible orientations of the source transvection provide the actual
quaternion pair, its SL2(3) overgroup, and the literal moving-factor actor. -/
theorem residual_transvection_orientation
    (k : QuaternionResidualCentralProduct Q d) (y : G)
    (hy : (MulAut.conjNormal y : MulAut Q)^2 = 1)
    (htrans : IsResidualTransvection Q d k y) :
    ∃ B C L : Subgroup G,
      Nonempty (B ≃* QuaternionGroup 2) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
      B ⊔ C = Q ∧ B ⊓ C = (center Q).map Q.subtype ∧
      Nat.card (B ⊓ C : Subgroup G) = 2 ∧
      (∀ b ∈ B, ∀ c ∈ C, b*c=c*b) ∧ B ≤ L ∧
      B = (pCore 2 L).map L.subtype ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      y ∈ centralizer (L : Set G) ∧
      ∃ α : MulAut C, α^2 = 1 ∧ (¬∃ b : C, ∀ x : C, α x = b*x*b⁻¹) ∧
        ∀ x : C, (α x : G) = y*x*y⁻¹ := by
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  have hspan : B ⊔ C = Q := by
    rw [←map_sup,d.span,←MonoidHom.range_eq_map,range_subtype]
  have hinter : B ⊓ C = (center Q).map Q.subtype := by
    rw [←map_inf _ _ _ Q.subtype_injective,←d.center_eq]
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    d.left_model.map fun e =>
      (d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans e
  have hC : Nonempty (C ≃* QuaternionGroup 2) :=
    d.right_model.map fun e =>
      (d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans e
  have hcard : Nat.card (B ⊓ C : Subgroup G) = 2 := by
    rw [hinter,card_map_of_injective Q.subtype_injective,d.center_card]
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
    rintro b ⟨b',hb,rfl⟩ c ⟨c',hc,rfl⟩
    exact congrArg Subtype.val (d.commute b' hb c' hc)
  rcases htrans with ⟨hfix,hcentral,houter⟩ | ⟨hfix,hcentral,houter⟩
  · have hleft := factor_map_eq_of_fixes Q d.left (MulAut.conjNormal y) hfix
    have hright := (d.map_left_eq_iff_map_right_eq (MulAut.conjNormal y)).mp hleft
    obtain ⟨α,hα,ho,happly⟩ := ambient_factor_action Q d.right y hright hy houter
    exact ⟨B,C,k.left,hB,hC,hspan,hinter,hcard,hcomm,k.left_contains,k.left_core.symm,k.left_model,
      hcentral,α,hα,ho,happly⟩
  · have hright := factor_map_eq_of_fixes Q d.right (MulAut.conjNormal y) hfix
    have hleft := (d.map_left_eq_iff_map_right_eq (MulAut.conjNormal y)).mpr hright
    obtain ⟨α,hα,ho,happly⟩ := ambient_factor_action Q d.left y hleft hy houter
    exact ⟨C,B,k.right,hC,hB,(sup_comm _ _).trans hspan,(inf_comm _ _).trans hinter,
      (by simpa only [inf_comm] using hcard),
      (fun c hc b hb => (hcomm b hb c hc).symm),k.right_contains,k.right_core.symm,k.right_model,
      hcentral,α,hα,ho,happly⟩

end Subgroup.QuaternionCentralProductData
