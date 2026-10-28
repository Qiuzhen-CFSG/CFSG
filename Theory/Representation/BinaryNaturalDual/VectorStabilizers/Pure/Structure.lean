module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Residual
public import Mathlib.LinearAlgebra.Projection

/-!
# The split pure parabolic and its marked quotient actions

The quotient map on X/span(x) has the elementary line radical as kernel
and a homomorphic section obtained by extending an automorphism of a
complement by the identity on x. Duality identifies the same quotient
with the full linear group on ann(x), retaining the actual evaluation
pairing with X/span(x). These constructions are transported through the
actual inner automorphism embedding.

Source: Aschbacher–Smith, H.9.1(3), printed pp.389–390.
-/

@[expose] public section
namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open BinaryLinear.OuterCyclic
open Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Coordinate change on a linear automorphism group. -/
def linearGroupCongr {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : V ≃ₗ[ZMod 2] W) : BinaryLinear.GL V ≃* BinaryLinear.GL W where
  toFun g := (e.symm.trans g).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g k := by ext v; simp

@[simp] theorem linearGroupCongr_apply {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : V ≃ₗ[ZMod 2] W) (g : BinaryLinear.GL V) (w : W) :
    linearGroupCongr e g w = e (g (e.symm w)) := rfl

/-- Contragradience identifies the full linear group with that on the dual. -/
noncomputable def dualGroupEquiv [FiniteDimensional (ZMod 2) V] :
    BinaryLinear.GL V ≃* BinaryLinear.GL (Module.Dual (ZMod 2) V) where
  toFun g := g.symm.dualMap
  invFun k := ((Module.evalEquiv (ZMod 2) V).trans k.symm.dualMap).trans
    (Module.evalEquiv (ZMod 2) V).symm
  left_inv g := by
    ext v
    apply (Module.evalEquiv (ZMod 2) V).injective
    ext q
    simp
  right_inv k := by
    ext q v
    change q ((Module.evalEquiv (ZMod 2) V).symm
      (k.dualMap (Module.evalEquiv (ZMod 2) V v))) = k q v
    rw [Module.apply_evalEquiv_symm_apply]
    rfl
  map_mul' _ _ := by ext; rfl

/-- Annihilating covectors are exactly the dual of the quotient by the marked line. -/
def annihilatorQuotientDual (x : V) :
    annihilator x ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (pointQuotient x) where
  toFun q := (BinaryFivePointStabilizer.line x).liftQ q.val (by
    rw [Submodule.span_singleton_le_iff_mem]
    exact q.property)
  invFun q := ⟨q.comp (BinaryFivePointStabilizer.line x).mkQ, by
    change q ((BinaryFivePointStabilizer.line x).mkQ x) = 0
    have hx : (BinaryFivePointStabilizer.line x).mkQ x = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self x)
    rw [hx, map_zero]⟩
  left_inv q := by apply Subtype.ext; ext; rfl
  right_inv q := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl
  map_add' q r := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl
  map_smul' a q := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl

@[simp] theorem annihilatorQuotientDual_mk (x : V) (q : annihilator x) (v : V) :
    annihilatorQuotientDual x q ((BinaryFivePointStabilizer.line x).mkQ v) = q.val v := rfl

/-- The actual contragredient action of the point stabilizer on ann(x). -/
def pointAnnihilatorAction (x : V) : pointStabilizer x →* BinaryLinear.GL (annihilator x) where
  toFun g := {
    toFun q := ⟨g.val.symm.dualMap q.val, by
      change q.val (g.val.symm x) = 0
      rw [show g.val.symm x = x from (g⁻¹).property]
      exact q.property⟩
    invFun q := ⟨g.val.dualMap q.val, by
      change q.val (g.val x) = 0
      rw [g.property]
      exact q.property⟩
    left_inv q := by apply Subtype.ext; ext v; exact congrArg q.val (g.val.symm_apply_apply v)
    right_inv q := by apply Subtype.ext; ext v; exact congrArg q.val (g.val.apply_symm_apply v)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The annihilator action is the precise dual of the quotient action. -/
theorem annihilator_quotient_compatibility (x : V) (g : pointStabilizer x) (q : annihilator x) :
    annihilatorQuotientDual x (pointAnnihilatorAction x g q) =
      (pointQuotientAction x g).symm.dualMap (annihilatorQuotientDual x q) := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

/-- The quotient linear group is identified with the full linear group on ann(x). -/
noncomputable def quotientAnnihilatorGroupEquiv [FiniteDimensional (ZMod 2) V] (x : V) :
    BinaryLinear.GL (pointQuotient x) ≃* BinaryLinear.GL (annihilator x) :=
  dualGroupEquiv.trans (linearGroupCongr (annihilatorQuotientDual x).symm)

theorem pointAnnihilatorAction_eq [FiniteDimensional (ZMod 2) V] (x : V) (g : pointStabilizer x) :
    pointAnnihilatorAction x g = quotientAnnihilatorGroupEquiv x (pointQuotientAction x g) := by
  apply LinearEquiv.ext
  intro q
  apply (annihilatorQuotientDual x).injective
  rw [annihilator_quotient_compatibility]
  exact ((annihilatorQuotientDual x).apply_symm_apply _).symm

/-- Every linear automorphism of ann(x) occurs as an actual stabilizer action. -/
theorem pointAnnihilatorAction_surjective [FiniteDimensional (ZMod 2) V] (x : V) :
    Function.Surjective (pointAnnihilatorAction x) := by
  intro k
  obtain ⟨g,hg⟩ := BinaryFivePointStabilizer.quotientAction_surjective x
    ((quotientAnnihilatorGroupEquiv x).symm k)
  exact ⟨g, by rw [pointAnnihilatorAction_eq, hg, MulEquiv.apply_symm_apply]⟩

/-- Both marked quotient actions have exactly the same elementary radical. -/
theorem pointAnnihilatorAction_ker [FiniteDimensional (ZMod 2) V] (x : V) :
    (pointAnnihilatorAction x).ker = pointKernel x := by
  ext g
  rw [MonoidHom.mem_ker, pointAnnihilatorAction_eq]
  exact (quotientAnnihilatorGroupEquiv x).map_eq_one_iff

/-- The quotient by the intrinsic two-core acts as the full group on ann(x). -/
noncomputable def pointQuotientTwoCoreEquivAnnihilator [FiniteDimensional (ZMod 2) V] (x : V) :
    (pointStabilizer x ⧸ pCore 2 (pointStabilizer x)) ≃* BinaryLinear.GL (annihilator x) :=
  (QuotientGroup.quotientMulEquivOfEq (point_twoCore x)).trans
    ((BinaryFivePointStabilizer.quotientEquiv x).trans (quotientAnnihilatorGroupEquiv x))

theorem pointQuotientTwoCoreEquivAnnihilator_mk [FiniteDimensional (ZMod 2) V]
    (x : V) (g : pointStabilizer x) :
    pointQuotientTwoCoreEquivAnnihilator x (QuotientGroup.mk' _ g) =
      pointAnnihilatorAction x g := (pointAnnihilatorAction_eq x g).symm

/-- Extend the full kernel group by the identity on its paired vector. -/
def pointLeviSection {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1) :
    BinaryLinear.GL f.ker →* pointStabilizer x :=
  (Subgroup.inclusion (show pairStabilizer x f ≤ pointStabilizer x from fun _ hg => hg.1)).comp
    (pairStabilizerEquivKernel h).symm.toMonoidHom

/-- Quotient restriction of the chosen complementary hyperplane. -/
noncomputable def kernelQuotientEquiv {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1) :
    f.ker ≃ₗ[ZMod 2] pointQuotient x :=
  ((BinaryFivePointStabilizer.line x).quotientEquivOfIsCompl f.ker (line_isCompl_kernel h)).symm

@[simp] theorem kernelQuotientEquiv_apply {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 1) (w : f.ker) :
    kernelQuotientEquiv h w = (BinaryFivePointStabilizer.line x).mkQ w := rfl

/-- The Levi section gives exactly the prescribed quotient automorphism. -/
theorem pointLeviSection_quotient {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1)
    (k : BinaryLinear.GL f.ker) :
    pointQuotientAction x (pointLeviSection h k) = linearGroupCongr (kernelQuotientEquiv h) k := by
  apply LinearEquiv.ext
  intro q
  obtain ⟨w,rfl⟩ := (kernelQuotientEquiv h).surjective q
  rw [linearGroupCongr_apply, LinearEquiv.symm_apply_apply, kernelQuotientEquiv_apply,
    BinaryFivePointStabilizer.quotientAction_mk]
  have hg : (pointLeviSection h k).val w = (k w : V) := by
    change f w • x + (k (kernelProjection h w) : V) = k w
    have hp : kernelProjection h w = w := by
      apply Subtype.ext
      simp [show f w = 0 from w.property]
    simp [show f w = 0 from w.property, hp]
  rw [hg, kernelQuotientEquiv_apply]

/-- A homomorphic splitting of the actual quotient action. -/
noncomputable def pointQuotientSection {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1) :
    BinaryLinear.GL (pointQuotient x) →* pointStabilizer x :=
  (pointLeviSection h).comp (linearGroupCongr (kernelQuotientEquiv h)).symm.toMonoidHom

theorem pointQuotientSection_rightInverse {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1) :
    Function.RightInverse (pointQuotientSection h) (pointQuotientAction x) := by
  intro k
  exact (pointLeviSection_quotient h _).trans ((linearGroupCongr (kernelQuotientEquiv h)).apply_symm_apply k)

/-- The actual inner radical is the pullback of the elementary matrix kernel. -/
noncomputable def innerRadicalEquiv {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    innerRadical d x ≃* pointKernel x where
  toFun g := ⟨innerEquivPoint d x g.val, g.property⟩
  invFun g := ⟨(innerEquivPoint d x).symm g.val, by
    change innerEquivPoint d x ((innerEquivPoint d x).symm g.val) ∈ pointKernel x
    rw [MulEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv g := by apply Subtype.ext; exact (innerEquivPoint d x).symm_apply_apply g.val
  right_inv g := by apply Subtype.ext; exact (innerEquivPoint d x).apply_symm_apply g.val
  map_mul' _ _ := by apply Subtype.ext; exact (innerEquivPoint d x).map_mul _ _

theorem innerRadical_eq_map {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    innerRadical d x = (pointKernel x).map (innerEquivPoint d x).symm.toMonoidHom := by
  ext g
  constructor
  · intro hg
    exact ⟨innerEquivPoint d x g, hg, (innerEquivPoint d x).symm_apply_apply g⟩
  · rintro ⟨k,hk,rfl⟩
    change innerEquivPoint d x ((innerEquivPoint d x).symm k) ∈ pointKernel x
    rwa [MulEquiv.apply_symm_apply]

/-- The intrinsic two-core in the actual inner stabilizer is its geometric radical. -/
theorem inner_twoCore {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    pCore 2 (innerStabilizer d (x,0)) = innerRadical d x := by
  rw [innerRadical_eq_map, ← point_twoCore, pCore_map_iso]

instance innerRadical_normal {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    (innerRadical d x).Normal := MonoidHom.normal_ker _

/-- The actual stabilizer radical is elementary abelian, with no abstract replacement. -/
theorem innerRadical_elementary {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    IsElementaryAbelian 2 (innerRadical d x) := by
  rw [innerRadical_eq_map]
  exact IsElementaryAbelian.map _

theorem innerRadical_card {n : ℕ} (d : CoordinateAction n) {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Nat.card (innerRadical d x) = 2 ^ (n - 1) := by
  rw [Nat.card_congr (innerRadicalEquiv d x).toEquiv, pointKernel_card hx]
  simp only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]

/-- The marked quotient action is surjective for the actual inner stabilizer. -/
theorem innerQuotientAction_surjective {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    Function.Surjective (innerQuotientAction d x) :=
  (BinaryFivePointStabilizer.quotientAction_surjective x).comp (innerEquivPoint d x).surjective

/-- The actual stabilizer quotient, identified by its action rather than its order. -/
noncomputable def innerQuotientEquiv {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    (innerStabilizer d (x,0) ⧸ innerRadical d x) ≃* BinaryLinear.GL (pointQuotient x) :=
  QuotientGroup.quotientKerEquivOfSurjective (innerQuotientAction d x)
    (innerQuotientAction_surjective d x)

/-- The quotient is GL_(n−1)(2), through the marked action on X/span(x). -/
noncomputable def innerQuotientEquivLinear {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    (innerStabilizer d (x,0) ⧸ innerRadical d x) ≃* LinearGroup (n - 1) :=
  (innerQuotientEquiv d x).trans (quotientGroupCoordinates hx)

/-- The full linear action on ann(x), now belonging to the actual inner stabilizer. -/
noncomputable def innerAnnihilatorAction {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    innerStabilizer d (x,0) →* BinaryLinear.GL (annihilator x) :=
  (pointAnnihilatorAction x).comp (innerEquivPoint d x).toMonoidHom

noncomputable def innerQuotientEquivAnnihilator {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) :
    (innerStabilizer d (x,0) ⧸ innerRadical d x) ≃* BinaryLinear.GL (annihilator x) :=
  (innerQuotientEquiv d x).trans (quotientAnnihilatorGroupEquiv x)

/-- The quotient equivalence agrees exactly with the original action on ann(x). -/
theorem innerQuotientEquivAnnihilator_mk {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) :
    innerQuotientEquivAnnihilator d x (QuotientGroup.mk' _ a) = innerAnnihilatorAction d x a :=
  (pointAnnihilatorAction_eq x (innerEquivPoint d x a)).symm

/-- Action compatibility in the original natural-plus-dual module. -/
theorem inner_annihilator_action {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) (q : annihilator x) :
    d.representation a.val (0,q.val) = (0,(innerAnnihilatorAction d x a q).val) := by
  rw [inner_action, naturalDualRepresentation_apply, map_zero]
  rfl

/-- The marked quotient and annihilator actions preserve their natural pairing. -/
theorem inner_quotient_pairing {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n)
    (a : innerStabilizer d (x,0)) (q : annihilator x) (v : OuterCyclic.Space n) :
    annihilatorQuotientDual x (innerAnnihilatorAction d x a q)
      (innerQuotientAction d x a ((BinaryFivePointStabilizer.line x).mkQ v)) = q.val v := by
  change q.val ((innerEquivPoint d x a).val.symm ((innerEquivPoint d x a).val v)) = q.val v
  rw [LinearEquiv.symm_apply_apply]

/-- A splitting in the actual inner stabilizer. -/
noncomputable def innerQuotientSection {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (OuterCyclic.Space n)} (h : f x = 1) :
    BinaryLinear.GL (pointQuotient x) →* innerStabilizer d (x,0) :=
  (innerEquivPoint d x).symm.toMonoidHom.comp (pointQuotientSection h)

theorem innerQuotientSection_rightInverse {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (OuterCyclic.Space n)} (h : f x = 1) :
    Function.RightInverse (innerQuotientSection d h) (innerQuotientAction d x) := by
  intro k
  change pointQuotientAction x (innerEquivPoint d x ((innerEquivPoint d x).symm _)) = k
  rw [MulEquiv.apply_symm_apply]
  exact pointQuotientSection_rightInverse h k


/-- The embedded radical is the literal geometric line radical under conjugation. -/
theorem embeddedRadical_eq_map {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    embeddedRadical d x = (radical (Submodule.span (ZMod 2) {x})).map MulAut.conj := by
  have he : (innerStabilizer d (x,0)).subtype.comp (innerEquivPoint d x).symm.toMonoidHom =
      (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)).comp (pointStabilizer x).subtype := by
    apply MonoidHom.ext
    intro g
    have hh := innerEquivPoint_conj d x ((innerEquivPoint d x).symm g)
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh.symm
  rw [embeddedRadical, innerRadical_eq_map, Subgroup.map_map, he, ← Subgroup.map_map,
    pointKernel_eq_radical, Subgroup.map_subgroupOf_eq_of_le (show
      radical (Submodule.span (ZMod 2) {x}) ≤ pointStabilizer x from
        fun _ hg => hg.1 x (Submodule.mem_span_singleton_self x))]

/-- The elementary radical remains the same group in the ambient automorphism group. -/
theorem embeddedRadical_elementary {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    IsElementaryAbelian 2 (embeddedRadical d x) := by
  let := innerRadical_elementary d x
  exact IsElementaryAbelian.map_subtype

theorem embeddedRadical_card {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Nat.card (embeddedRadical d x) = 2 ^ (n - 1) := by
  rw [embeddedRadical, ← Nat.card_congr ((innerRadical d x).equivMapOfInjective
    (innerStabilizer d (x,0)).subtype (innerStabilizer d (x,0)).subtype_injective).toEquiv]
  exact innerRadical_card d hx

/-- Intrinsic O₂ of the full stabilizer maps to exactly the embedded radical. -/
theorem full_twoCore_map {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    (pCore 2 (fullStabilizer d (x,0))).map (fullStabilizer d (x,0)).subtype =
      embeddedRadical d x := by
  rw [pure_fullStabilizer_eq_innerStabilizer hn d hx, inner_twoCore]
  rfl


/-- The marked quotient action is induced by the original representation on X. -/
theorem innerQuotientAction_mk {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) (v : OuterCyclic.Space n) :
    innerQuotientAction d x a ((BinaryFivePointStabilizer.line x).mkQ v) =
      (BinaryFivePointStabilizer.line x).mkQ ((d.representation a.val (v,0)).1) := by
  rw [inner_action, naturalDualRepresentation_apply]
  rfl

/-- The actual annihilator action has full image. -/
theorem innerAnnihilatorAction_surjective {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    Function.Surjective (innerAnnihilatorAction d x) :=
  (pointAnnihilatorAction_surjective x).comp (innerEquivPoint d x).surjective

end BinaryNaturalDual.VectorStabilizers.Pure
