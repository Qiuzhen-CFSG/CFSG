module

public import Theory.Representation.RepEquiv

@[expose] public section

namespace Representation

open _root_.Representation

open RepMap Function

/-- The endomorphism ring of a representation. -/
abbrev End {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) := ρ →ₗ ρ

namespace End

instance {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : One (End ρ) :=
  ⟨1, fun _ ↦ rfl⟩

instance {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : Mul (End ρ) :=
  ⟨fun f g ↦ RepMap.comp f g⟩

theorem one_eq_id {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : (1 : End ρ) = IntertwiningMap.id ρ := rfl

theorem mul_eq_comp {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) (f g : End ρ) : f * g = f.comp g := rfl

@[simp]
theorem one_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) (v : V) : (1 : End ρ) v = v := rfl

@[simp]
theorem mul_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) (f g : End ρ) (v : V) :
    (f * g) v = f (g v) := rfl

theorem coe_one {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : ⇑(1 : End ρ) = _root_.id := rfl

theorem coe_mul {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) (f g : End ρ) : ⇑(f * g) = f ∘ g := rfl

instance instNontrivial {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) [Nontrivial V] :
    Nontrivial (End ρ) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : V)
  exact nontrivial_of_ne 1 0 fun p => ne (by simpa using RepMap.congr_fun p m)

instance instMonoid {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : Monoid (End ρ) where
  mul_assoc _ _ _ := ext fun _ ↦ rfl
  mul_one := comp_id
  one_mul := id_comp

instance instSemiring {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : Semiring (End ρ) where
  mul_zero f := comp_zero f
  zero_mul f := zero_comp f
  left_distrib := fun _ _ _ ↦ comp_add _ _ _
  right_distrib := fun _ _ _ ↦ add_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem natCast_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (n : ℕ) (m : V) :
    (↑n : End ρ) m = n • m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    simp only [RepMap.add_apply, one_apply, ih, succ_nsmul]

@[simp]
theorem ofNat_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (n : ℕ) [n.AtLeastTwo] (m : V)
    : (ofNat(n) : End ρ) m = ofNat(n) • m := by
  trans (↑n : End ρ) m
  rfl
  rw [natCast_apply]
  rfl

instance instAddCommGroup {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : AddCommGroup (End ρ) := inferInstance

instance instRing {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : Ring (End ρ) where
  intCast z := z • (1 : End ρ)
  intCast_ofNat n := by
    rw [natCast_zsmul, nsmul_eq_mul]
    exact Monoid.mul_one _
  intCast_negSucc n := by
    rw [negSucc_zsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact congrArg Neg.neg (Monoid.mul_one (↑n + 1 : End ρ))

@[simp]
theorem intCast_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (z : ℤ) (m : V) :
    (z : End ρ) m = z • m := by
  cases z with
  | ofNat n =>
    simpa using natCast_apply n m
  | negSucc n =>
    rw [Int.cast_negSucc]
    simp [natCast_apply, succ_nsmul, add_comm]

theorem coe_pow {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (f : End ρ) (n : ℕ) :
    ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

theorem pow_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (f : End ρ) (n : ℕ) (m : V) :
    (f ^ n) m = f^[n] m :=
  congr_fun (coe_pow f n) m

@[simp]
theorem id_pow {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (n : ℕ) : (id : End ρ) ^ n = .id :=
  one_pow n


theorem iterate_succ {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} {f' : End ρ}
    (n : ℕ) : f' ^ (n + 1) = .comp (f' ^ n) f' := by
  rw [pow_succ]
  rfl

/-- Scalar multiplication by `α` as an endomorphism of `ρ`. -/
def smulLeft {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (α : F) : End ρ where
  toFun x := α • x
  map_add' := smul_add _
  map_smul' β _ := by rw [smul_comm]; rfl
  isIntertwining' g := by
    ext; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_smul]

@[simp] lemma smulLeft_eq {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (α : F) :
    smulLeft α = α • .id (ρ := ρ) := rfl

instance applyModule {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : Module (End ρ) V where
  smul := (· <| ·)
  smul_zero := fun r => RepMap.map_zero r
  smul_add := fun r x y => RepMap.map_add r x y
  add_smul := fun r s x => RepMap.add_apply r s x
  zero_smul := fun x => RepMap.zero_apply x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (f : End ρ) (a : V) : f • a = f a := by
  change f a = f a
  rfl

instance apply_faithfulSMul {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : FaithfulSMul (End ρ) V :=
  ⟨fun h => RepMap.ext (fun x => h x)⟩

instance apply_smulCommClass {F G V S : Type*} [CommRing F] [Monoid G]
    [AddCommGroup V] [Module F V] {ρ : Representation F G V} [Monoid S]
    [SMul S F] [SMul S V] [IsScalarTower S F V]
    : SMulCommClass S (End ρ) V where
  smul_comm r e m := by
    change r • e m = e (r • m)
    exact (e.map_smul_of_tower r m).symm

instance apply_smulCommClass' {F G V S : Type*} [CommRing F] [Monoid G]
    [AddCommGroup V] [Module F V] {ρ : Representation F G V} [Monoid S]
    [SMul S F] [SMul S V] [IsScalarTower S F V]
    : SMulCommClass (End ρ) S V :=
  SMulCommClass.symm _ _ _

instance instAlgebra {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} : Algebra F (End ρ) :=
  {
    algebraMap :=
      {
        toFun := fun f ↦ smulLeft f
        map_one' := by simp only [smulLeft_eq, one_smul]; rfl
        map_mul' f₁ f₂ := by
          ext x
          simp [smulLeft_eq, RepMap.smul_apply, mul_smul]
          rw [smul_smul, smul_smul, mul_comm]
        map_zero' := by simp only [smulLeft_eq, zero_smul]
        map_add' f₁ f₂ := by
          ext x
          simp [smulLeft_eq, RepMap.smul_apply, RepMap.add_apply, add_smul]
      }
    commutes' f g := by
      ext x
      simp [smulLeft_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        RepMap.smul_apply]
    smul_def' f g := by
      ext x
      simp [RepMap.smul_apply, smulLeft_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  }

theorem algebraMap_apply {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
    [Module F V] {ρ : Representation F G V} (f : F) :
    (algebraMap F (End ρ)) f = f • id (ρ := ρ) := by
  rw [show (algebraMap F (End ρ)) f = smulLeft f from rfl, smulLeft_eq]
