/-
Authors: Yusen Tang
-/

module

public import Submission.FeitThompson.Representation.RepEquiv

namespace Representation

open RepMap Function

variable {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V]
  [Module F V] (ρ : Representation F G V)

/-- The endomorphism ring of a representation. -/
public abbrev End := ρ →ₗ ρ

namespace End

public instance : One (End ρ) := ⟨1, fun _ ↦ rfl⟩

public instance : Mul (End ρ) := ⟨fun f g ↦ RepMap.comp f g⟩

public theorem one_eq_id : (1 : End ρ) = IntertwiningMap.id ρ := rfl

public theorem mul_eq_comp (f g : End ρ) : f * g = f.comp g := rfl

@[simp]
public theorem one_apply (v : V) : (1 : End ρ) v = v := rfl

@[simp]
public theorem mul_apply (f g : End ρ) (v : V) : (f * g) v = f (g v) := rfl

public theorem coe_one : ⇑(1 : End ρ) = _root_.id := rfl

public theorem coe_mul (f g : End ρ) : ⇑(f * g) = f ∘ g := rfl

public instance instNontrivial [Nontrivial V] : Nontrivial (End ρ) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : V)
  exact nontrivial_of_ne 1 0 fun p => ne (RepMap.congr_fun p m)

public instance instMonoid : Monoid (End ρ) where
  mul_assoc _ _ _ := ext fun _ ↦ rfl
  mul_one := comp_id
  one_mul := id_comp

variable {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V]
  [Module F V] {ρ : Representation F G V}

public instance instSemiring : Semiring (End ρ) where
  mul_zero f := comp_zero ρ ρ f
  zero_mul := zero_comp ρ ρ
  left_distrib := fun _ _ _ ↦ comp_add _ _ _
  right_distrib := fun _ _ _ ↦ add_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
public theorem natCast_apply (n : ℕ) (m : V) : (↑n : End ρ) m = n • m := by
  trans (n • (1 : End ρ)) m
  simp only [nsmul_eq_mul, mul_one]
  rfl

@[simp]
public theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (m : V) :
    (ofNat(n) : End ρ) m = ofNat(n) • m := by
  trans (↑n : End ρ) m
  rfl
  rw [natCast_apply]
  rfl

public instance instRing : Ring (End ρ) where
  intCast z := z • (1 : End ρ)
  intCast_ofNat n := by simp only [natCast_zsmul, nsmul_eq_mul, mul_one]
  intCast_negSucc n := by simp only [negSucc_zsmul, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_one, neg_add_rev]

@[simp]
public theorem intCast_apply (z : ℤ) (m : V) : (z : End ρ) m = z • m :=
  rfl

public theorem coe_pow (f : End  ρ) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

public theorem pow_apply (f : End ρ) (n : ℕ) (m : V) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m

public theorem pow_map_zero_of_le {f : End ρ} {m : V} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← Nat.sub_add_cancel hk, pow_add, mul_apply, hm, RepMap.map_zero]

public theorem commute_pow_left_of_commute
    {W : Type*} [AddCommMonoid W] [Module F W] {σ : Representation F G W}
    {f : ρ →ₗ σ} {g : End ρ} {g₂ : End σ}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction k with
  | zero => ext; simp only [pow_zero, coe_comp, Function.comp_apply, one_apply]
  | succ k ih => rw [pow_succ', pow_succ', mul_eq_comp, RepMap.comp_assoc, ih,
    ← RepMap.comp_assoc, h, RepMap.comp_assoc, mul_eq_comp]

@[simp]
public theorem id_pow (n : ℕ) : (id : End ρ) ^ n = .id :=
  one_pow n

variable {f' : End ρ}

public theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = .comp (f' ^ n) f' := by rw [pow_succ, mul_eq_comp]

public theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h

public theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h

public theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h

public theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia), iterate_succ, coe_comp] at h
  exact h.of_comp

public theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn), pow_succ', coe_mul] at h
  exact Surjective.of_comp h

/-- Scalar multiplication by `α` as an endomorphism of `ρ`. -/
@[expose]
public def smulLeft (α : F) : End ρ where
  toFun x := α • x
  map_add' := smul_add _
  map_smul' β _ := by rw [smul_comm]; rfl
  isIntertwining' g := by ext; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_smul]

@[simp]
public lemma smulLeft_eq (α : F) : smulLeft α = α • .id (ρ := ρ) := rfl

public instance applyModule : Module (End ρ) V where
  smul := (· <| ·)
  smul_zero := RepMap.map_zero
  smul_add := RepMap.map_add
  add_smul := RepMap.add_apply _ _
  zero_smul := RepMap.zero_apply _ _
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
public protected theorem smul_def (f : End ρ) (a : V) : f • a = f a :=
  rfl

public instance apply_faithfulSMul : FaithfulSMul (End ρ) V :=
  ⟨RepMap.ext⟩

variable {S : Type*} [Monoid S]

public instance apply_smulCommClass [SMul S F] [SMul S V] [IsScalarTower S F V] :
    SMulCommClass S (End ρ) V where
  smul_comm r e m := (e.map_smul_of_tower r m).symm

public instance apply_smulCommClass' [SMul S F] [SMul S V] [IsScalarTower S F V] :
    SMulCommClass (End ρ) S V :=
  SMulCommClass.symm _ _ _

public instance : Algebra F (End ρ) := {
  algebraMap := {
    toFun := fun f ↦ smulLeft f
    map_one' := by simp only [smulLeft_eq, one_smul]; rfl
    map_mul' f₁ f₂ := by
      ext
      simp only [smulLeft_eq, smul_apply, id_coe, id_eq, mul_apply, RepMap.map_smul]
      rw [← mul_smul, mul_comm]
    map_zero' := by simp only [smulLeft_eq, zero_smul]
    map_add' f₁ f₂ := by
      ext
      simp only [smulLeft_eq, smul_apply, id_coe, id_eq, add_apply, add_smul]
  }
  commutes' f g := by
    ext
    simp only [smulLeft_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_apply,
      smul_apply, id_coe, id_eq, RepMap.map_smul]
  smul_def' f g := by
    ext
    simp only [smul_apply, smulLeft_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_apply, id_coe, id_eq]
}

public theorem algebraMap_apply (f : F) : (algebraMap F (End ρ)) f = f • id (ρ := ρ) :=
  rfl
