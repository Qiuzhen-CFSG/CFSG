module
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Fixed-space bounds for the natural SL₃ normalizer

An additive normalizer of the natural SL₃ action preserves its scalar
commutant, hence acts semilinearly over the original field. A nonidentity
semilinear operator on F³ fixes at most |F|² vectors: a linear operator
moves at least one field dimension, while a nontrivial scalar twist moves
at least half the binary dimension. The estimate needs no involution or
odd-degree hypothesis and retains the prescribed automorphism of SL₃.

Source application: Aschbacher–Smith C.1.35, printed p.139, the first
natural fixed-codimension estimate in (+).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3NaturalFixed
open Matrix
variable {F : Type*} [Field F] [Finite F]

/-- An additive intertwiner of the natural action is semilinear over the same field. -/
theorem semilinear_of_intertwines
    (f : (Fin 3 → F) ≃+ (Fin 3 → F))
    (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hf : ∀ g v, f (specialLinearNatural 3 g v) = specialLinearNatural 3 (α g) (f v)) :
    ∃ σ : F ≃+* F, ∀ c v, f (c • v) = σ c • f v := by
  let q (c : F) : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => f (c • f.symm v)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hq (c : F) : ∃ d : F, ∀ v, q c v = d • v := by
    apply SL3OddNaturalNormalizer.centralizer_scalar
    intro g v
    have hi : f.symm (specialLinearNatural 3 g v) =
        specialLinearNatural 3 (α.symm g) (f.symm v) := by
      apply f.injective
      rw [f.apply_symm_apply, hf, α.apply_symm_apply, f.apply_symm_apply]
    change f (c • f.symm (specialLinearNatural 3 g v)) =
      specialLinearNatural 3 g (f (c • f.symm v))
    rw [hi, ← (specialLinearNatural 3 (α.symm g)).map_smul, hf, α.apply_symm_apply]
  let φ : F → F := fun c => q c (Pi.single 0 1) 0
  have hφ (c : F) (v : Fin 3 → F) : q c v = φ c • v := by
    obtain ⟨d,hd⟩ := hq c
    have he : φ c = d := by simp [φ,hd]
    exact he ▸ hd v
  have hmul (a b : F) (v : Fin 3 → F) : q (a*b) v = q a (q b v) := by
    simp [q,mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ,q]
      map_mul' := by
        intro a b
        change q (a*b) (Pi.single 0 1) 0 = φ a * φ b
        rw [hmul,hφ,hφ]
        simp
      map_zero' := by simp [φ,q]
      map_add' := by intro a b; simp [φ,q,add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective,Finite.surjective_of_injective φhom.injective⟩,fun c v => ?_⟩
  have he := hφ c (f v)
  change f (c • v) = φhom c • f v
  simpa only [q,AddMonoidHom.coe_mk,ZeroHom.coe_mk,f.symm_apply_apply,φhom,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk] using he

variable [Algebra (ZMod 2) F]

/-- A nonidentity semilinear operator on the three-dimensional space fixes at most |F|² vectors. -/
theorem fixed_card_le_of_semilinear
    (f : (Fin 3 → F) ≃+ (Fin 3 → F)) (hne : f ≠ AddEquiv.refl _)
    (σ : F ≃+* F) (hf : ∀ c v, f (c • v) = σ c • f v) :
    Nat.card {v : Fin 3 → F // f v = v} ≤ Nat.card F ^ 2 := by
  let t := f.toAddMonoidHom.toZModLinearMap 2
  let D := LinearMap.range (t - 1)
  let Z := LinearMap.ker (t - 1)
  let m := Module.finrank (ZMod 2) F
  have hdim : Module.finrank (ZMod 2) (Fin 3 → F) = 3*m := by
    simp [Module.finrank_pi_fintype,m]
  have hsum : Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) Z = 3*m := by
    simpa only [hdim] using (t-1).finrank_range_add_finrank_ker
  have hlower : m ≤ Module.finrank (ZMod 2) D := by
    by_cases hσ : ∃ a, σ a ≠ a
    · have hb := BinaryOffender.NaturalTensor.finrank_le_twice_operatorFixedCodim
        t σ.toRingHom hσ hf
      change Module.finrank (ZMod 2) (Fin 3 → F) ≤ 2*Module.finrank (ZMod 2) D at hb
      rw [hdim] at hb
      omega
    · push Not at hσ
      let δ : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
        { toFun := fun v => f v-v
          map_add' := by intro x y; simp only [map_add]; abel
          map_smul' := by intro a v; simp only [hf,hσ,smul_sub]; rfl }
      have he : Module.finrank (ZMod 2) D = m * Module.finrank F δ.range := by
        change Module.finrank (ZMod 2) (δ.restrictScalars (ZMod 2)).range = _
        rw [LinearMap.range_restrictScalars]
        have he := ((Submodule.restrictScalarsEquiv (ZMod 2) F (Fin 3 → F) δ.range).restrictScalars
          (ZMod 2)).finrank_eq
        rw [he, ← Module.finrank_mul_finrank (ZMod 2) F δ.range]
      have hδ : δ ≠ 0 := by
        intro hz
        apply hne
        apply AddEquiv.ext
        intro v
        exact sub_eq_zero.mp (congrArg (fun l : (Fin 3 → F) →ₗ[F] (Fin 3 → F) => l v) hz)
      have hp : 0 < Module.finrank F δ.range := by
        by_contra! hz
        exact hδ (LinearMap.range_eq_bot.mp
          (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz)))
      rw [he]
      exact Nat.le_mul_of_pos_right _ hp
  have hz : Module.finrank (ZMod 2) Z ≤ 2*m := by omega
  let e : {v : Fin 3 → F // f v = v} ≃ Z :=
    { toFun := fun v => ⟨v,sub_eq_zero.mpr v.property⟩
      invFun := fun v => ⟨v,sub_eq_zero.mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  calc
    2^Module.finrank (ZMod 2) Z ≤ 2^(2*m) := Nat.pow_le_pow_right (by decide) hz
    _ = Nat.card F^2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F),Nat.card_zmod,←pow_mul]
      congr 1
      exact Nat.mul_comm _ _

/-- The fixed-space bound for the full additive normalizer of the marked natural action. -/
theorem fixed_card_le_of_intertwines
    (f : (Fin 3 → F) ≃+ (Fin 3 → F)) (hne : f ≠ AddEquiv.refl _)
    (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hf : ∀ g v, f (specialLinearNatural 3 g v) = specialLinearNatural 3 (α g) (f v)) :
    Nat.card {v : Fin 3 → F // f v = v} ≤ Nat.card F ^ 2 := by
  obtain ⟨σ,hσ⟩ := semilinear_of_intertwines f α hf
  exact fixed_card_le_of_semilinear f hne σ hσ
end Representation.SL3NaturalFixed
end
