module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import Mathlib.Algebra.CharP.Reduced

/-!
# The unitary overlap calculation for the enlarged generic cores

In the full degree-two unitary overlap, every normal two-subgroup has
trivial outer parity. Indeed, commuting an element of nontrivial parity
with a diagonal torus element gives an ordinary Borel element with first
diagonal entry σ(a)/a. Its two-power order forces that entry to be one
in characteristic two, contradicting the nontrivial field involution.
The compatible projective map preserves this calculation.

The generic application uses normality of O₂(GᵢT) in the whole overlap.
It does not assume normality of the original S there, or use the incorrect
identity O₂(B) = U⟨σ⟩ discussed in UnitaryFourExtension. Both odd Cartans
remain in the overlap. This supplies the missing containment for the
unitary enlarged-core identities in Aschbacher–Smith 5.2.7(3), printed
p.651, using the literal extension in F.1.12 and F.4.29 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourSylow
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryCore
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "B" => borelSU F J
local notation "E" => UnitaryFourOuter.overlap F σ hσ

private def ordinary : B →* E where
  toFun b := ⟨SemidirectProduct.inl b.val,b.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

omit [CharP F 2] in
private theorem ordinary_injective : Function.Injective (ordinary F σ hσ) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : E => x.val.left) h)

private theorem normal_two_subgroup_parity
    (hne : ∃ a : F, σ a ≠ a) (Q : Subgroup E) [Q.Normal]
    (hQ : IsPGroup 2 Q) (x : E) (hx : x ∈ Q) : x.val.right = 1 := by
  rcases UnitaryFourOuter.c2_cases x.val.right with he | he
  · exact he
  exfalso
  obtain ⟨a,ha⟩ := hne
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  let u : Fˣ := Units.mk0 a ha0
  let t : B := torusLift F σ hσ u 1
  let b : B := ⟨x.val.left,x.property⟩
  let t' : B := ⟨UnitaryFourOuter.matrixAut F σ hσ t.val,
    (UnitaryFourOuter.matrixAut_mem_point F σ hσ _).mpr t.property.1,
    (UnitaryFourOuter.matrixAut_mem_plane F σ hσ _).mpr t.property.2⟩
  let c : B := b * t' * b⁻¹ * t⁻¹
  let d := ordinary F σ hσ t
  have hc : ordinary F σ hσ c = x * d * x⁻¹ * d⁻¹ := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change x.val.left * UnitaryFourOuter.matrixAut F σ hσ t.val *
          x.val.left⁻¹ * t.val⁻¹ =
        (x.val * SemidirectProduct.inl t.val * x.val⁻¹ *
          (SemidirectProduct.inl t.val)⁻¹).left
      simp only [SemidirectProduct.mul_left,SemidirectProduct.mul_right,
        SemidirectProduct.inv_left,SemidirectProduct.inv_right,
        SemidirectProduct.left_inl,SemidirectProduct.right_inl,mul_one,
        map_one,MulAut.one_apply,he,UnitaryFourOuter.action_generator,
        map_inv,← MulAut.mul_apply,mul_inv_cancel]
    · simp [d,ordinary]
  have hcQ : c ∈ Q.comap (ordinary F σ hσ) := by
    change ordinary F σ hσ c ∈ Q
    rw [hc]
    have hh := Q.mul_mem hx ((inferInstance : Q.Normal).conj_mem x⁻¹ (Q.inv_mem hx) d)
    simpa only [mul_assoc] using hh
  obtain ⟨k,hk⟩ := (hQ.comap_of_injective (ordinary F σ hσ)
    (ordinary_injective F σ hσ)).exists_pow_pow_eq_one ⟨c,hcQ⟩
  have hcPow : c ^ (2^k) = 1 := congrArg Subtype.val hk
  let χ : B →* Fˣ := (MonoidHom.fst Fˣ (FixedField F σ)ˣ).comp (torusCharacter F σ hσ)
  have ht : (χ t : F) = a := by
    change ((torusCharacter F σ hσ t).1 : F) = a
    rw [torusCharacter_lift]
    rfl
  have ht' : (χ t' : F) = σ a := by
    change ((torusCharacter F σ hσ t').1 : F) = σ a
    rw [torusCharacter_fst_val]
    change σ (t.val.val.val 0 0) = σ a
    exact congrArg σ ((torusCharacter_fst_val F σ hσ t).symm.trans ht)
  have hcχ : (χ c : F) = σ a * a⁻¹ := by
    simp only [c,map_mul,map_inv,Units.val_mul,Units.val_inv_eq_inv_val,ht,ht']
    have hb : (χ b : F) ≠ 0 := (χ b).ne_zero
    field_simp
  have hp : (σ a * a⁻¹)^(2^k) = 1 := by
    have hh := congrArg (fun z : B => (χ z : F)) hcPow
    simpa only [map_pow,Units.val_pow_eq_pow_val,map_one,Units.val_one,hcχ] using hh
  have hh : σ a * a⁻¹ = 1 := by
    simpa only [Nat.mul_one,pow_one] using
      (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 (σ a * a⁻¹)).mp (by simpa using hp)
  exact ha ((mul_inv_eq_one₀ ha0).mp hh)

open ChapterF.GreenBook.LieModels.UnitaryFour

/-- A normal two-subgroup of the whole extended overlap has trivial parity. -/
theorem unitaryExtension_overlap_twoCore_parity (m : ℕ) (hm : 1 ≤ m)
    (x : Extension.overlap m hm) (hx : x ∈ pCore 2 (Extension.overlap m hm)) :
    x.val.right = 1 := by
  let e := (Extension.projectIso m hm).middle
  obtain ⟨y,rfl⟩ := e.surjective x
  have hh := normal_two_subgroup_parity (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) (PointLocal.fieldConj_nontrivial m hm)
    ((pCore 2 (Extension.overlap m hm)).comap e.toMonoidHom)
    (pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective) y hx
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryCore
