module
public import Theory.SpecificGroups.SU3.QuinticSylowFixer
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.AllPrimes

/-!
# Quintic root displacement in the projective ternary unitary group

A Sylow-fixing projective involution is inner and is conjugate to the
marked sign involution. Lift its conjugator through the literal SU₃→PSU₃
map and use the existing exponent-five extraspecial root of order 125.
That root embeds in the projective quotient: a kernel element has both
cube and fifth power one, so is trivial. Its actual nontrivial involutory
action therefore forces displacement at least eight on every faithful
binary ambient representation.

The same ambient actor, group embedding, Hermitian form and scalar quotient
are retained. Source: Aschbacher–Smith 12.6.26, printed p.832, using the
quintic displacement calculation of G.7.1(2).
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylowFixer
open OddPrimeSylow.NormalizedOuter.Coverage
open OddPrimeSylow.NormalizedOuter

/-- The faithful projective model retains the exponent-five root group and forces displacement eight. -/
theorem eight_le_projective_displacement_of_sylow_fixer
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hF : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (j : ProjectiveSpecialUnitaryMatrixGroup J →* D) (hj : Function.Injective j)
    (t : D) (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : orderOf a = 2)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (hP : ∀ x ∈ P, a x = x)
    (heq : ∀ x, j (a x) = t * j x * t⁻¹) :
    8 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1
      (by decide) (by simpa using hF) (by simpa using hc)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 5 hF hf
  let J₀ := FormTransport.standardForm J
  let B := ProjectiveSpecialUnitaryMatrixGroup J₀
  let : DivisionMonoid B := @Group.toDivisionMonoid _ inferInstance
  let : IsSimpleGroup B := e.symm.isSimpleGroup
  let := J₀.projective_isPerfect_of_fixed_card (by decide : 2 < 5) hF hf
  let a₀ := MulAut.congr e a
  let P₀ := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have ha₀ : orderOf a₀ = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hP₀ : ∀ x ∈ P₀, a₀ x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hP x hx]
  let j₀ : B →* D := j.comp e.symm.toMonoidHom
  have hj₀ : Function.Injective j₀ := hj.comp e.symm.injective
  have heq₀ (x : B) : j₀ (a₀ x) = t * j₀ x * t⁻¹ := by
    change j (e.symm (e (a (e.symm x)))) = _
    rw [e.symm_apply_apply]
    exact heq _
  have hz : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz|hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
  obtain ⟨s,hs⟩ := OddPrimeSylow.inner_of_involutive_fixing_sylow J₀ (by decide) (by decide)
    hF hf P₀ a₀ (ha₀ ▸ pow_orderOf_eq_one a₀) hP₀
  have hso : orderOf s = 2 :=
    (orderOf_injective MulAut.conj (Theory.GroupTheory.conj_injective_of_center_eq_bot hz) s).symm.trans
      (hs ▸ ha₀)
  have h2 : (2:F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by decide : 5 ≠ 2)
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (InvolutionConjugateBounds.Inner.projective_involutions_isConj J₀ (by decide) (by decide)
      hF hc (hermitianTorusPSU J₀ rfl (-1)) s (torus_neg_orderOf J₀ rfl h2) hso)
  let q := J₀.specialToProjective
  obtain ⟨r,hr⟩ := J₀.specialToProjective_surjective g
  have hqs : q (r * hermitianTorusSU J₀ rfl (-1) * r⁻¹) = s := by
    have hqt : q (hermitianTorusSU J₀ rfl (-1)) = hermitianTorusPSU J₀ rfl (-1) := by
      apply Subtype.ext
      exact J₀.specialToProjective_apply_val _
    rw [map_mul,map_mul,map_inv,hr,hqt]
    exact hg
  obtain ⟨Y,hY,hYcard,hYexp,b,hb,hmove⟩ := sign_conjugate_moves_root J₀ rfl hF hf r
  let := hY
  let k : Y →* D := j₀.comp (q.comp Y.subtype)
  have hk : Function.Injective k := by
    apply k.ker_eq_bot_iff.mp
    apply bot_unique
    intro y hy
    have hqy : q y.val = 1 := hj₀ ((show k y = 1 from hy).trans j₀.map_one.symm)
    have h3 : y ^ 3 = 1 := Subtype.ext
      (congrArg (fun x : J₀.specialToProjective.ker => x.val)
        (J₀.specialToProjective_ker_cube ⟨y.val,hqy⟩))
    have hd : orderOf y ∣ 1 := Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one (hYexp y))
    have he : y ^ 1 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    change y = 1
    simpa only [pow_one] using he
  apply Representation.ExtraspecialQuinticActor.eight_le_displacement_of_movement ρ hρ k hk
    hYcard hYexp t b hb
  intro y
  change j₀ (q (b y).val) = _
  have hqmove : q (b y).val = s * q y.val * s⁻¹ := by
    rw [hmove,map_mul,map_mul,map_inv,hqs]
  rw [hqmove]
  change j₀ ((MulAut.conj s) (q y.val)) = _
  rw [←hs]
  exact heq₀ _
end BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylowFixer
