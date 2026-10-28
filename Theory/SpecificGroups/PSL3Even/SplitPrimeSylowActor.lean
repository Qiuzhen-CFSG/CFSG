module

public import Theory.SpecificGroups.PSL3.CartanActions
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.SylowPrimeActors

/-!
# Split-prime actors on the original linear Sylow group

The projective image of diag(a,a⁻¹,1) has coordinate weights (a²,a⁻¹,a) on
UT₃(F). It moves the highest-root commutator whenever a is nontrivial. In
characteristic two all three weights are nontrivial, so its fixed subgroup in
UT₃(F) is trivial. Cauchy's theorem selects a parameter of each prime order
p dividing |F|−1; central two-kernel lifting then supplies an actor of exactly
that order on every specified Sylow subgroup of a genuine cover.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, proof of
2.5.7, printed p.556. The actual Chapter 2 application is in
ComponentSelection/SplitPrimeTorusSource.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3Even.UnipotentGeometry.SplitPrimeActor
open Matrix.PSL3 Matrix.PSL3.CartanActions Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]
def torusParameter : Fˣ →* (Fˣ × Fˣ) where
  toFun a := (a, 1)
  map_one' := rfl
  map_mul' a b := by simp

def actorHom : Fˣ →* PSL(3,F) := (torusMap F).comp (torusParameter F)

theorem weights (a : Fˣ) (u : U F) :
    actorHom F a * projective F u * (actorHom F a)⁻¹ =
      projective F ⟨(a:F)^2*u.x, ((a⁻¹:Fˣ):F)*u.y, (a:F)*u.c⟩ := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  have h : torusSL F (a,1) * specialLinear F u =
      specialLinear F ⟨(a:F)^2*u.x, ((a⁻¹:Fˣ):F)*u.y, (a:F)*u.c⟩ * torusSL F (a,1) := by
    apply Subtype.ext
    change diagonal _ * matrix F u = matrix F _ * diagonal _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.diagonal_mul, Matrix.mul_diagonal, pow_two,
        mul_assoc, mul_left_comm, mul_comm]
    field_simp
  simpa only [map_mul, actorHom, torusMap, torusParameter, projective, projection,
    MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk] using congrArg (projection F) h

theorem highest_root_commutator :
    ⁅(⟨1,0,0⟩ : U F), ⟨0,1,0⟩⁆ = (⟨0,0,1⟩ : U F) := by
  apply U.ext <;> simp [commutatorElement_def, Inv.inv]

theorem actor_ne_one (a : Fˣ) (ha : a ≠ 1) : actorHom F a ≠ 1 := by
  intro h
  have hw := weights F a (⟨0,0,1⟩ : U F)
  rw [h, one_mul, inv_one, mul_one] at hw
  have he := congrArg U.c ((projective_injective F) hw)
  have ha1 : (a:F) = 1 := by simpa using he.symm
  exact ha (Units.ext ha1)

theorem highest_root_mem_derived :
    projective F (⟨0,0,1⟩ : U F) ∈ ⁅unipotent F, unipotent F⁆ := by
  rw [←highest_root_commutator F, map_commutatorElement]
  exact commutator_mem_commutator ((projective_range F).le ⟨_,rfl⟩)
    ((projective_range F).le ⟨_,rfl⟩)

theorem actor_moves_derived (a : Fˣ) (ha : a ≠ 1) :
    actorHom F a ∉ centralizer ((⁅unipotent F, unipotent F⁆ : Subgroup PSL(3,F)) : Set PSL(3,F)) := by
  intro hc
  have hh := hc _ (highest_root_mem_derived F)
  have hw := weights F a (⟨0,0,1⟩ : U F)
  rw [←hh, mul_inv_cancel_right] at hw
  have he := congrArg U.c ((projective_injective F) hw)
  exact ha (Units.ext (by simpa using he.symm))

variable [CharP F 2]
theorem fixed_eq_one (a : Fˣ) (ha : a ≠ 1) (u : U F)
    (hc : Commute (actorHom F a) (projective F u)) : u = 1 := by
  have hw := weights F a u
  rw [hc.eq, mul_inv_cancel_right] at hw
  have he := (projective_injective F) hw
  have ha1 : (a:F) ≠ 1 := fun h => ha (Units.ext h)
  have ha2 : (a:F)^2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h|h
    · exact ha1 h
    · exact ha1 (by simpa only [CharTwo.neg_eq] using h)
  have hai : ((a⁻¹:Fˣ):F) ≠ 1 := by
    intro h
    have hh : a⁻¹ = (1:Fˣ) := Units.ext h
    exact ha (inv_eq_one.mp hh)
  apply U.ext
  · have h := congrArg U.x he
    change u.x = (a:F)^2*u.x at h
    have hh : ((a:F)^2-1)*u.x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha2)
  · have h := congrArg U.y he
    change u.y = ((a⁻¹:Fˣ):F)*u.y at h
    have hh : (((a⁻¹:Fˣ):F)-1)*u.y = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hai)
  · have h := congrArg U.c he
    change u.c = (a:F)*u.c at h
    have hh : ((a:F)-1)*u.c = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha1)
variable [Finite F]
theorem standard_prime_actor {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    ∃ X : Subgroup PSL(3,F), Nat.card X = p ∧
      X ≤ normalizer (unipotent F : Set PSL(3,F)) ∧
      ¬ X ≤ centralizer ((⁅unipotent F, unipotent F⁆ : Subgroup PSL(3,F)) : Set PSL(3,F)) ∧
      unipotent F ⊓ centralizer (X : Set PSL(3,F)) = ⊥ := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (by simpa only [Nat.card_units] using hd : p ∣ Nat.card Fˣ)
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  have ht : (actorHom F a)^p = 1 := by
    rw [←map_pow, ←ha, pow_orderOf_eq_one, map_one]
  have hord : orderOf (actorHom F a) = p :=
    orderOf_eq_prime ht (actor_ne_one F a ha1)
  refine ⟨zpowers (actorHom F a), ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hord]
  · apply zpowers_le.mpr
    exact borel_le_normalizer_unipotent F (torus_le_borel F ⟨(a,1),rfl⟩)
  · exact fun h => actor_moves_derived F a ha1 (h (mem_zpowers _))
  · apply bot_unique
    intro y hy
    change y=1
    obtain ⟨u,rfl⟩ := (projective_range F).ge hy.1
    have hu : u = 1 := fixed_eq_one F a ha1 u (hy.2 _ (mem_zpowers _))
    rw [hu,map_one]



variable {E : Type*} [Group E] [Finite E]
/-- The actual split-prime actor on every central two-cover and every original Sylow. -/
theorem prime_actor_on_cover
    (α : E →* PSL(3,F)) (hα : Function.Surjective α)
    (h2 : IsPGroup 2 α.ker) (hc : α.ker ≤ center E)
    {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ 2^n-1) (S : Sylow 2 E) :
    ∃ X : Subgroup E, Nat.card X=p ∧ X ≤ normalizer (S : Set E) ∧
      ¬ X ≤ centralizer ((⁅(S : Subgroup E),(S : Subgroup E)⁆ : Subgroup E) : Set E) ∧
      (S : Subgroup E) ⊓ centralizer (X : Set E) = α.ker := by
  obtain ⟨β,hβ,hker,hS⟩ := exists_sylow_aligned_map α hα S (unipotentSylow F hn hF)
  change (S : Subgroup E).map β=unipotent F at hS
  have hb2 : IsPGroup 2 β.ker := by rw [hker]; exact h2
  have hbc : β.ker ≤ center E := by rw [hker]; exact hc
  obtain ⟨A,hA,hN,hm,hfix⟩ := standard_prime_actor F (hF ▸ hd)
  obtain ⟨X,hX,hcard,hXN,hmove⟩ := lift_odd_sylow_actor β hβ hb2 hbc S A
    (hA ▸ ho) (hS.symm ▸ hN) (by simpa only [hS] using hm)
  refine ⟨X,hcard.trans hA,hXN,hmove,?_⟩
  rw [←hker]
  apply sylow_centralizer_eq_kernel_of_image β hb2 hbc S X
  rw [hS,hX]
  exact hfix

end Matrix.PSL3Even.UnipotentGeometry.SplitPrimeActor
