module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Schur endomorphisms from common binary displacements

Suppose a faithful elementary abelian two-group commutes with a representation,
and every nonidentity actor has the same displacement image I and kernel K.
A fixed nonzero displacement identifies V/K with I. Every other displacement
therefore descends to an equivariant endomorphism of I. The fixed displacement
squares to zero, so I lies in K and all pairwise displacement products vanish.
Consequently descent is additive and faithful, embedding the actor in End(I).

This is the linear rank argument used in the marked homogeneous branch of
Aschbacher--Smith G.10--11, printed pp.360,368--369. It requires neither a
complementary simple copy nor a semisimplicity hypothesis. The original terminal
A₆ application is SmallRows.AlternatingSixActionSourceMultiplicityRank.
-/

public noncomputable section
open Representation Module
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {A H V : Type*} [Group A] [IsElementaryAbelian 2 A]
  [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Common displacement images and kernels give a faithful additive action
in the endomorphisms of the common image. -/
theorem exists_injective_schur_displacement
    (ρ : Representation (ZMod 2) A V) (τ : Representation (ZMod 2) H V)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a h v, ρ a (τ h v) = τ h (ρ a v))
    (I : Subrepresentation τ) (K : Submodule (ZMod 2) V)
    (hdata : ∀ a : A, a ≠ 1 →
      LinearMap.range (ρ a - LinearMap.id) = I.toSubmodule ∧
      LinearMap.ker (ρ a - LinearMap.id) = K) :
    ∃ f : Additive A →ₗ[ZMod 2] IntertwiningMap I.toRepresentation I.toRepresentation,
      Function.Injective f := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let := h
    exact ⟨0, fun _ _ _ => Subsingleton.elim _ _⟩
  | inr h =>
    let := h
    obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
    let d (a : A) : V →ₗ[ZMod 2] V := ρ a - LinearMap.id
    have d_one : d 1 = 0 := by ext v; simp [d]
    have hr (a : A) : LinearMap.range (d a) ≤ I.toSubmodule := by
      by_cases ha : a = 1
      · subst a; simp [d_one]
      · exact (hdata a ha).1.le
    have hk (a : A) : K ≤ LinearMap.ker (d a) := by
      by_cases ha : a = 1
      · subst a; simp [d_one]
      · exact (hdata a ha).2.ge
    have hsq (v : V) : d a₀ (d a₀ v) = 0 := by
      have ha : a₀ * a₀ = 1 := by
        simpa only [pow_two] using
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) a₀
      have he : ρ a₀ (ρ a₀ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, ha, map_one, Module.End.one_apply]
      simp only [d, LinearMap.sub_apply, LinearMap.id_apply, map_sub, he]
      simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
      calc
        _ = (v + v) + (ρ a₀ v + ρ a₀ v) := by abel
        _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]
    have hIK : I.toSubmodule ≤ K := by
      rw [← (hdata a₀ ha₀).1, ← (hdata a₀ ha₀).2]
      rintro _ ⟨v, rfl⟩
      exact hsq v
    have hfix (a b : A) (v : V) : ρ a (d b v) = d b v := by
      apply sub_eq_zero.mp
      exact hk a (hIK (hr b ⟨v,rfl⟩))
    have hadd (a b : A) (v : V) : d (a*b) v = d a v + d b v := by
      change ρ (a*b) v - v = (ρ a v - v) + (ρ b v - v)
      calc
        ρ (a*b) v - v = ρ a ((ρ b v - v) + v) - v := by
          simp [map_mul, Module.End.mul_apply]
        _ = (ρ b v - v) + (ρ a v - v) := by
          rw [map_add, show ρ a (ρ b v - v) = ρ b v - v from hfix a b v]
          abel
        _ = (ρ a v - v) + (ρ b v - v) := add_comm _ _
    let q (a : A) : V →ₗ[ZMod 2] I.toSubmodule :=
      (d a).codRestrict I.toSubmodule (fun v => hr a ⟨v,rfl⟩)
    have hq (a : A) (g : H) (v : V) : q a (τ g v) = I.toRepresentation g (q a v) := by
      apply Subtype.ext
      change ρ a (τ g v) - τ g v = τ g (ρ a v - v)
      rw [map_sub,hcomm]
    have hp : Function.Surjective (q a₀) := by
      intro v
      obtain ⟨w,hw⟩ := (hdata a₀ ha₀).1.ge v.property
      exact ⟨w, Subtype.ext hw⟩
    have hker (a : A) : (q a₀).ker ≤ (q a).ker := by
      intro v hv
      have hv' : v ∈ K := by
        rw [← (hdata a₀ ha₀).2]
        exact congrArg Subtype.val (show q a₀ v = 0 from hv)
      apply Subtype.ext
      exact hk a hv'
    let e := (q a₀).quotKerEquivOfSurjective hp
    let D (a : A) : I.toSubmodule →ₗ[ZMod 2] I.toSubmodule :=
      ((q a₀).ker.liftQ (q a) (hker a)).comp e.symm.toLinearMap
    have hD (a : A) (v : V) : D a (q a₀ v) = q a v := by
      change ((q a₀).ker.liftQ (q a) (hker a)) (e.symm (q a₀ v)) = q a v
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
      rfl
    let F (a : A) : IntertwiningMap I.toRepresentation I.toRepresentation := {
      toLinearMap := D a
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        obtain ⟨w,rfl⟩ := hp v
        change D a (I.toRepresentation g (q a₀ w)) = I.toRepresentation g (D a (q a₀ w))
        rw [← hq, hD, hD, hq] }
    have hF (a : A) (v : V) : F a (q a₀ v) = q a v := hD a v
    let f : Additive A →+ IntertwiningMap I.toRepresentation I.toRepresentation := {
      toFun := fun a => F a.toMul
      map_zero' := by
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        obtain ⟨w,rfl⟩ := hp v
        change F 1 (q a₀ w) = 0
        rw [hF]
        apply Subtype.ext
        exact LinearMap.congr_fun d_one w
      map_add' := by
        intro a b
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        obtain ⟨w,rfl⟩ := hp v
        change F (a.toMul * b.toMul) (q a₀ w) = F a.toMul (q a₀ w) + F b.toMul (q a₀ w)
        rw [hF,hF,hF]
        apply Subtype.ext
        exact hadd a.toMul b.toMul w }
    refine ⟨f.toZModLinearMap 2, ?_⟩
    intro a b hab
    apply Additive.toMul.injective
    apply hfaith
    ext v
    have he := congrArg (fun t : IntertwiningMap I.toRepresentation I.toRepresentation =>
      t (q a₀ v)) hab
    change F a.toMul (q a₀ v) = F b.toMul (q a₀ v) at he
    rw [hF,hF] at he
    have he' : ρ a.toMul v - v = ρ b.toMul v - v := congrArg Subtype.val he
    simpa only [sub_add_cancel] using congrArg (fun w : V => w + v) he'
end Representation.BinaryOffender
