module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.MovedHead
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.IsPerfect

/-!
# Detection of perfect commuting actions on the canonical head

An endomorphism of a finite module whose image lies in the module radical is
nilpotent. Indeed, Fitting's argument makes the kernel and image of a high
power generate the module. If that kernel were proper, a maximal submodule
containing it would also contain the radical, contradicting generation.

Apply this to each commuting operator minus the identity. Triviality on the
canonical head puts its image in the radical. In characteristic two, nilpotence
then makes the operator have two-power order. The finite action image is thus
a two-group; if the actor is perfect, this image is trivial.

For the actual second component, this contradicts its nontrivial action on
the original moved space. No flag or bound on the number of factors is needed.

Source: Aschbacher–Smith, B.5.9, printed p.108, the centralizer assertion
for c = 2 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
set_option backward.isDefEq.respectTransparency false

namespace Head

private theorem nilpotent_of_range_le_radical
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsCoatomic (Submodule R M)]
    (f : Module.End R M) (hf : LinearMap.range f ≤ Module.jacobson R M) :
    IsNilpotent f := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_codisjoint_ker_pow_range_pow
  have hcod := (hn (n + 1) (Nat.le_succ n)).eq_top
  have hr : LinearMap.range (f ^ (n + 1)) ≤ Module.jacobson R M := by
    rintro _ ⟨x, rfl⟩
    rw [pow_succ', Module.End.mul_apply]
    exact hf (LinearMap.mem_range_self f _)
  have hk : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
    rcases eq_top_or_exists_le_coatom (LinearMap.ker (f ^ (n + 1))) with h | ⟨N, hN, hle⟩
    · exact h
    · have ht : (⊤ : Submodule R M) ≤ N := by
        rw [← hcod]
        exact sup_le hle (hr.trans (sInf_le hN))
      exact (hN.ne_top (top_le_iff.mp ht)).elim
  exact ⟨n + 1, LinearMap.ker_eq_top.mp hk⟩

variable {P Q W : Type*} [Group P] [Group Q]
  [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]

private theorem exists_two_power (τ : Representation (ZMod 2) P W)
    (σ : Representation (ZMod 2) Q W) (hc : ∀ p q, τ p * σ q = σ q * τ p)
    (h : action τ σ hc = 1) (q : Q) : ∃ n : ℕ, σ q ^ 2 ^ n = 1 := by
  classical
  cases subsingleton_or_nontrivial W with
  | inl hs => exact ⟨0, Subsingleton.elim _ _⟩
  | inr hn =>
    let : Nontrivial τ.asModule := τ.asModuleEquiv.toEquiv.nontrivial
    let : Finite τ.asModule := Module.finite_of_finite (ZMod 2)
    let : IsArtinian (ZMod 2)[P] τ.asModule := isArtinian_of_finite
    let t : IntertwiningMap τ τ := ⟨σ q, fun p => (hc p q).symm⟩
    let a := IntertwiningMap.equivAlgEnd τ t
    have ha : LinearMap.range (a - 1) ≤ Module.jacobson (ZMod 2)[P] τ.asModule := by
      rintro _ ⟨w, rfl⟩
      exact (action_eq_one_iff τ σ hc).mp h q w
    obtain ⟨n, hn⟩ := nilpotent_of_range_le_radical (a - 1) ha
    let : CharP (Module.End (ZMod 2)[P] τ.asModule) 2 :=
      CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) _) 2 (by decide)
    have hp : a ^ 2 ^ n = 1 := by
      have hz := pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))) hn
      rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right a), one_pow,
        sub_eq_zero] at hz
      exact hz
    have hpow (k : ℕ) (w : W) :
        τ.asModuleEquiv ((a ^ k) (τ.asModuleEquiv.symm w)) = (σ q ^ k) w := by
      induction k with
      | zero => exact τ.asModuleEquiv.apply_symm_apply w
      | succ k ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
        change σ q (τ.asModuleEquiv ((a ^ k) (τ.asModuleEquiv.symm w))) = _
        rw [ih]
    refine ⟨n, ?_⟩
    ext w
    simpa only [hpow, Module.End.one_apply, LinearEquiv.apply_symm_apply] using
      congrArg (fun b : Module.End (ZMod 2)[P] τ.asModule =>
        τ.asModuleEquiv (b (τ.asModuleEquiv.symm w))) hp

/-- The canonical head detects a finite perfect commuting action. -/
theorem eq_one_of_action_eq_one [Finite Q] [Group.IsPerfect Q]
    (τ : Representation (ZMod 2) P W) (σ : Representation (ZMod 2) Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (h : action τ σ hc = 1) : σ = 1 := by
  let a := σ.asGroupHom
  have hp : IsPGroup 2 a.range := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨x, q, rfl⟩
    obtain ⟨n, hn⟩ := exists_two_power τ σ hc h q
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hn
  let : Finite a.range := Finite.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  let : Group.IsNilpotent a.range := hp.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  apply MonoidHom.ext
  intro q
  exact congrArg (fun x : a.range => (x.val : Module.End (ZMod 2) W))
    (hs.elim (a.rangeRestrict q) 1)

end Head

open Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The actual second component acts nontrivially on the first component's head. -/
theorem secondHead_ne_one {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) : secondHead ρ hL d ≠ 1 := by
  let : Group.IsPerfect d.second := d.isComponent.2.toIsPerfect
  intro h
  exact movedAction_ne_one ρ hL d
    (Head.eq_one_of_action_eq_one (componentAction ρ L) (secondAction ρ hL d)
      (moved_commute ρ hL d) h)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
