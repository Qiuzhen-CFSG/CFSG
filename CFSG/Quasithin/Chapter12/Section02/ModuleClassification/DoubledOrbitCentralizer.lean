module

public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer
public import Theory.Representation.CentralizerField
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleOddActor

/-!
# The two-core on a pair of different simple constituents

Schur's lemma kills the off-diagonal blocks of a commuting operator on two
nonisomorphic irreducible binary modules. Each diagonal endomorphism field
has an odd number of units, so a commuting operator of two-power order is
trivial. A normal two-core centralizes a normal quasisimple component;
transport through the actual pair coordinates therefore kills that core.

The consumer in DoubledOrbitOffenders applies this calculation to the
literal doubled orbit in 12.2.2, without imposing Irr⁺ on the whole orbit.
Source: Aschbacher--Smith, B.5.1 and D.3.10, printed pp.99--103 and 201,
using Schur's lemma and the finite endomorphism-field argument of A.1.41.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
variable {P U Z : Type*} [Group P] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  (α : Representation (ZMod 2) P U) (β : Representation (ZMod 2) P Z)
  [IsIrreducible α] [IsIrreducible β]

private theorem cross_eq_zero (hne : ¬ Nonempty (α.Equiv β))
    (f : α.IntertwiningMap β) : f = 0 :=
  (IsIrreducible.bijective_or_eq_zero f).resolve_left fun hf => hne ⟨f.ofBijective hf⟩

private theorem end_eq_one_of_two_power [Module.Finite (ZMod 2) U]
    (f : α.IntertwiningMap α) (r : ℕ) (hf : f ^ 2 ^ r = 1) : f = 1 := by
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one hf (by positivity : 2 ^ r ≠ 0)
  have hp : u ^ 2 ^ r = 1 := Units.ext hf
  have ho := CentralizerField.units_odd_card α
  have hu : u = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_right.pow_right r) (orderOf_dvd_natCard u)
    (orderOf_dvd_of_pow_eq_one hp))
  exact congrArg Units.val hu

/-- A commuting operator cannot mix two nonisomorphic irreducible summands. -/
theorem commuting_pair_diagonal (hne : ¬ Nonempty (α.Equiv β))
    (f : Module.End (ZMod 2) (U × Z))
    (hc : ∀ g v, f ((α.prod β) g v) = (α.prod β) g (f v)) :
    ∀ u z, f (u,z) = ((f (u,0)).1, (f (0,z)).2) := by
  let a : α.IntertwiningMap β :=
    ⟨(LinearMap.snd _ _ _).comp (f.comp (LinearMap.inl _ _ _)), fun g => by
      apply LinearMap.ext
      intro u
      have h := congrArg Prod.snd (hc g (u,0))
      change (f (α g u, β g 0)).2 = β g (f (u,0)).2 at h
      simpa only [map_zero, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply] using h⟩
  let b : β.IntertwiningMap α :=
    ⟨(LinearMap.fst _ _ _).comp (f.comp (LinearMap.inr _ _ _)), fun g => by
      apply LinearMap.ext
      intro z
      have h := congrArg Prod.fst (hc g (0,z))
      change (f (α g 0, β g z)).1 = α g (f (0,z)).1 at h
      simpa only [map_zero, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply] using h⟩
  have ha := cross_eq_zero α β hne a
  have hb := cross_eq_zero β α (fun ⟨e⟩ => hne ⟨e.symm⟩) b
  intro u z
  have hfa : (f (u,0)).2 = 0 := DFunLike.congr_fun ha u
  have hfb : (f (0,z)).1 = 0 := DFunLike.congr_fun hb z
  have hs : f (u,z) = f (u,0) + f (0,z) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using f.map_add (u,0) (0,z)
  rw [hs]
  exact Prod.ext (by simp only [Prod.fst_add, hfb, add_zero])
    (by simp only [Prod.snd_add, hfa, zero_add])

/-- A two-power-order operator centralizing a multiplicity-free pair is trivial. -/
theorem commuting_pair_two_power_eq_one
    [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) Z]
    (hne : ¬ Nonempty (α.Equiv β))
    (f : Module.End (ZMod 2) (U × Z))
    (hc : ∀ g v, f ((α.prod β) g v) = (α.prod β) g (f v))
    (r : ℕ) (hp : f ^ 2 ^ r = 1) : f = 1 := by
  have hd := commuting_pair_diagonal α β hne f hc
  let a : α.IntertwiningMap α :=
    ⟨(LinearMap.fst _ _ _).comp (f.comp (LinearMap.inl _ _ _)), fun g => by
      apply LinearMap.ext
      intro u
      have h := congrArg Prod.fst (hc g (u,0))
      change (f (α g u, β g 0)).1 = α g (f (u,0)).1 at h
      simpa only [map_zero, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply] using h⟩
  let b : β.IntertwiningMap β :=
    ⟨(LinearMap.snd _ _ _).comp (f.comp (LinearMap.inr _ _ _)), fun g => by
      apply LinearMap.ext
      intro z
      have h := congrArg Prod.snd (hc g (0,z))
      change (f (α g 0, β g z)).2 = β g (f (0,z)).2 at h
      simpa only [map_zero, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply] using h⟩
  have hpow (m : ℕ) (u : U) (z : Z) :
      (f ^ m) (u,z) = ((a ^ m) u, (b ^ m) z) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', pow_succ', pow_succ', Module.End.mul_apply, ih, hd]
      rfl
  have ha : a ^ 2 ^ r = 1 := by
    apply DFunLike.ext
    intro u
    have h := congrArg Prod.fst (hpow (2^r) u 0)
    rw [hp] at h
    exact h.symm
  have hb : b ^ 2 ^ r = 1 := by
    apply DFunLike.ext
    intro z
    have h := congrArg Prod.snd (hpow (2^r) 0 z)
    rw [hp] at h
    exact h.symm
  have ha1 := end_eq_one_of_two_power α a r ha
  have hb1 := end_eq_one_of_two_power β b r hb
  apply LinearMap.ext
  rintro ⟨u,z⟩
  rw [hd]
  exact Prod.ext (DFunLike.congr_fun ha1 u) (DFunLike.congr_fun hb1 z)
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

open Subgroup Theory.GroupTheory
open Representation.BinaryOffender Representation.BinaryOffender.QuasisimpleNormalizer
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
variable {P H U Z W : Type*} [Group P] [Group H] [Finite H]
  [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
  [AddCommGroup Z] [Module (ZMod 2) Z] [Module.Finite (ZMod 2) Z]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The two-core vanishes on a faithful action with two different simple
component constituents. The marking retains the map to the actual component. -/
theorem twoCore_eq_bot_of_pair
    (ρ : Representation (ZMod 2) H W) (hf : Function.Injective ρ)
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (q : P →* K) (α : Representation (ZMod 2) P U)
    (β : Representation (ZMod 2) P Z) [IsIrreducible α] [IsIrreducible β]
    (hne : ¬ Nonempty (α.Equiv β)) (e : W ≃ₗ[ZMod 2] (U × Z))
    (he : ∀ g w, e (ρ (q g) w) = (α.prod β) g (e w)) :
    pCore 2 H = ⊥ := by
  have hs : componentLayer K = ⊤ := by
    apply top_unique
    exact le_sSup (show IsComponent K ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hc := twoCore_centralizes_of_normal_layer_or_odd K (Or.inl hs)
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply hf
  let f := (e.conjAlgEquiv (ZMod 2)) (ρ x)
  have hfc : ∀ g v, f ((α.prod β) g v) = (α.prod β) g (f v) := by
    intro g v
    have hi : e.symm ((α.prod β) g v) = ρ (q g) (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    change e (ρ x (e.symm ((α.prod β) g v))) = _
    rw [hi]
    have hxq : x * (q g : H) = (q g : H) * x :=
      (mem_centralizer_iff.mp (hc hx) (q g) (q g).property).symm
    rw [← Module.End.mul_apply, ← map_mul, hxq, map_mul, Module.End.mul_apply, he]
    rfl
  obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨x,hx⟩
  have hr' : x ^ 2 ^ r = 1 := congrArg Subtype.val hr
  have hp : f ^ 2 ^ r = 1 := by
    rw [← map_pow, ← map_pow, hr', map_one, map_one]
  have hf1 := commuting_pair_two_power_eq_one α β hne f hfc r hp
  apply (e.conjAlgEquiv (ZMod 2)).injective
  simpa only [map_one] using hf1
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
