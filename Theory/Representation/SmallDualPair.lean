module
public import Theory.Representation.IrreduciblePairBound
public import Theory.Representation.IrreducibleDualBound
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# A simple pair in a small binary natural--dual module

Opposite simple embeddings into X and X* pair nondegenerately when their
dimensions sum to more than dim X. The pairing splits off the first simple
module. If the remaining dimension is at most two, a perfect binary actor
fixes the complement, so its kernel on that simple module fixes X.
For an embedded pair of inequivalent three-dimensional simples, coordinate
projections supply the opposite embeddings in every dimension at most five.

Source application: Aschbacher--Smith 10.2.9, printed p.752, exclusion of
the original natural--dual row inside containing natural--dual modules.
-/

public noncomputable section
namespace Representation.SmallDualPair
open Subgroup Theory.GroupTheory

private theorem small_linear_solvable (n : ℕ) (hn : n ≤ 2) :
    Group.IsSolvable (BinaryLinear.OuterCyclic.LinearGroup n) := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
      (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))) DFunLike.coe_injective
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hc : Nat.card (BinaryLinear.OuterCyclic.LinearGroup n) =
      ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
      Matrix.card_GL_field]
    simp
  rw [hc] at hd
  interval_cases n
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num [Fin.prod_univ_two] at hd
    rcases hp.dvd_mul.mp (show p ∣ 2*3 from hd) with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)

/-- Perfect groups act trivially on binary spaces of dimension at most two. -/
theorem trivial_of_finrank_le_two {H X : Type*} [Group H] [Group.IsPerfect H]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (σ : Representation (ZMod 2) H X) (hd : Module.finrank (ZMod 2) X ≤ 2) : σ = 1 := by
  let n := Module.finrank (ZMod 2) X
  let e := (Module.finBasis (ZMod 2) X).equivFun
  let a := LinearMap.GeneralLinearGroup.congrLinearEquiv e
  let b := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)
  let f := b.toMonoidHom.comp (a.toMonoidHom.comp σ.asGroupHom)
  let : Group.IsSolvable (BinaryLinear.OuterCyclic.LinearGroup n) := small_linear_solvable n hd
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.range := inferInstance
  have hz : f.range = ⊥ := by
    by_contra hn
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  let : Subsingleton f.range := by rw [hz]; infer_instance
  have hf (h : H) : f h = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f h,h,rfl⟩ : f.range) 1)
  ext h x
  have he : σ.asGroupHom h = 1 := (b.injective.comp a.injective) (by change b (a (σ.asGroupHom h)) = b (a 1); rw [map_one,map_one]; exact hf h)
  exact LinearMap.congr_fun (congrArg Units.val he) x

variable {H W Y X : Type*} [Group H] [Group.IsPerfect H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {ρ : Representation (ZMod 2) H W} {η : Representation (ZMod 2) H Y}
  {σ : Representation (ZMod 2) H X} [IsIrreducible ρ] [IsIrreducible η]

/-- Opposite simple embeddings split off a summand. A complement of dimension
at most two is trivial for the perfect actor, so the original kernel fixes X. -/
theorem fixes_of_opposite_embeddings
    (hd : Module.finrank (ZMod 2) X < Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) Y)
    (he : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) Y)
    (hsmall : Module.finrank (ZMod 2) X ≤ Module.finrank (ZMod 2) W + 2)
    (f : ρ.IntertwiningMap σ) (hf : f ≠ 0)
    (g : η.IntertwiningMap σ.dual) (hg : g ≠ 0)
    (h : H) (hh : ρ h = 1) : σ h = 1 := by
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hgi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  let t : σ.IntertwiningMap η.dual := {
    toLinearMap := {
      toFun x := {
        toFun y := g y x
        map_add' := by intros; simp
        map_smul' := by intros; simp }
      map_add' := by intros; ext y; exact map_add (g y) _ _
      map_smul' := by intros; ext y; exact map_smul (g y) _ _ }
    isIntertwining' := by
      intro a
      ext x y
      change g y (σ a x) = g (η a⁻¹ y) x
      rw [g.isIntertwining]
      change g y (σ a x) = g y (σ ((a⁻¹)⁻¹) x)
      rw [inv_inv] }
  have htf : t.comp f ≠ 0 := by
    intro hz
    have hr : LinearMap.range g.toLinearMap ≤
        (LinearMap.range f.toLinearMap).dualAnnihilator := by
      rintro _ ⟨y,rfl⟩
      apply (Submodule.mem_dualAnnihilator _).mpr
      rintro _ ⟨w,rfl⟩
      exact congrArg (fun a : ρ.IntertwiningMap η.dual => a w y) hz
    have hfd : Module.finrank (ZMod 2) (LinearMap.range f.toLinearMap) =
        Module.finrank (ZMod 2) W := (LinearEquiv.ofInjective f.toLinearMap hfi).finrank_eq.symm
    have hgd : Module.finrank (ZMod 2) (LinearMap.range g.toLinearMap) =
        Module.finrank (ZMod 2) Y := (LinearEquiv.ofInjective g.toLinearMap hgi).finrank_eq.symm
    have hl := Submodule.finrank_mono hr
    have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f.toLinearMap)
    omega
  have hti := (IsIrreducible.injective_or_eq_zero (t.comp f)).resolve_right htf
  have hts : Function.Surjective (t.comp f) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq]; exact he)).mp hti
  let E := (t.comp f).ofBijective ⟨hti,hts⟩
  let p := E.symm.toIntertwiningMap.comp t
  have hpf (w : W) : p (f w) = w := E.symm_apply_apply w
  have hps : Function.Surjective p := fun w => ⟨f w,hpf w⟩
  have hdim : Module.finrank (ZMod 2) p.ker.toSubmodule ≤ 2 := by
    have hs := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hps,finrank_top] at hs
    change Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) p.ker.toSubmodule =
      Module.finrank (ZMod 2) X at hs
    omega
  have htr := trivial_of_finrank_le_two p.ker.toRepresentation hdim
  apply LinearMap.ext
  intro x
  let z : p.ker.toSubmodule := ⟨x - f (p x),by
    change p (x - f (p x)) = 0
    rw [map_sub,hpf,sub_self]⟩
  have hz : σ h (x - f (p x)) = x - f (p x) := congrArg Subtype.val
    (LinearMap.congr_fun (DFunLike.congr_fun htr h) z)
  have hfz : σ h (f (p x)) = f (p x) := by
    rw [←f.isIntertwining,hh]
    rfl
  change σ h x = x
  simpa only [map_sub,hfz,sub_left_inj] using hz
/-- An embedded pair of inequivalent three-dimensional simples detects the
kernel of every perfect binary action of dimension at most five. -/
theorem fixes_of_pair_embedding
    (hw : Module.finrank (ZMod 2) W = 3) (hy : Module.finrank (ZMod 2) Y = 3)
    (hd : Module.finrank (ZMod 2) X ≤ 5)
    (hzero : ∀ b : η.IntertwiningMap ρ, b = 0)
    (F : (ρ.prod η).IntertwiningMap (σ.prod σ.dual)) (hF : Function.Injective F)
    (h : H) (hρ : ρ h = 1) (hη : η h = 1) : σ h = 1 := by
  let a : ρ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (F.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro w
      simpa using congrArg Prod.fst (LinearMap.congr_fun (F.isIntertwining' h) (w,0)) }
  let b : η.IntertwiningMap σ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (F.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro w
      simpa using congrArg Prod.fst (LinearMap.congr_fun (F.isIntertwining' h) (0,w)) }
  let c : ρ.IntertwiningMap σ.dual := {
    toLinearMap := (LinearMap.snd _ _ _).comp (F.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro w
      simpa using congrArg Prod.snd (LinearMap.congr_fun (F.isIntertwining' h) (w,0)) }
  let d : η.IntertwiningMap σ.dual := {
    toLinearMap := (LinearMap.snd _ _ _).comp (F.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro w
      simpa using congrArg Prod.snd (LinearMap.congr_fun (F.isIntertwining' h) (0,w)) }
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra! hn
    have hz (w : W) : F (w,0) = 0 := Prod.ext
      (congrArg (fun z : ρ.IntertwiningMap σ => z w) hn.1)
      (congrArg (fun z : ρ.IntertwiningMap σ.dual => z w) hn.2)
    have hs : Subsingleton W := ⟨fun x y => congrArg Prod.fst
      (hF ((hz x).trans (hz y).symm))⟩
    let := hs
    have hz : Module.finrank (ZMod 2) W = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hbd : b ≠ 0 ∨ d ≠ 0 := by
    by_contra! hn
    have hz (w : Y) : F (0,w) = 0 := Prod.ext
      (congrArg (fun z : η.IntertwiningMap σ => z w) hn.1)
      (congrArg (fun z : η.IntertwiningMap σ.dual => z w) hn.2)
    have hs : Subsingleton Y := ⟨fun x y => congrArg Prod.snd
      (hF ((hz x).trans (hz y).symm))⟩
    let := hs
    have hz : Module.finrank (ZMod 2) Y = 0 := Module.finrank_zero_of_subsingleton
    omega
  rcases hac with ha | hc
  · have hb := (IntertwiningMap.small_inequivalent_pair hzero (by omega) a b).resolve_left ha
    exact fixes_of_opposite_embeddings (by omega) (by omega) (by omega)
      a ha d (hbd.resolve_left (not_not_intro hb)) h hρ
  · have hd' := (IntertwiningMap.small_inequivalent_pair hzero (by
      rw [Subspace.dual_finrank_eq]; omega) c d).resolve_left hc
    exact fixes_of_opposite_embeddings (by omega) (by omega) (by omega)
      b (hbd.resolve_right (not_not_intro hd')) c hc h hη
end Representation.SmallDualPair
