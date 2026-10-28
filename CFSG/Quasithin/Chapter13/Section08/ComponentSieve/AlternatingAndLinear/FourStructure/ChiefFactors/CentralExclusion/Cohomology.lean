module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Cohomology tools for central-chief-factor exclusion

Vanishing first cohomology is preserved by extensions. Dualizing the exact
sequence gives the corresponding assertion for dual coefficients. A perfect
central cover with vanishing dual first cohomology has zero kernel, by the
universal cover of Aschbacher–Smith, Remark I.1.5, printed p.408.
-/

@[expose] public section

open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
variable {k G X Y Z : Type*} [Field k] [Group G]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z]
  {α : Representation k G X} {β : Representation k G Y} {γ : Representation k G Z}

lemma h1_vanish_exact (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : i.toLinearMap.range = p.toLinearMap.ker)
    [Subsingleton (H1 α)] [Subsingleton (H1 γ)] : Subsingleton (H1 β) := by
  suffices h : ∀ f : cocycles β, ∃ y, principal β y = f by
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := (Submodule.mkQ_surjective _) x
    obtain ⟨y, rfl⟩ := (Submodule.mkQ_surjective _) y
    exact ((classMap_eq_zero_iff β x).mpr (h x)).trans
      ((classMap_eq_zero_iff β y).mpr (h y)).symm
  intro f
  classical
  let pf : cocycles γ := ⟨fun g => p (f.val g), by
    intro g h
    change p (f.val (g * h)) = _
    rw [f.property, map_add, p.isIntertwining]⟩
  obtain ⟨z, hz⟩ := (classMap_eq_zero_iff γ pf).mp (Subsingleton.elim _ _)
  obtain ⟨y, rfl⟩ := hp z
  let d := f - principal β y
  have hd (g : G) : d.val g ∈ i.toLinearMap.range := by
    rw [hex]
    change p (f.val g - (β g y - y)) = 0
    have h := congrArg (fun c : cocycles γ => c.val g) hz
    change γ g (p y) - p y = p (f.val g) at h
    rw [map_sub, map_sub, p.isIntertwining, h, sub_self]
  choose a ha using hd
  change ∀ g, i (a g) = d.val g at ha
  let c : cocycles α := ⟨a, by
    intro g h
    apply hi
    rw [map_add, i.isIntertwining, ha, ha, ha]
    exact d.property g h⟩
  obtain ⟨x, hx⟩ := (classMap_eq_zero_iff α c).mp (Subsingleton.elim _ _)
  refine ⟨i x + y, ?_⟩
  ext g
  have h := congrArg (fun c : cocycles α => i (c.val g)) hx
  change i (α g x - x) = i (a g) at h
  rw [map_sub, i.isIntertwining, ha] at h
  change β g (i x + y) - (i x + y) = f.val g
  change β g (i x) - i x = f.val g - (β g y - y) at h
  rw [map_add]
  calc
    _ = (β g (i x) - i x) + (β g y - y) := by abel
    _ = f.val g := by rw [h]; abel

lemma cover_injective [Finite G] [FiniteDimensional k X] [FiniteDimensional k Y]
    (p : β.IntertwiningMap α) (hp : IsCover p)
    (hH : Module.finrank k (H1 α.dual) = 0) : Function.Injective p := by
  let : FiniteDimensional k (Module.Dual k (cocycles α.dual)) :=
    Subspace.instModuleDualFiniteDimensional (K := k) (V := cocycles α.dual)
  obtain ⟨q, hq, hqp⟩ := exists_universalCover_quotient p hp
  have hu : Function.Injective (universalCoverProjection α) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_ker_universalCoverProjection, hH]
  intro x y hxy
  obtain ⟨a, rfl⟩ := hq x
  obtain ⟨b, rfl⟩ := hq y
  exact congrArg q (hu (by rw [← hqp, ← hqp, hxy]))

lemma dual_equivariant (e : X ≃ₗ[k] Y)
    (he : ∀ g x, e (α g x) = β g (e x)) (g : G) (f : Module.Dual k X) :
    e.symm.dualMap (α.dual g f) = β.dual g (e.symm.dualMap f) := by
  ext y
  change f (α g⁻¹ (e.symm y)) = f (e.symm (β g⁻¹ y))
  congr 1
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply]

lemma h1_vanish_dual_exact [Finite G]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : i.toLinearMap.range = p.toLinearMap.ker)
    (hX : Module.finrank k (H1 α.dual) = 0)
    (hZ : Module.finrank k (H1 γ.dual) = 0) :
    Module.finrank k (H1 β.dual) = 0 := by
  have : Subsingleton (H1 α.dual) := Module.finrank_zero_iff.mp hX
  have : Subsingleton (H1 γ.dual) := Module.finrank_zero_iff.mp hZ
  have : Subsingleton (H1 β.dual) := h1_vanish_exact (dualIntertwining p)
    (dualIntertwining i) (LinearMap.dualMap_injective_of_surjective hp)
    (LinearMap.dualMap_surjective_of_injective hi) (by
      change p.toLinearMap.dualMap.range = i.toLinearMap.dualMap.ker
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
        LinearMap.ker_dualMap_eq_dualAnnihilator_range, hex])
  exact Module.finrank_zero_of_subsingleton
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
