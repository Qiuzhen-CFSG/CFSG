module

public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.HalfWeight
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal


/-!
# The orthogonal sum of the two alternating-five modules

Each factor is the actual five-point augmentation core, with its minus-type
quadratic form. The product action and the literal factor interchange preserve
the orthogonal-sum form. Its polar form is nondegenerate, hence a totally
isotropic subspace has dimension at most four. The diagonal singular point is
the unique nonzero vector fixed by the two diagonal Klein generators and swap;
its stabilizer in the product consists of the two point-four stabilizers.

The small checks concern binary words on five coordinates. Source:
Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(12), printed
p.364, and the model calculation in 12.8.13(7), printed p.856.
-/

@[expose] public section

open Module
namespace BinaryPermutation.TerminalOrthogonal.PairedFive
abbrev Factor := core (Fin 5)
abbrev Space := Factor × Factor
abbrev Actor := alternatingGroup (Fin 5) × alternatingGroup (Fin 5)

noncomputable def action : Representation (ZMod 2) Actor Space :=
  Representation.prod
  (((coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype).comp
    (MonoidHom.fst _ _))
  (((coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype).comp
    (MonoidHom.snd _ _))

@[simp] lemma action_apply (g : Actor) (v : Space) :
    action g v = (coreRepresentation (Fin 5) g.1.val v.1,
      coreRepresentation (Fin 5) g.2.val v.2) := rfl

def swap : Space ≃ₗ[ZMod 2] Space := LinearEquiv.prodComm _ _ _

lemma swap_action (g : Actor) (v : Space) :
    swap (action g v) = action (g.2, g.1) (swap v) := rfl

noncomputable def form : QuadraticForm (ZMod 2) Space :=
  (FiveGeometry.form.comp (LinearMap.fst _ _ _)) +
    (FiveGeometry.form.comp (LinearMap.snd _ _ _))

@[simp] lemma form_apply (v : Space) :
    form v = FiveGeometry.form v.1 + FiveGeometry.form v.2 := rfl

lemma swap_form (v : Space) : form (swap v) = form v := add_comm _ _

lemma finrank_space : finrank (ZMod 2) Space = 8 := by
  rw [Module.finrank_prod, FiveGeometry.finrank_core]

private lemma factor_halfWeight (v : Factor) :
    FiveGeometry.form v = Atlas.Order20160A8.HalfWeight.binaryHalfWeight v.val := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) =
        Atlas.Order20160A8.HalfWeight.binaryHalfWeight x := by decide
  exact h v.val v.property

lemma factor_form_invariant (g : Equiv.Perm (Fin 5)) (v : Factor) :
    FiveGeometry.form (coreRepresentation (Fin 5) g v) = FiveGeometry.form v := by
  rw [factor_halfWeight, factor_halfWeight]
  unfold Atlas.Order20160A8.HalfWeight.binaryHalfWeight
  congr 1
  congr 1
  rw [Atlas.Codes.hammingNorm_eq_sum, Atlas.Codes.hammingNorm_eq_sum]
  exact Equiv.sum_comp g.symm (fun i => if v.val i = 0 then 0 else 1)

lemma form_invariant (g : Actor) (v : Space) : form (action g v) = form v := by
  simp only [form_apply, action_apply, factor_form_invariant]

private lemma factor_polar (v w : Factor) :
    FiveGeometry.form.polarBilin v w = ∑ i, v.val i * w.val i := by
  have h : ∀ x y : Full (Fin 5), (∑ i, x i) = 0 → (∑ i, y i) = 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, (x i + y i) * (x j + y j)) -
        (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) -
        (∑ i : Fin 5, ∑ j : Fin 5 with i < j, y i * y j) =
          ∑ i, x i * y i := by decide
  exact h v.val w.val v.property w.property

lemma factor_polar_nondegenerate : FiveGeometry.form.polarBilin.Nondegenerate := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      (∀ y : Full (Fin 5), (∑ i, y i) = 0 → (∑ i, x i * y i) = 0) → x = 0 := by decide
  constructor
  · intro v hv
    apply Subtype.ext
    exact h v.val v.property (fun y hy => by
      simpa only [factor_polar] using hv (⟨y, hy⟩ : Factor))
  · intro v hv
    apply Subtype.ext
    exact h v.val v.property (fun y hy => by
      simpa only [factor_polar, mul_comm] using hv (⟨y, hy⟩ : Factor))

lemma polar_apply (v w : Space) :
    form.polarBilin v w = FiveGeometry.form.polarBilin v.1 w.1 +
      FiveGeometry.form.polarBilin v.2 w.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, form_apply,
    Prod.fst_add, Prod.snd_add]
  ring

lemma polar_nondegenerate : form.polarBilin.Nondegenerate := by
  constructor
  · intro v hv
    apply Prod.ext
    · apply factor_polar_nondegenerate.1
      intro w
      have h := hv (w, 0)
      simpa only [polar_apply, map_zero, add_zero] using h
    · apply factor_polar_nondegenerate.1
      intro w
      have h := hv (0, w)
      simpa only [polar_apply, map_zero, zero_add] using h
  · intro v hv
    apply Prod.ext
    · apply factor_polar_nondegenerate.2
      intro w
      have h := hv (w, 0)
      simpa only [polar_apply, map_zero, LinearMap.zero_apply, add_zero] using h
    · apply factor_polar_nondegenerate.2
      intro w
      have h := hv (0, w)
      simpa only [polar_apply, map_zero, LinearMap.zero_apply, zero_add] using h

lemma isotropic_finrank_le (E : Submodule (ZMod 2) Space)
    (hE : ∀ v ∈ E, ∀ w ∈ E, form.polarBilin v w = 0) : finrank (ZMod 2) E ≤ 4 := by
  have hle : E ≤ LinearMap.BilinForm.orthogonal form.polarBilin E := fun v hv w hw => hE w hw v hv
  have hd := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal polar_nondegenerate, finrank_space] at hd
  omega

/-- The singular point fixed by the standard Klein four. -/
def factorPoint : Factor := ⟨fun i => if i = 4 then 0 else 1, by
  change (∑ i : Fin 5, if i = 4 then (0 : ZMod 2) else 1) = 0
  decide⟩

def point : Space := (factorPoint, factorPoint)

lemma point_ne_zero : point ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Space => v.1.val 0) h
  exact one_ne_zero h0

lemma point_singular : form point = 0 := by decide

lemma swap_point : swap point = point := rfl

lemma factorPoint_fixed_iff (g : Equiv.Perm (Fin 5)) :
    coreRepresentation (Fin 5) g factorPoint = factorPoint ↔ g 4 = 4 := by
  constructor
  · intro h
    have hh := congrArg (fun v : Factor => v.val (g 4)) h
    change (if g.symm (g 4) = 4 then (0 : ZMod 2) else 1) =
      (if g 4 = 4 then 0 else 1) at hh
    by_contra hn
    simp [hn] at hh
  · intro h
    apply Subtype.ext
    funext i
    change (if g.symm i = 4 then (0 : ZMod 2) else 1) = (if i = 4 then 0 else 1)
    simp only [Equiv.symm_apply_eq, h]

lemma point_fixed_iff (g : Actor) : action g point = point ↔
    g.1.val 4 = 4 ∧ g.2.val 4 = 4 := by
  change action g (factorPoint, factorPoint) = (factorPoint, factorPoint) ↔ _
  rw [action_apply, Prod.mk.injEq, factorPoint_fixed_iff, factorPoint_fixed_iff]

end BinaryPermutation.TerminalOrthogonal.PairedFive

namespace BinaryPermutation.TerminalOrthogonal.PairedFive

private lemma factor_fixed_test (v : Factor)
    (h₁ : coreRepresentation (Fin 5) BinaryPermutation.CubicFixedSpace.Five.first.val v = v)
    (h₂ : coreRepresentation (Fin 5) BinaryPermutation.CubicFixedSpace.Five.second.val v = v) :
    v = 0 ∨ v = factorPoint := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      representation (Fin 5) BinaryPermutation.CubicFixedSpace.Five.first.val x = x →
      representation (Fin 5) BinaryPermutation.CubicFixedSpace.Five.second.val x = x →
      x = 0 ∨ x = (fun i => if i = 4 then 0 else 1) := by decide
  rcases h v.val v.property (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

lemma eq_point_of_fixed (v : Space) (hv : v ≠ 0)
    (h₁ : action (BinaryPermutation.CubicFixedSpace.Five.first,
      BinaryPermutation.CubicFixedSpace.Five.first) v = v)
    (h₂ : action (BinaryPermutation.CubicFixedSpace.Five.second,
      BinaryPermutation.CubicFixedSpace.Five.second) v = v)
    (hs : swap v = v) : v = point := by
  have he : v.2 = v.1 := congrArg Prod.fst hs
  rcases factor_fixed_test v.1 (congrArg Prod.fst h₁) (congrArg Prod.fst h₂) with h | h
  · exact (hv (Prod.ext h (he.trans h))).elim
  · exact Prod.ext h (he.trans h)

end BinaryPermutation.TerminalOrthogonal.PairedFive
