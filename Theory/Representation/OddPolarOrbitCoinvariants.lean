module
public import Theory.Representation.UniformBinaryPolar
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Full displacement on an odd polar orbit

A doubly transitive binary orbit has the uniform off-diagonal polar form.
When its degree is odd and the target polar is nondegenerate, the orbit
sum vanishes. Its images in the coinvariant quotient are all equal, so
that odd sum kills the quotient. The proof preserves the actual action
and permits relations among orbit vectors.

Source application: the original normal row of Aschbacher–Smith 14.2.16,
printed pp.985–986.
-/

public section
open Module Representation
namespace BinaryBorelOrbit
variable {A P Ω W : Type*} [Group A] [Group P] [MulAction P Ω]
variable [AddCommGroup W] [Module (ZMod 2) W]

theorem odd_polar_coinvariants [Finite Ω]
    (π : A →* P) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) A W)
    (htwo : MulAction.IsMultiplyPretransitive P Ω 2)
    (b : Ω → W) (hb : ∀ a x, b (π a • x) = ρ a (b x))
    (hspan : Submodule.span (ZMod 2) (Set.range b) = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (hinv : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (hker : B.ker = ⊥) (hodd : Odd (Nat.card Ω)) :
    Coinvariants.ker ρ = ⊤ := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  let : MulAction.IsMultiplyPretransitive P Ω 2 := htwo
  let : MulAction.IsPretransitive P Ω := MulAction.isPretransitive_of_is_two_pretransitive
  let eΩ : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  let w (i : Fin (Fintype.card Ω)) := b (eΩ i)
  let f := Fintype.linearCombination (ZMod 2) w
  have hspw : Submodule.span (ZMod 2) (Set.range w) = ⊤ := by
    apply top_unique
    rw [←hspan]
    apply Submodule.span_mono
    rintro _ ⟨x,rfl⟩
    obtain ⟨i,rfl⟩ := eΩ.surjective x
    exact ⟨i,rfl⟩
  have hf : Function.Surjective f :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (ZMod 2) w).mp hspw
  have hcoeff (i : Fin (Fintype.card Ω)) : f (Pi.single i 1) = b (eΩ i) := by simp [f,w]
  have hp (i j i' j' : Fin (Fintype.card Ω)) (hij : i ≠ j) (hij' : i' ≠ j') :
      B (f (Pi.single i 1)) (f (Pi.single j 1)) =
        B (f (Pi.single i' 1)) (f (Pi.single j' 1)) := by
    simp only [hcoeff]
    obtain ⟨g,hi,hj⟩ := MulAction.is_two_pretransitive_iff.mp htwo
      (eΩ.injective.ne hij) (eΩ.injective.ne hij')
    obtain ⟨a,rfl⟩ := hπ g
    rw [←hi,←hj,hb,hb,hinv]
  have hpull := UniformBinaryPolar.pullback_eq_uniform B hB hne f hf hp
  have hodd' : Odd (Fintype.card Ω) := by simpa only [Nat.card_eq_fintype_card] using hodd
  have hone : (fun _ : Fin (Fintype.card Ω) => (1 : ZMod 2)) ∈
      (UniformBinaryPolar.form (Fintype.card Ω)).ker := by
    apply LinearMap.mem_ker.mpr
    apply (Pi.basisFun (ZMod 2) (Fin (Fintype.card Ω))).ext
    intro j
    simp only [Pi.basisFun_apply,LinearMap.zero_apply]
    rw [UniformBinaryPolar.form_apply_basis]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      hodd'.natCast_zmod_two]
    decide
  have hsum : f (fun _ => 1) = 0 := by
    have hz : f (fun _ => 1) ∈ B.ker := by
      apply LinearMap.mem_ker.mpr
      ext y
      obtain ⟨x,rfl⟩ := hf y
      have he := congrArg (fun C : LinearMap.BilinForm (ZMod 2)
        (UniformBinaryPolar.V (Fintype.card Ω)) => C (fun _ => 1) x) hpull
      exact he.trans (congrArg (fun l => l x) hone)
    simpa only [hker,Submodule.mem_bot] using hz
  have hmk (x y : Ω) : Coinvariants.mk ρ (b x) = Coinvariants.mk ρ (b y) := by
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq P y x
    obtain ⟨a,rfl⟩ := hπ a
    rw [←ha,hb,Coinvariants.mk_self_apply]
  apply top_unique
  rw [←hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  apply (Coinvariants.mk_eq_zero _).mp
  have hs := congrArg (Coinvariants.mk ρ) hsum
  have he : Coinvariants.mk ρ (f (fun _ => 1)) = Coinvariants.mk ρ (b x) := by
    change Coinvariants.mk ρ (∑ i, (1 : ZMod 2) • w i) = _
    simp only [one_smul,map_sum,w,hmk _ x,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),hodd'.natCast_zmod_two,one_smul]
  exact he.symm.trans (hs.trans (map_zero _))
end BinaryBorelOrbit
