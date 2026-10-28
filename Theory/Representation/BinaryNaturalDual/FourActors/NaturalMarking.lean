module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.Radical
public import Theory.Representation.BinaryNaturalDual.FourActors.NaturalMarking.RadicalIdentification
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections.Linear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Natural transvections in the fixed eight-point comparison

The fixed-point-free four-pair permutation centralizes the binary-tree Sylow.
A Sylow of A₈ can be placed inside that tree subgroup; pulling it back through
`linearAlternatingEquiv` makes the four-pair element a natural transvection.
Conjugacy of transvections and invariance under automorphisms then identify
exactly the cycle type 2⁴, using the specified exceptional comparison.

The displacement formula retains its nonzero center vector and linear form,
its center line, and its hyperplane axis. Rank-nullity gives fixed dimension
three. For another nonidentity involution the square-zero displacement has
rank at least two and image in its kernel, forcing fixed dimension two.

The imported radical identification uses the public exterior/deleted-module
compatibility of the attributed ATLAS comparison, and needs only the order-16
premise for the specified A₀. It does not assume a transvection marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(4–6),
printed pp.391–392, PDF pp.402–403.
-/

@[expose] public section

open scoped Pointwise
open Equiv Subgroup
open BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricEight.Involutions
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryNaturalDual.FourActors

private theorem fourPairs_central_tree {x : S} (hx : x ∈ treeGroup) :
    x * fourPairs = fourPairs * x := by
  have h : treeGroup ≤ centralizer ({fourPairs} : Set S) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((by decide +kernel : ∀ i, treeGenerator i * fourPairs = fourPairs * treeGenerator i) i)
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hx)

private theorem exists_sylow_le_tree :
    ∃ P : Sylow 2 (alternatingGroup (Fin 8)), ∀ x ∈ P, x.val ∈ treeGroup := by
  let R : Sylow 2 (alternatingGroup (Fin 8)) := Sylow.nonempty.some
  obtain ⟨Q, hQ⟩ := R.exists_comap_subtype_eq
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq S Q treeSylow
  let a : MulAut (alternatingGroup (Fin 8)) := MulAut.conjNormal q
  refine ⟨R.mapSurjective (f := a.toMonoidHom) a.surjective, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y.val ∈ Q := by
    change y ∈ (Q : Subgroup S).comap (alternatingGroup (Fin 8)).subtype
    rwa [hQ]
  have hq' : MulAut.conj q • (Q : Subgroup S) = treeGroup :=
    congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hq
  rw [← hq']
  exact Subgroup.smul_mem_pointwise_smul y.val (MulAut.conj q) (Q : Subgroup S) hyQ

noncomputable def naturalFourPairs : G :=
  linearAlternatingEquiv.symm ⟨fourPairs, Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[simp] theorem naturalFourPairs_permutation :
    (linearAlternatingEquiv naturalFourPairs).val = fourPairs := by
  simp [naturalFourPairs]

theorem naturalFourPairs_isTransvection : IsTransvection naturalFourPairs := by
  obtain ⟨P, hP⟩ := exists_sylow_le_tree
  let Q : Sylow 2 G := P.mapSurjective
    (f := linearAlternatingEquiv.symm.toMonoidHom) linearAlternatingEquiv.symm.surjective
  apply isTransvection_of_central_sylow (V := X) (by simp [Nat.card_eq_fintype_card, X])
    (by simp [X]) Q
  · intro h
    have hh := congrArg (fun g : G => (linearAlternatingEquiv g).val) h
    rw [naturalFourPairs_permutation, map_one] at hh
    exact (by decide +kernel : fourPairs ≠ 1) hh
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply linearAlternatingEquiv.injective
    apply Subtype.ext
    change (linearAlternatingEquiv (linearAlternatingEquiv.symm y * naturalFourPairs)).val =
      (linearAlternatingEquiv (naturalFourPairs * linearAlternatingEquiv.symm y)).val
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      naturalFourPairs_permutation] using fourPairs_central_tree (hP y hy)

theorem isTransvection_iff_cycleType (g : G) :
    IsTransvection g ↔ (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2} := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := transvections_conjugate naturalFourPairs_isTransvection hg
    rw [← ha, permutationEquiv_action]
    exact (Perm.isConj_iff_cycleType_eq.mp (isConj_iff.mpr
      ⟨permutationEquiv (MulAut.conj a), rfl⟩)).symm.trans
      (by rw [naturalFourPairs_permutation]; exact fourPairs_cycleType)
  · intro hg
    have hc : IsConj fourPairs (linearAlternatingEquiv g).val :=
      Perm.isConj_iff_cycleType_eq.mpr (fourPairs_cycleType.trans hg.symm)
    obtain ⟨q, hq⟩ := isConj_iff.mp hc
    let a : M := permutationEquiv.symm q
    have ha : a naturalFourPairs = g := by
      apply linearAlternatingEquiv.injective
      apply Subtype.ext
      rw [permutationEquiv_action, naturalFourPairs_permutation]
      simpa only [a, MulEquiv.apply_symm_apply] using hq
    rw [← ha]
    exact (isTransvection_map_linear (by decide) a naturalFourPairs).mpr
      naturalFourPairs_isTransvection

/-- The actual rank-one displacement, its center line, and its hyperplane axis. -/
theorem transvection_geometry {g : G} (hg : IsTransvection g) :
    ∃ (w : X) (f : X →ₗ[ZMod 2] ZMod 2), w ≠ 0 ∧ f ≠ 0 ∧ f w = 0 ∧
      (∀ x, g x = x + f x • w) ∧ g.fixedSubmodule = f.ker ∧
      LinearMap.range (g.toLinearMap - LinearMap.id) = Submodule.span (ZMod 2) {w} := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := hg
  refine ⟨w, f, hw, hf, hfw, fun _ => rfl, ?_, ?_⟩
  · ext x
    change x + f x • w = x ↔ f x = 0
    simp [hw]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change (x + f x • w) - x ∈ Submodule.span (ZMod 2) {w}
      simpa only [add_sub_cancel_left] using
        (Submodule.span (ZMod 2) {w}).smul_mem (f x) (Submodule.mem_span_singleton_self w)
    · apply Submodule.span_le.mpr
      intro u hu
      have heu : u = w := Set.mem_singleton_iff.mp hu
      subst u
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra! h
        exact hf (LinearMap.ext h)
      have hx1 : f x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (f x) hx
      exact ⟨x, by change (x + f x • w) - x = w; simp [hx1]⟩

theorem transvection_fixed_finrank {g : G} (hg : IsTransvection g) :
    Module.finrank (ZMod 2) g.fixedSubmodule = 3 := by
  obtain ⟨w, f, _, hf, _, _, he, _⟩ := transvection_geometry hg
  rw [he]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hd : Module.finrank (ZMod 2) X = 4 := by simp [X]
  rw [hd] at h
  exact Nat.add_right_cancel h

theorem nontransvection_involution_fixed_finrank (g : G) (h1 : g ≠ 1)
    (h2 : g ^ 2 = 1) (ht : ¬ IsTransvection g) :
    Module.finrank (ZMod 2) g.fixedSubmodule = 2 := by
  let d := g.toLinearMap - LinearMap.id
  have hle : d.range ≤ d.ker := by
    rintro _ ⟨x, rfl⟩
    have hgx : g (g x) = x := congrArg (fun e : G => e x) h2
    change g (g x - x) - (g x - x) = 0
    rw [map_sub, hgx]
    have hn : -(g x - x) = g x - x := by
      exact (eq_neg_of_add_eq_zero_left (ZModModule.add_self (g x - x))).symm
    rw [show x - g x = -(g x - x) by abel, hn, sub_self]
  have hr : 2 ≤ Module.finrank (ZMod 2) d.range := by
    by_contra! h
    have hh := Representation.SymmetricEightTransvections.Linear.of_small_displacement g
      (show Module.finrank (ZMod 2) d.range ≤ 1 by omega)
    obtain ⟨f, w, hfw, he⟩ := LinearEquiv.mem_transvections_iff.mp hh
    apply ht
    have hw : w ≠ 0 := by
      intro hz
      apply h1
      rw [he]
      ext x
      simp [hz]
    have hf : f ≠ 0 := by
      intro hz
      apply h1
      rw [he]
      ext x
      simp [hz]
    exact ⟨w, f, hw, hf, hfw, he.trans (by ext x; rfl)⟩
  have hk := Submodule.finrank_mono hle
  have hn := d.finrank_range_add_finrank_ker
  have hd : Module.finrank (ZMod 2) X = 4 := by simp [X]
  rw [hd] at hn
  rw [LinearMap.fixedSubmodule_eq_ker]
  change Module.finrank (ZMod 2) d.ker = 2
  omega

/-- The natural four-pair transvection induces the already published actor `r`. -/
theorem naturalFourPairs_inner : MulAut.conj naturalFourPairs = r := by
  apply permutationEquiv.injective
  rw [permutationEquiv_inner, naturalFourPairs_permutation, permutationEquiv_r]

/-- Natural transvections have genuinely one-dimensional displacement. -/
theorem transvection_displacement_finrank {g : G} (hg : IsTransvection g) :
    Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1 := by
  obtain ⟨w, f, hw, _, _, _, _, he⟩ := transvection_geometry hg
  rw [he, finrank_span_singleton hw]

/-- The fixed dimension for the other natural involution class, in order notation. -/
theorem nontransvection_orderTwo_fixed_finrank (g : G) (hg : orderOf g = 2)
    (ht : ¬ IsTransvection g) : Module.finrank (ZMod 2) g.fixedSubmodule = 2 := by
  apply nontransvection_involution_fixed_finrank g
  · intro h
    simp [h] at hg
  · simpa only [hg] using pow_orderOf_eq_one g
  · exact ht

end BinaryNaturalDual.FourActors
