module

public import Theory.AlgebraicGroup.RootSystems.Weyl
/-!
# The unique highest point of a dominant Weyl orbit

A point maximizing root height has no negative simple-coroot evaluation:
reflecting in such a root would increase height. The fundamental-domain
theorem identifies that maximum with the dominant representative. Equality
in the height bound consequently forces equality of the weights.

This is the highest-monomial argument for the fundamental Weyl-orbit sums in
Steinberg (1963), §3.9. The proof uses the actual Weyl group and its existing
root-space action, without enumerating Weyl elements.
-/

open Module
public section
namespace Theory.AlgebraicGroup.WeylOrbitHeight
variable {ι M N : Type*} [Fintype ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

omit [P.IsReduced] in
lemma dominant_of_maximal_height (x : M)
    (hx : ∀ g : P.weylGroup, b.chamberFunctional (g.1.weightMap x) ≤
      b.chamberFunctional x) : x ∈ b.dominantChamber := by
  intro j
  by_contra hneg
  have hBneg : P.RootForm x (P.root j) < 0 := lt_of_not_ge hneg
  have hcneg : P.coroot' j x < 0 := by
    have hlen := RootPairing.rootForm_root_self_pos P j
    have heq := RootPairing.two_mul_rootForm_apply_root P j x
    nlinarith
  have hmax := hx (b.simpleReflection j)
  change b.chamberFunctional (P.reflection j x) ≤ b.chamberFunctional x at hmax
  rw [P.reflection_apply, map_sub, map_smul, b.chamberFunctional_root] at hmax
  simp only [smul_eq_mul, mul_one] at hmax
  linarith

lemma height_le_of_dominant (x : M) (hx : x ∈ b.dominantChamber)
    (g : P.weylGroup) :
    b.chamberFunctional (g.1.weightMap x) ≤ b.chamberFunctional x := by
  let : Finite P.weylGroup := weylGroup_finite P
  let : Fintype P.weylGroup := Fintype.ofFinite P.weylGroup
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ
    (fun w : P.weylGroup => b.chamberFunctional (w.1.weightMap x)) Finset.univ_nonempty
  have hdom : w.1.weightMap x ∈ b.dominantChamber := by
    apply dominant_of_maximal_height b
    intro a
    exact hw (a * w) (Finset.mem_univ _)
  have he : w.1.weightMap x = x :=
    (weylGroup_dominantChamber_fundamentalDomain b).2 x hx w hdom
  simpa only [he] using hw g (Finset.mem_univ g)

lemma height_eq_iff_of_dominant (x : M) (hx : x ∈ b.dominantChamber)
    (g : P.weylGroup) :
    b.chamberFunctional (g.1.weightMap x) = b.chamberFunctional x ↔
      g.1.weightMap x = x := by
  constructor
  · intro he
    have hdom : g.1.weightMap x ∈ b.dominantChamber := by
      apply dominant_of_maximal_height b
      intro a
      rw [he]
      exact height_le_of_dominant b x hx (a * g)
    exact (weylGroup_dominantChamber_fundamentalDomain b).2 x hx g hdom
  · rintro h
    rw [h]
end Theory.AlgebraicGroup.WeylOrbitHeight
