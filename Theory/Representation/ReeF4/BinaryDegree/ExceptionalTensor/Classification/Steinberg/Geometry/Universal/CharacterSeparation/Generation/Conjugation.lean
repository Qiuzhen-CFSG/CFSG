module

public import Theory.AlgebraicGroup.RootSubgroups.Conjugation

/-!
# Matching realized root subgroups across torus conjugacy

Conjugation preserves and reflects the root-weight equation. Given uniqueness
of the subgroup with one specified weight, completeness of a root realization
then identifies the conjugate of that subgroup among the realization's roots.
The argument uses actual characters and is independent of root indices, bases,
and coroot conventions.

These are the transport steps in GLS3, Theorem 1.9.5(b),(c), used in the
whole-group generation clause of (i), `refs/KGroup/GLS3/Chapter1.tex`.
Uniqueness at the initial torus is an explicit geometric input.
-/

public section

universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Conjugating both subgroups preserves and reflects the exact root-weight equation. -/
theorem RootWeightEquation.conjugate_iff
    (T X : ClosedSubgroup G) (g : Variety.Point G) (χ : TorusWeight T) :
    RootWeightEquation T X χ ↔ RootWeightEquation (T.conjugate g) (X.conjugate g)
      (torusWeightConjugateEquiv T g χ) := by
  constructor
  · exact RootWeightEquation.conjugate g
  · intro h y t s
    let y' : OneParameterParametrization (X.conjugate g).carrierVariety :=
      (X.conjugateIso g).comp y
    let s' := (T.conjugateIso g).hom.onPoints s
    have hy (a : k) : (X.conjugate g).includePoint (y'.value a) =
        g * X.includePoint (y.value a) * g⁻¹ :=
      X.conjugateIso_hom_inclusion_apply g (y.value a)
    have hs : (T.conjugate g).includePoint s' = g * T.includePoint s * g⁻¹ :=
      T.conjugateIso_hom_inclusion_apply g s
    have hχ : (torusWeightConjugateEquiv T g χ).pointCharacter s' =
        χ.pointCharacter s := by
      rw [torusWeightConjugateEquiv_pointCharacter]
      change χ.pointCharacter ((T.conjugateIso g).inv.onPoints
        ((T.conjugateIso g).hom.onPoints s)) = _
      rw [(T.conjugateIso g).hom_inv_id]
    have heq := h y' t s'
    rw [hy, hs, hχ, hy] at heq
    apply (MulAut.conj g).injective
    simp only [MulAut.conj_apply]
    calc
      _ = (g * T.includePoint s * g⁻¹)⁻¹ *
          (g * X.includePoint (y.value t) * g⁻¹) *
          (g * T.includePoint s * g⁻¹) := by group
      _ = _ := heq

/-- Every uniquely realized weight supplies the corresponding root subgroup in any
realization for a conjugate torus. No identification of root indices is required. -/
theorem RootGroupData.exists_rootSubgroup_eq_conjugate_of_unique_weight
    {T X : ClosedSubgroup G} {χ : TorusWeight T}
    (g : Variety.Point G) (D : RootGroupData G (T.conjugate g))
    (hD : D.IsRealization) (hX : IsTorusRootSubgroup T X)
    (hχ : RootWeightEquation T X χ)
    (hunique : ∀ Y : ClosedSubgroup G, IsTorusRootSubgroup T Y →
      RootWeightEquation T Y χ → Y = X) :
    ∃ α, D.rootSubgroup α = X.conjugate g := by
  have hroot : torusWeightConjugateEquiv T g χ ∈ TorusRootSet (T.conjugate g) :=
    IsTorusRoot.conjugate g ⟨X, hX, hχ⟩
  rw [← hD.2.1] at hroot
  obtain ⟨α, hα⟩ := hroot
  have hY := (hD.2.2.1 α).1.conjugate g⁻¹
  have hT : (T.conjugate g).conjugate g⁻¹ = T := by
    rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
      ClosedSubgroup.conjugate_one]
  rw [hT] at hY
  have hback : ((D.rootSubgroup α).conjugate g⁻¹).conjugate g =
      D.rootSubgroup α := by
    rw [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
      ClosedSubgroup.conjugate_one]
  have hYχ : RootWeightEquation T ((D.rootSubgroup α).conjugate g⁻¹) χ := by
    apply (RootWeightEquation.conjugate_iff T _ g χ).mpr
    rw [hback, ← hα]
    exact (hD.2.2.1 α).2
  have hYX := hunique _ hY hYχ
  refine ⟨α, ?_⟩
  rw [← hback, hYX]

end Theory.AlgebraicGroup
