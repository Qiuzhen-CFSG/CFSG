module
public import Theory.Representation.Suzuki.NaturalCentralizer
public import Theory.Representation.Suzuki.SmallDegree.Twists
public import Theory.Representation.Suzuki.SmallDegree.Models

/-!
# Field-linear lifts of Suzuki automorphisms

Inner-field coverage implements every automorphism on the natural module.
Comparing its intertwiner with a field-linear lift gives an additive
commuting map, hence a scalar. The field factor must therefore be identity.
The result is consumed by the literal Chapter 10 Hall action.

Source: GLS3, 2.5.12(b--f); Aschbacher--Smith 10.2.3, printed p.745.
-/

public noncomputable section
namespace Representation.SuzukiNatural
open BenderSuzuki.MatrixGroups SuzukiSmallDegree

theorem linear_intertwiner_inner (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m))
    (E : W m ≃ₗ[F m] W m)
    (he : ∀ g v, E (natural m g v) = natural m (α g) (E v)) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨g,s,hs⟩ := suzukiAut_eq_inner_mul_field m hm α
  let δ := innerFieldEquiv m g s
  let D := δ.toLinearEquiv
  have hD (x : SuzukiMatrixGroup m) (v : W m) :
      D (natural m x v) = natural m (α x) (D v) := by
    have hh := LinearMap.congr_fun (δ.isIntertwining' x) v
    change D (natural m x v) = natural m ((MulAut.conj g * suzukiFieldAut m s) x) (D v) at hh
    rwa [←hs] at hh
  let f : W m →+ W m := E.symm.toAddEquiv.toAddMonoidHom.comp D.toAddEquiv.toAddMonoidHom
  have hf (x : SuzukiMatrixGroup m) (v : W m) :
      f (natural m x v) = natural m x (f v) := by
    apply E.injective
    change E (E.symm (D (natural m x v))) = E (natural m x (E.symm (D v)))
    rw [E.apply_symm_apply,he,E.apply_symm_apply,hD]
  obtain ⟨a,ha⟩ := commuting_addHom_eq_scalar m f hf
  have hlin (c : F m) (v : W m) : D (c • v) = c • D v := by
    have hv (v : W m) : D v = E (a • v) := by
      have hh := congrArg E (ha v)
      change E (E.symm (D v)) = _ at hh
      rwa [E.apply_symm_apply] at hh
    rw [hv,hv,E.map_smul,E.map_smul,E.map_smul,smul_comm]
  have hsem (c : F m) (v : W m) : D (c • v) = s c • D v := by
    change natural m g (fieldCoordinates m s (c • v)) =
      s c • natural m g (fieldCoordinates m s v)
    have hh : fieldCoordinates m s (c • v) = s c • fieldCoordinates m s v := by
      ext i
      exact s.map_mul c (v i)
    rw [hh]
    exact (SuzukiSmallDegree.naturalField m g).map_smul (s c) _
  have hsone : s = 1 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : W m)
    have hDv : D v ≠ 0 := fun hh => hv (D.injective (hh.trans D.map_zero.symm))
    ext c
    exact smul_left_injective (F m) hDv ((hsem c v).symm.trans (hlin c v))
  refine ⟨g,?_⟩
  rw [hs,hsone]
  rw [←suzukiFieldAutHom_apply,map_one,mul_one]
end Representation.SuzukiNatural
