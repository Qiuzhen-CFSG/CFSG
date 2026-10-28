module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel

/-!
# Correcting a literal lifted subspace by a full shear

An automorphism fixing the projection kernel pointwise sends a subspace to
another lift with the same projected image. Linear sections of the two
projections measure their difference in the kernel. Extending that difference
to the whole quotient gives a single shear which corrects the original
subspace. The exact correcting linear map and ambient subspace are retained.
-/

public section
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) X]

/-- Full kernel shears correct a literal lifted subspace whenever its image
is stabilized and the original projection kernel is fixed pointwise. -/
theorem exists_shear_correcting_subspace
    (p : X →ₗ[ZMod 2] Y) (E : Submodule (ZMod 2) X)
    (g : X ≃ₗ[ZMod 2] X) (hfix : ∀ x ∈ p.ker, g x = x)
    (himage : E.map (p.comp g.toLinearMap) = E.map p) :
    ∃ f : Y →ₗ[ZMod 2] p.ker,
      E.map (g.toLinearMap + p.ker.subtype.comp (f.comp (p.comp g.toLinearMap))) = E := by
  let P := E.map p
  let a : E →ₗ[ZMod 2] P := ((p.comp g.toLinearMap).comp E.subtype).codRestrict P (by
    intro e
    change p (g e) ∈ E.map p
    rw [←himage]
    exact Submodule.mem_map.mpr ⟨e,e.property,rfl⟩)
  let b : E →ₗ[ZMod 2] P := (p.comp E.subtype).codRestrict P (by
    intro e
    exact Submodule.mem_map.mpr ⟨e,e.property,rfl⟩)
  have has : Function.Surjective a := by
    intro y
    have hy : y.val ∈ E.map (p.comp g.toLinearMap) := himage.symm ▸ y.property
    obtain ⟨e,he,hye⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨e,he⟩,Subtype.ext hye⟩
  have hbs : Function.Surjective b := by
    intro y
    obtain ⟨e,he,hye⟩ := Submodule.mem_map.mp y.property
    exact ⟨⟨e,he⟩,Subtype.ext hye⟩
  obtain ⟨u,hu⟩ := a.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr has)
  obtain ⟨v,hv⟩ := b.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hbs)
  have hu' (y : P) : p (g (u y)) = y.val := congrArg Subtype.val (LinearMap.congr_fun hu y)
  have hv' (y : P) : p (v y) = y.val := congrArg Subtype.val (LinearMap.congr_fun hv y)
  let f₀ : P →ₗ[ZMod 2] p.ker :=
    ((E.subtype.comp v) - g.toLinearMap.comp (E.subtype.comp u)).codRestrict p.ker (by
      intro y
      change p ((v y : X) - g (u y)) = 0
      rw [map_sub,hv',hu',sub_self])
  obtain ⟨f,hf⟩ := f₀.exists_extend
  have hf' (y : P) : (f y.val : X) = (v y : X) - g (u y) :=
    congrArg Subtype.val (LinearMap.congr_fun hf y)
  let φ := g.toLinearMap + p.ker.subtype.comp (f.comp (p.comp g.toLinearMap))
  have hpφ (x : X) : p (φ x) = p (g x) := by
    change p (g x + (f (p (g x)) : X)) = p (g x)
    rw [map_add,(f (p (g x))).property,add_zero]
  have hφ : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro x hx
    have hpx : p (g x) = 0 := (hpφ x).symm.trans (by rw [show φ x=0 from hx,map_zero])
    have hgx : g x = 0 := by
      have hh : g x + (f (p (g x)) : X) = 0 := hx
      simpa only [hpx,map_zero,Submodule.coe_zero,add_zero] using hh
    exact g.injective (hgx.trans g.map_zero.symm)
  have hle : E.map φ ≤ E := by
    rintro _ ⟨e,he,rfl⟩
    let y : P := a ⟨e,he⟩
    have hy : y.val = p (g e) := rfl
    have hker : g (e - (u y : X)) ∈ p.ker := by
      change p (g (e - (u y : X))) = 0
      rw [map_sub,map_sub,hu',hy,sub_self]
    have hfixed : g (e - (u y : X)) = e - (u y : X) := by
      apply g.injective
      exact hfix _ hker
    have hvalue : φ e = (v y : X) + (e - (u y : X)) := by
      change g e + (f (p (g e)) : X) = _
      rw [←hy,hf']
      have hh := hfixed
      rw [map_sub] at hh
      calc
        _ = (v y : X) + (g e - g (u y)) := by abel
        _ = (v y : X) + (e - (u y : X)) := by rw [hh]
    rw [hvalue]
    exact E.add_mem (v y).property (E.sub_mem he (u y).property)
  refine ⟨f,Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  have hh := LinearMap.finrank_range_of_inj (f := φ.comp E.subtype)
    (hφ.comp E.subtype_injective)
  have hr : (φ.comp E.subtype).range = E.map φ := by
    ext x
    constructor
    · rintro ⟨e,rfl⟩
      exact ⟨e,e.property,rfl⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨⟨e,he⟩,rfl⟩
  rw [hr] at hh
  exact hh

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
