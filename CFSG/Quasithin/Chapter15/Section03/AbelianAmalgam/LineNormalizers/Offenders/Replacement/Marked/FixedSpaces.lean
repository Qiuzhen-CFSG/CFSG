module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Constructions

/-!
# Literal marked fixed spaces and right conjugation

The source fixed spaces are relative element centralizers in the original
module. Their conjugacy uses right conjugation, and passage to a subgroup
containing the module preserves the literal fixed spaces. These identities do
not assert invariance under the whole line centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G]

/-- The actual subgroup `C_U(τ)`. -/
def markedFixed (U : Subgroup G) (τ : G) : Subgroup G :=
  U ⊓ centralizer ({τ} : Set G)

/-- The two source fixed spaces are conjugate by the specified right action. -/
theorem markedFixed_conjugate (U : Subgroup G) (τ y : G)
    (hy : y ∈ normalizer (U : Set G)) :
    otherLine (markedFixed U τ) y = markedFixed U (y⁻¹ * τ * y) := by
  let e : G ≃* G := MulAut.conj y⁻¹
  have heU : U.map e.toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (U : Set G)).inv_mem hy)
  change (U ⊓ centralizer ({τ} : Set G)).map e.toMonoidHom = _
  rw [map_inf _ _ _ e.injective, heU]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg e (mem_centralizer_singleton_iff.mp hv)
    have heτ : e τ = y⁻¹ * τ * y := by simp [e]
    rw [← heτ]
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h
  · intro hx
    refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, e, MulAut.conj_apply, inv_inv] using
      (mem_centralizer_singleton_iff.mp hx)

/-- The raw fixed space inside `H` maps to precisely the original ambient one. -/
theorem intrinsic_markedFixed_map (H U : Subgroup G) (hUH : U ≤ H) (τ : H) :
    (markedFixed (U.subgroupOf H) τ).map H.subtype = markedFixed U (τ : G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.1, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hv.2))⟩
  · rintro ⟨hxU, hxτ⟩
    exact mem_map.mpr ⟨⟨x, hUH hxU⟩, ⟨hxU, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hxτ))⟩, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
