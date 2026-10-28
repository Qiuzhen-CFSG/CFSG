module

public import Theory.GroupTheory.DihedralEightSections

/-!
# Exponent bounds in Sylow sections

Lift a quotient Sylow to a Sylow of the original subgroup and place its
image in an ambient Sylow. Conjugacy carries the exponent bound to that
image, and the actual quotient map carries it back down. This supports
the marked component quotient calculations in Aschbacher–Smith F.6.18.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem sylow_section_pow_eq_one
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) {n : ℕ} (he : ∀ x : T, x ^ n = 1)
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (x : P) : x ^ n = 1 := by
  obtain ⟨S,hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  let eQ : ((S : Subgroup K).map f) ≃* P :=
    MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hS)
  let q : S →* P := eQ.toMonoidHom.comp (f.subgroupMap (S : Subgroup K))
  have hq : Function.Surjective q :=
    eQ.surjective.comp (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U,hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  let i : S →* U := (Subgroup.inclusion hU).comp
    (K.subtype.subgroupMap (S : Subgroup K))
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) h
  let j := U.equiv T
  obtain ⟨s,rfl⟩ := hq x
  have hs : s ^ n = 1 := hi (j.injective (by
    simp only [map_pow,map_one]
    exact he (j (i s))))
  rw [← map_pow,hs,map_one]
end Theory.GroupTheory
