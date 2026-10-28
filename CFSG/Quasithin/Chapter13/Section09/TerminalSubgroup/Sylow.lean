module

public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Basic
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Restricting the centralizer Sylow product to the terminal residual

Transfer kills the E-coordinate in the residual. Consequently, if the
second factor D of a marked Sylow product E × D lies in H, its literal
ambient image is a Sylow subgroup of H. Restriction to the normal residual
preserves the chosen Sylow subgroup; no conjugation changes the marking.

Source: Aschbacher–Smith, proof of 13.9.1, printed pp.973–974. The eventual
application takes D = T₂, after the two local Klein-four cores generate it.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The literal D factor, once generated inside H, is Sylow in H. -/
theorem exists_terminal_sylow_of_sylow_product
    (E D : Subgroup G) [IsMulCommutative E] (hE : IsPGroup 2 E)
    (S : Sylow 2 (centralizer (E : Set G)))
    (e : E × D ≃* S)
    (he : ∀ a b, (((e (a, b) : S) : centralizer (E : Set G)) : G) =
      (a : G) * (b : G))
    (hD : D ≤ terminal E) :
    ∃ P : Sylow 2 (terminal E), (P : Subgroup (terminal E)).map (terminal E).subtype = D := by
  let C := centralizer (E : Set G)
  let R := pResidual 2 C
  have hd := disjoint_terminal_of_sylow_product E D hE S e he
  have hintersection : ((S : Subgroup C).map C.subtype) ⊓ terminal E = D := by
    apply le_antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hxH⟩
      obtain ⟨⟨a, b⟩, hab⟩ := e.surjective (⟨s, hs⟩ : S)
      have hx : (s : G) = (a : G) * (b : G) := by
        rw [← he a b]
        exact congrArg (fun q : S => ((q : C) : G)) hab.symm
      have haH : (a : G) ∈ terminal E := by
        have h := (terminal E).mul_mem hxH ((terminal E).inv_mem (hD b.property))
        change (s : G) * (b : G)⁻¹ ∈ terminal E at h
        rwa [hx, mul_inv_cancel_right] at h
      have ha1 := disjoint_def.mp hd a.property haH
      change (s : G) ∈ D
      rw [hx, ha1, one_mul]
      exact b.property
    · intro d hdD
      refine ⟨?_, hD hdD⟩
      have hdEq := he 1 (⟨d, hdD⟩ : D)
      simp only [Subgroup.coe_one, one_mul] at hdEq
      exact ⟨(e (1, ⟨d, hdD⟩) : C), (e (1, ⟨d, hdD⟩)).property, hdEq⟩
  obtain ⟨P, hP⟩ := S.exists_sylow_map_eq_inf_of_normal R
  let eR : R ≃* terminal E := R.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨P.mapSurjective (f := eR.toMonoidHom) eR.surjective, ?_⟩
  change ((P : Subgroup R).map eR.toMonoidHom).map (terminal E).subtype = D
  calc
    _ = ((P : Subgroup R).map R.subtype).map C.subtype := by
      rw [map_map, map_map]
      rfl
    _ = ((S : Subgroup C) ⊓ R).map C.subtype := by rw [hP]
    _ = ((S : Subgroup C).map C.subtype) ⊓ terminal E :=
      Subgroup.map_inf _ _ C.subtype C.subtype_injective
    _ = D := hintersection

end CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
