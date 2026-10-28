module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction.Action
public import Theory.ElementaryAbelian.MarkedEightCoordinates
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag

/-!
# The marked elementary-eight automorphism calculation

Coordinates adapted to the actual point and plane identify both stabilizers
under one action-compatible automorphism equivalence. Residual functoriality
then gives their cubic core quotients and their generation. The same coordinate
map transports the plane displacements, giving the full elementary group.
These are exactly the four finite inputs of the natural flag constructor.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), pp.849,1009.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
namespace ElementaryEight
open Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {E : Type*} [Group E]

private theorem stabilizer_map (e : Model ≃* E) (P : Subgroup Model) :
    (MulAction.stabilizer (MulAut Model) P).map (MulAut.congr e).toMonoidHom =
      flagStabilizer (P.map e.toMonoidHom) := by
  ext g
  obtain ⟨g, rfl⟩ := (MulAut.congr e).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change g ∈ MulAction.stabilizer (MulAut Model) P ↔
    MulAut.congr e g ∈ MulAction.stabilizer (MulAut E) (P.map e.toMonoidHom)
  rw [stabilizer_iff, stabilizer_iff]
  constructor
  · intro hg x
    obtain ⟨x, rfl⟩ := e.surjective x
    change e (g (e.symm (e x))) ∈ P.map e.toMonoidHom ↔ e x ∈ P.map e.toMonoidHom
    simpa only [Subgroup.mem_map_equiv, e.symm_apply_apply] using hg x
  · intro hg x
    have hx := hg (e x)
    change e (g (e.symm (e x))) ∈ P.map e.toMonoidHom ↔ e x ∈ P.map e.toMonoidHom at hx
    simpa only [Subgroup.mem_map_equiv, e.symm_apply_apply] using hx

private theorem residual_map (e : Model ≃* E) (P : Subgroup Model)
    (Q : Subgroup SL) (hQ :
      (MulAction.stabilizer (MulAut Model) P).comap slAut.toMonoidHom = Q) :
    (residual Q).map (slAut.trans (MulAut.congr e)).toMonoidHom =
      flagResidual (P.map e.toMonoidHom) := by
  have hs : Q.map slAut.toMonoidHom = MulAction.stabilizer (MulAut Model) P := by
    rw [← hQ, Subgroup.map_comap_eq_self_of_surjective slAut.surjective]
  change ((pResidual 2 Q).map Q.subtype).map
    (slAut.trans (MulAut.congr e)).toMonoidHom = _
  rw [map_embedded_pResidual]
  have hh : Q.map (slAut.trans (MulAut.congr e)).toMonoidHom =
      flagStabilizer (P.map e.toMonoidHom) := by
    change Q.map ((MulAut.congr e).toMonoidHom.comp slAut.toMonoidHom) = _
    rw [← Subgroup.map_map, hs, stabilizer_map]
  rw [hh]
  rfl

private theorem quotient_card (R : Subgroup SL) (S : Subgroup (MulAut E))
    (f : SL ≃* MulAut E) (h : R.map f.toMonoidHom = S)
    (hc : Nat.card (R ⧸ pCore 2 R) = 3) : Nat.card (coreQuotient S) = 3 := by
  let e : R ≃* S := (f.subgroupMap R).trans (MulEquiv.subgroupCongr h)
  let q := QuotientGroup.congr (pCore 2 R) (pCore 2 S) e (pCore_map_iso 2 e)
  exact (Nat.card_congr q.toEquiv).symm.trans hc

variable [Finite E] [IsElementaryAbelian 2 E]

/-- The four intrinsic calculations for an actual incident point and plane. -/
theorem calculation (hE : Nat.card E = 8) (A B : Subgroup E)
    (hA : Nat.card A = 2) (hB : Nat.card B = 4) (hAB : A ≤ B) :
    Nat.card (coreQuotient (flagResidual A)) = 3 ∧
    Nat.card (coreQuotient (flagResidual B)) = 3 ∧
    flagResidual A ⊔ flagResidual B = ⊤ ∧
    flagMovement B (flagResidual A) = ⊤ := by
  obtain ⟨e, heA, heB⟩ := coordinates hE A B hA hB hAB
  let f := slAut.trans (MulAut.congr e)
  have hRA : pointA.map f.toMonoidHom = flagResidual A := by
    have h := residual_map e point pointParabolicSL point_stabilizer
    rwa [point_residual, heA] at h
  have hRB : lineA.map f.toMonoidHom = flagResidual B := by
    have h := residual_map e plane lineParabolicSL plane_stabilizer
    rwa [line_residual, heB] at h
  refine ⟨quotient_card pointA _ f hRA card_point_core_quotient,
    quotient_card lineA _ f hRB card_line_core_quotient, ?_, ?_⟩
  · rw [← hRA, ← hRB, ← Subgroup.map_sup, residuals_generate,
      Subgroup.map_top_of_surjective _ f.surjective]
  · let D := (flagMovement B (flagResidual A)).comap e.toMonoidHom
    have hD : D = ⊤ := by
      apply plane_movement D
      intro b hb a ha
      change e (b * (slAut a b)⁻¹) ∈ flagMovement B (flagResidual A)
      have hbB : e b ∈ B := by rw [← heB]; exact ⟨b, hb, rfl⟩
      have haR : f a ∈ flagResidual A := by rw [← hRA]; exact ⟨a, ha, rfl⟩
      have hm : e b * (f a (e b))⁻¹ ∈ flagMovement B (flagResidual A) :=
        Subgroup.subset_closure ⟨e b, hbB, f a, haR, rfl⟩
      change e b * (e (slAut a (e.symm (e b))))⁻¹ ∈ flagMovement B (flagResidual A) at hm
      simpa only [map_mul, map_inv, e.symm_apply_apply] using hm
    apply top_unique
    intro x _
    obtain ⟨x, rfl⟩ := e.surjective x
    exact (show x ∈ D from hD ▸ mem_top x)

end ElementaryEight
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
