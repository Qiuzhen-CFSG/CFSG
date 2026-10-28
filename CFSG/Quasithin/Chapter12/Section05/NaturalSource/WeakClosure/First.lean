module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.First.Geometry
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.First.Actor
public import Theory.Representation.SL5ExteriorSquare.RadicalGeneration

/-!
# The first exterior weak-closure alternative

The generator calculation puts W₁ in the radical preimage. Every L₆-conjugate
of W₁ is consequently contained in T; weak closure makes L₆ normalize W₁.
Its image is normalized by the entire four-space parabolic, so the intrinsic
shear-generation theorem gives the actual W̄₁ = R̄₆ alternative whenever W₁
moves V. Geometry also supplies W₁ ≤ C_G(V₆), C_G(C₁) ≤ M and the original
H-star generation-one exclusion.

Source: Aschbacher--Smith, 12.5.10 and 12.5.11(1), printed p.821.
The earlier numerical and point-fusion inputs remain with the exterior
fusion assembly; the local G₆ bound remains with the local analysis.
No L₆ normalization, irreducibility or actor-image premise remains.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open SylowExteriorMarking
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

theorem L₆_normalizes_first_of_radical (s : SylowExteriorMarking D)
    (hR : s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) ≤
      SL5ExteriorSquare.parabolicResidualTwoCore 4) :
    s.marking.Li 6 ≤ normalizer (indexedWeakClosure V (T : Subgroup G) 1 : Set G) := by
  let W := indexedWeakClosure V (T : Subgroup G) 1
  let H := L ⊔ (T : Subgroup G)
  have hWH : W ≤ H := (indexedWeakClosure_le _ _ _).trans le_sup_right
  intro l hl
  let lH : H := ⟨l, ((s.marking.Li_le_L 6).trans le_sup_left) hl⟩
  have hlI : s.actor lH ∈ SL5ExteriorSquare.parabolic 4 := by
    rw [← actorImage_L₆ s]
    exact ⟨lH, hl, rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply weakClosure_weakly_closed V (T : Subgroup G) 1 l
  rintro x ⟨w, hw, rfl⟩
  let wH : H := ⟨w, hWH hw⟩
  have hwR : s.actor wH ∈ SL5ExteriorSquare.parabolicResidualTwoCore 4 :=
    hR ⟨wH, hw, rfl⟩
  have hcR := (mem_normalizer_iff.mp
    (SL5ExteriorSquare.parabolic_four_normalizes_radicalSix hlI) (s.actor wH)).mp hwR
  rw [← actor_preimage_flag_eq_sylow s]
  refine ⟨lH * wH * lH⁻¹, ?_, rfl⟩
  change s.actor (lH * wH * lH⁻¹) ∈ SL5ExteriorSquare.flagGroup
  rw [map_mul, map_mul, map_inv]
  exact SL5ExteriorSquare.radicalSix_le_flagGroup hcR

theorem parabolic_normalizes_first_actorImage (s : SylowExteriorMarking D)
    (hR : s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) ≤
      SL5ExteriorSquare.parabolicResidualTwoCore 4) :
    SL5ExteriorSquare.parabolic 4 ≤ normalizer
      (s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) : Set SL5TenDimensional.Group) := by
  let W := indexedWeakClosure V (T : Subgroup G) 1
  let H := L ⊔ (T : Subgroup G)
  have hn := L₆_normalizes_first_of_radical s hR
  have hlocal : (s.marking.Li 6).subgroupOf H ≤ normalizer (W.subgroupOf H : Set H) := by
    intro l hl
    apply mem_normalizer_iff.mpr
    intro w
    exact mem_normalizer_iff.mp (hn hl) (w : G)
  rw [← actorImage_L₆ s]
  exact (map_mono hlocal).trans ((W.subgroupOf H).le_normalizer_map s.actor)

/-- Original 12.5.10(1), with the actual first weak closure and literal R₆. -/
theorem first_alternative (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3) :
    indexedWeakClosure V (T : Subgroup G) 1 ≤ centralizer (V : Set G) ∨
      s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) =
        s.actorImage (s.marking.Ri 6) := by
  let W := indexedWeakClosure V (T : Subgroup G) 1
  by_cases hc : W ≤ centralizer (V : Set G)
  · exact Or.inl hc
  right
  have hR := first_actorImage_le_radical s p hr hs
  have hne : s.actorImage W ≠ ⊥ := by
    intro he
    have hf := s.subspace_fixedSpace ((indexedWeakClosure_le V (T : Subgroup G) 1).trans
      (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)))
    rw [he, BinaryOffender.fixedSpace_bot, s.marking.subspace_top] at hf
    exact hc (le_centralizer_iff.mpr (inf_eq_left.mp hf.symm))
  rw [actorImage_R₆ s]
  apply le_antisymm hR
  rw [SL5ExteriorSquare.parabolicResidualTwoCore_four] at hR ⊢
  exact SL5ExteriorSquare.shearSubgroup_le_of_normalized_nontrivial hR hne
    (parabolic_normalizes_first_actorImage s (first_actorImage_le_radical s p hr hs))

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
