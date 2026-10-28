module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter.Size
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour

/-!
# The point parabolics inside the native J₄ max4 subgroup

An index-five subgroup of the literal quotient S₅ × SL₃(2) contains the
second factor: otherwise its restriction would give a faithful action of
SL₃(2) on at most five cosets. The first projection then has order 24 and
is a stabilizer in the actual five-letter action.

For a subgroup of the native max4 containing an ambient Sylow two-subgroup
with relative index 63, the native normal two-kernel lies in that same
Sylow. The certified core and quotient orders give index five, so the
subgroup is the full inverse image of a point stabilizer times SL₃(2).
No placement in max4 is asserted for arbitrary J₄ parabolics. The original
exterior-source application is in NaturalSource/Local/Normalizers/JankoMax4.

Source: Aschbacher–Smith, proof of 12.5.3, printed p.818/PDF p.835;
the native matrix projection and its ATLAS provenance are in `Quotient`.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear

/-- Index-five subgroups are point stabilizers in the specified product action. -/
theorem quotient_index_five (H : Subgroup QuotientModel) (hH : H.index = 5) :
    ∃ j : Fin 5, H = (MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤ := by
  let f : QuotientModel →* Equiv.Perm (Fin 5) := MonoidHom.fst _ _
  let g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* QuotientModel := MonoidHom.inr _ _
  have hi : (H.comap g).index ≤ 5 := by
    rw [index_comap]
    have hb := H.relIndex_le_of_le_right (show g.range ≤ ⊤ from le_top)
      (by simpa only [relIndex_top_right, hH] using (by decide : (5 : ℕ) ≠ 0))
    simpa only [relIndex_top_right, hH] using hb
  have hfull : H.comap g = ⊤ := by
    let := Atlas.Comparisons.Exceptional.sl3Two_simple
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le hi
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    exact lt_of_le_of_lt hb (by decide)
  have hk : f.ker ≤ H := by
    intro x hx
    have hx1 : x.1 = 1 := hx
    have hm : x.2 ∈ H.comap g := hfull ▸ mem_top _
    change (1, x.2) ∈ H at hm
    simpa only [← hx1] using hm
  have hf : Function.Surjective f := fun x => ⟨(x, 1), rfl⟩
  have hidx : (H.map f).index = 5 := (H.index_map_eq hf hk).trans hH
  have hcard : Nat.card (H.map f) = 24 := by
    have hc := (H.map f).card_mul_index
    rw [hidx, Nat.card_perm, Nat.card_fin] at hc
    change Nat.card (H.map f) * 5 = 120 at hc
    omega
  obtain ⟨j, hj⟩ := Theory.SpecificGroups.Alternating.FivePointTwentyFour.exists_eq_stabilizer
    (H.map f) hcard
  refine ⟨j, ?_⟩
  rw [← H.comap_map_eq_self hk, hj]
  ext x
  simp only [mem_comap, mem_prod, mem_top, and_true]
  rfl


/-- The full preimage of a point stabilizer under the actual max4 projection. -/
@[expose] def pointParabolic (j : Fin 5) : Subgroup Model :=
  (((MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤).comap
    max4Projection).map max4Subgroup.subtype

/-- The exact order follows from the certified core and literal quotient. -/
theorem max4_card : Nat.card max4Subgroup = 2 ^ 21 * 315 := by
  have hi : (pCore 2 max4Subgroup).index = 20160 := by
    change Nat.card (max4Subgroup ⧸ pCore 2 max4Subgroup) = 20160
    rw [Nat.card_congr max4QuotientEquiv.toEquiv, quotientModel_card]
  have hc := (pCore 2 max4Subgroup).card_mul_index
  rw [twoCore_card, hi] at hc
  exact hc.symm

/-- Within max4, the original Sylow index determines a literal point preimage. -/
theorem parabolic_eq_point (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : (S : Subgroup Model) ≤ H) (hHM : H ≤ max4Subgroup)
    (hi : (S : Subgroup Model).relIndex H = 63) :
    ∃ j : Fin 5, H = pointParabolic j := by
  let R := S.subtype (hSH.trans hHM)
  let J := H.subgroupOf max4Subgroup
  have hRJ : (R : Subgroup max4Subgroup) ≤ J := comap_mono hSH
  have hk : max4Projection.ker ≤ J := by
    rw [max4Projection_kernel_eq_twoCore]
    exact pCore_isPGroup.le_sylow_of_normal R |>.trans hRJ
  have hRcard : Nat.card R = 2 ^ 21 := by
    rw [R.card_eq_multiplicity, max4_card]
    decide +kernel
  have hRidx : (R : Subgroup max4Subgroup).index = 315 := by
    have hc := (R : Subgroup max4Subgroup).card_mul_index
    rw [hRcard, max4_card] at hc
    omega
  have hrel : (R : Subgroup max4Subgroup).relIndex J = 63 := by
    change ((S : Subgroup Model).subgroupOf max4Subgroup).relIndex
      (H.subgroupOf max4Subgroup) = 63
    rw [relIndex_subgroupOf hHM]
    exact hi
  have hJidx : J.index = 5 := by
    have hc := relIndex_mul_index hRJ
    rw [hrel, hRidx] at hc
    omega
  have hidx : (J.map max4Projection).index = 5 :=
    (J.index_map_eq max4Projection_surjective hk).trans hJidx
  obtain ⟨j, hj⟩ := quotient_index_five (J.map max4Projection) hidx
  have he : J = ((MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤).comap
      max4Projection := by
    rw [← hj, comap_map_eq_self hk]
  refine ⟨j, ?_⟩
  rw [pointParabolic, ← he]
  exact (map_subgroupOf_eq_of_le hHM).symm


/-- The native incidence calculation respects a supplied equivalence and Sylow;
no model Sylow or replacement marking is selected. -/
theorem parabolic_eq_point_of_equiv {C : Type*} [Group C] [Finite C]
    (e : C ≃* Model) (S : Sylow 2 C) (H : Subgroup C)
    (hSH : (S : Subgroup C) ≤ H) (hHM : H.map e.toMonoidHom ≤ max4Subgroup)
    (hi : (S : Subgroup C).relIndex H = 63) :
    ∃ j : Fin 5, H.map e.toMonoidHom = pointParabolic j := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  apply parabolic_eq_point R (H.map e.toMonoidHom) (map_mono hSH) hHM
  change ((S : Subgroup C).map e.toMonoidHom).relIndex (H.map e.toMonoidHom) = 63
  exact (relIndex_map_map_of_injective (f := e.toMonoidHom)
    (S : Subgroup C) H e.injective).trans hi

end Janko4.LocalStructure.SymmetricLinear
