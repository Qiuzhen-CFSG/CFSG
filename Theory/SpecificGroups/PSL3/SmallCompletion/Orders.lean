module
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Parabolic indices with the full projective torus

The scalar character of each SL₃ parabolic has the vector or covector
stabilizer as its kernel. Its affine coordinates give the endpoint order.
Passing to PSL₃ cancels the common scalar kernel in the Borel index, giving
q + 1. The endpoint order is (q + 1)q³ times the actual projective torus
order; no assumption on gcd(3,q - 1) is made.

These counts feed the native four-path action in `NativePaths`.
Source: Aschbacher–Smith F.4.4–6, printed pp.274–277 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.SmallCompletion
variable (F : Type*) [Field F] [Finite F]

private def pointScale : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]
private def lineScale : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

private theorem point_order : Nat.card (pointParabolicSL F) =
    Nat.card (pointLocalSL F) * (Nat.card F - 1) := by
  let f := (pointScale F).toHomUnits
  have hf : Function.Surjective f := by
    intro u
    refine ⟨⟨pointTorus F u,(pointTorus_mem_borel F u).1⟩, ?_⟩
    apply Units.ext
    rfl
  have hk : f.ker = (pointLocalSL F).subgroupOf (pointParabolicSL F) := by
    ext g
    change f g = 1 ↔ g.val ∈ pointLocalSL F
    rw [mem_pointLocalSL_iff]
    have hp := (mem_pointParabolicSL_iff F g).mp g.property
    exact ⟨fun h => ⟨congrArg Units.val h,hp⟩,fun h => Units.ext h.1⟩
  have h := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,Nat.card_units,hk,
    Nat.card_congr (subgroupOfEquivOfLe (pointLocalSL_le F)).toEquiv] at h
  exact h.symm
private theorem line_order : Nat.card (lineParabolicSL F) =
    Nat.card (lineLocalSL F) * (Nat.card F - 1) := by
  let f := (lineScale F).toHomUnits
  have hf : Function.Surjective f := by
    intro u
    refine ⟨⟨lineTorus F u,(lineTorus_mem_borel F u).2⟩, ?_⟩
    apply Units.ext
    rfl
  have hk : f.ker = (lineLocalSL F).subgroupOf (lineParabolicSL F) := by
    ext g
    change f g = 1 ↔ g.val ∈ lineLocalSL F
    rw [mem_lineLocalSL_iff]
    have hp := (mem_lineParabolicSL_iff F g).mp g.property
    exact ⟨fun h => ⟨hp.1,hp.2,congrArg Units.val h⟩,fun h => Units.ext h.2.2⟩
  have h := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,Nat.card_units,hk,
    Nat.card_congr (subgroupOfEquivOfLe (lineLocalSL_le F)).toEquiv] at h
  exact h.symm

theorem card_parabolicSL (i : Bool) : Nat.card (parabolicSL F i) =
    Nat.card F^3 * (Nat.card F^2-1) * (Nat.card F-1) := by
  have hc : Nat.card (Matrix.SL2.Affine F) = Nat.card F^3 * (Nat.card F^2-1) := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl,
      Nat.card_fun, Nat.card_fin, Atlas.card_sl_two]
    ring
  cases i
  · change Nat.card (pointParabolicSL F) = _
    rw [point_order, Nat.card_congr (pointLocalAffineEquiv F).toEquiv,hc]
  · change Nat.card (lineParabolicSL F) = _
    rw [line_order, Nat.card_congr (lineLocalAffineEquiv F).toEquiv,hc]

private theorem borelSL_order : Nat.card (borelSL F) = Nat.card F^3 * (Nat.card F-1)^2 := by
  have hc := (BorelQuotient.borelSL_complement F).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (BorelQuotient.torusSL_le_borel F)).toEquiv,
    ← Nat.card_congr (BorelQuotient.torusSLEquiv F).toEquiv,
    Nat.card_prod, Nat.card_units, card_unipotentSL, ← pow_two] at hc
  exact hc.symm

omit [Finite F] in
theorem borel_le_parabolic (i : Bool) : borel F ≤ parabolic F i := by
  cases i
  · exact map_mono inf_le_left
  · exact map_mono inf_le_right

theorem borel_relIndex (i : Bool) : (borel F).relIndex (parabolic F i) = Nat.card F+1 := by
  have hle : borelSL F ≤ parabolicSL F i := by cases i <;> exact (by first | exact inf_le_left | exact inf_le_right)
  have he : parabolic F i = (parabolicSL F i).map (projection F) := by cases i <;> rfl
  rw [he,borel,relIndex_map_map,sup_eq_left.mpr (projection_ker_le_borelSL F),
    sup_eq_left.mpr ((projection_ker_le_borelSL F).trans hle)]
  have hc := ((borelSL F).subgroupOf (parabolicSL F i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,borelSL_order,card_parabolicSL] at hc
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h2 : Nat.card F^2-1 = (Nat.card F-1)*(Nat.card F+1) := by
    have ht := Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega)
    have hs := Nat.sub_add_cancel (show 1 ≤ Nat.card F^2 by nlinarith)
    nlinarith
  have hqm : 0 < Nat.card F-1 := by omega
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F^3*(Nat.card F-1)^2 by positivity)
  change Nat.card F^3*(Nat.card F-1)^2 * ((borelSL F).subgroupOf (parabolicSL F i)).index = _
  rw [hc,h2]
  ring

theorem card_borel {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card (borel F) = Nat.card F^3 * Nat.card (torus F) := by
  have h := (BorelQuotient.borel_complement F hF).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv,card_unipotent] at h
  exact h.symm

theorem card_parabolic {n : ℕ} (hF : Nat.card F = 2^n) (i : Bool) :
    Nat.card (parabolic F i) = (Nat.card F+1)*Nat.card F^3 * Nat.card (torus F) := by
  have h := ((borel F).subgroupOf (parabolic F i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic F i)).toEquiv,card_borel F hF] at h
  change _ * (borel F).relIndex (parabolic F i) = _ at h
  rw [borel_relIndex] at h
  exact h.symm.trans (by ring)
end Matrix.PSL3.SmallCompletion
