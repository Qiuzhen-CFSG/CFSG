module
public import Stellmacher.Recognition.Parrott.SylowSeedOuterData
public import Stellmacher.Recognition.Parrott.SylowSeedOuterGeometry
public import Stellmacher.Recognition.Parrott.OuterInvolutionClassSeparation
public import Stellmacher.Recognition.Parrott.SylowSeedLastComputations

/-!
# Selecting the last central factor in Parrott's Sylow calculation

For the supplied seed normalized through (18), conjugation by dxd sends
 y=x²z to yaz, and conjugation once more by u sends it to yatz. Therefore
 the alternative [y,c]=at would conjugate y to yz inside H=C_G(z).
 Separation of these two H-classes selects [y,c]=atz without assuming a
 global class for the actual y or transporting an order-four root.

This module proves the word calculation and selects the central factor from
 the commutator alternatives using the established nonfusion theorem.
 It also records the obstruction to deducing all last relations for an
 arbitrary literal seed: the residual change (a,b,c,d) ↦ (at,bv,cu,dw)
 preserves the middle relations but changes the proposed x,c commutator.
 Thus an additional coordinate choice is necessary for final assembly.
 No completed frame or recognition theorem is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
 printed p.680, paragraph preceding equation (19). Conjugation by u makes
 the comparison with yat explicit in the present commutator convention.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
  {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowSeedData n false)

private theorem pc_conj {p q r : G} (h : Tits.parrottCommutator p q = r) :
    q⁻¹*p*q=p*r := by
  rw [← h, Tits.parrottCommutator]
  group

private theorem pc_conj_rev {p q r : G} (h : Tits.parrottCommutator p q = r)
    (hr : r^2=1) : p⁻¹*q*p=q*r := by
  have hi : r⁻¹=r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr)
  rw [← hi, ← h, Tits.parrottCommutator]
  group

private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by
  rw [← mul_assoc, h]

/-- The middle relations already determine this conjugate of the actual y. -/
public theorem y_conj_dxd (hm : f.OuterMiddleRelations) :
    (f.d*f.x*f.d)⁻¹*(f.x^2*z)*(f.d*f.x*f.d) =
      (f.x^2*z)*f.a*z := by
  let y := f.x^2*z
  let α : G ≃* G := MulAut.conj f.d⁻¹
  let β : G ≃* G := MulAut.conj f.x⁻¹
  have αeq (g : G) : α g = f.d⁻¹*g*f.d := by simp [α]
  have βeq (g : G) : β g = f.x⁻¹*g*f.x := by simp [β]
  have yd : α y = y*(f.b*f.w) := by rw [αeq]; exact pc_conj hm.eq17_yd
  have yx : β y = y := by
    rw [βeq]
    change f.x⁻¹*(f.x^2*z)*f.x = f.x^2*z
    simp only [mul_assoc, f.relations.comm_zx.eq]
    group
  have bx : β f.b = f.b*f.a := by rw [βeq]; exact pc_conj hm.eq18_bx
  have wx : β f.w = f.w*f.u := by
    rw [βeq]; exact pc_conj_rev f.relations.eq01_xw f.relations.u_sq
  have bd : α f.b = f.b*n.v := by
    rw [αeq]; exact pc_conj_rev f.relations.eq03_db f.relations.v_sq
  have ad : α f.a = f.a*f.u := by
    rw [αeq]; exact pc_conj (by simpa using f.relations.eq11_ad)
  have wd : α f.w = f.w := by
    rw [αeq]; simpa using pc_conj_rev f.relations.eq07_dw (one_pow 2)
  have ud : α f.u = f.u := by
    rw [αeq]; simpa using pc_conj_rev f.relations.eq08_du (one_pow 2)
  have wb := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.relations.eq02_bw).symm.eq
  have wv := f.relations.comm_vw.symm.eq
  have wa : f.w*f.a=f.a*f.w*z := by
    have he := (Tits.parrottCommutator_eq_iff _ _ _).mp f.relations.eq02_aw
    have hi : z⁻¹=z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.relations.z_sq)
    calc
      f.w*f.a = f.a*f.w*z⁻¹ := by rw [he]; group
      _ = _ := by rw [hi]
  have bb : f.b*f.b=n.v := by simpa only [pow_two] using f.relations.eq03_b
  have vv : n.v*n.v=1 := by simpa only [pow_two] using f.relations.v_sq
  have ww : f.w*f.w=1 := by simpa only [pow_two] using f.relations.w_sq
  have uu : f.u*f.u=1 := by simpa only [pow_two] using f.relations.u_sq
  calc
    _ = α (β (α y)) := by rw [αeq, βeq, αeq]; dsimp only [y]; group
    _ = (y*(f.b*f.w)) * ((f.b*n.v)*(f.a*f.u)) * (f.w*f.u) := by
      simp only [yd, map_mul, yx, bx, wx, bd, ad, wd, ud, mul_assoc]
    _ = y*f.a*z := by
      simp only [mul_assoc, tail wb, tail bb, tail wv, tail vv,
        one_mul, tail wa, tail f.relations.comm_uw.eq,
        f.relations.comm_zw.eq, tail ww, uu, mul_one]

/-- An explicit element of the supplied Sylow sends y to yatz. -/
public theorem y_conj_dxdu (hm : f.OuterMiddleRelations) :
    (f.d*f.x*f.d*f.u)⁻¹*(f.x^2*z)*(f.d*f.x*f.d*f.u) =
      (f.x^2*z)*f.a*n.t*z := by
  let y := f.x^2*z
  have huy : Tits.parrottCommutator f.u y = n.t := by
    change f.u⁻¹ * y⁻¹ * f.u * y = n.t
    rw [mul_assoc f.u⁻¹, mul_assoc f.u⁻¹,
      f.relations.square_mul_z_action.2.1, inv_mul_cancel_left]
  have hyu : f.u⁻¹*y*f.u = y*n.t := pc_conj_rev huy f.relations.t_sq
  have hau : f.u⁻¹*f.a*f.u=f.a := by
    rw [mul_assoc, f.relations.comm_au.eq, inv_mul_cancel_left]
  have hzu : f.u⁻¹*z*f.u=z := by
    rw [mul_assoc, f.relations.comm_zu.eq, inv_mul_cancel_left]
  calc
    _ = f.u⁻¹ * ((f.d*f.x*f.d)⁻¹*y*(f.d*f.x*f.d)) * f.u := by dsimp only [y]; group
    _ = f.u⁻¹*(y*f.a*z)*f.u := by rw [f.y_conj_dxd hm]
    _ = (f.u⁻¹*y*f.u)*(f.u⁻¹*f.a*f.u)*(f.u⁻¹*z*f.u) := by group
    _ = y*f.a*n.t*z := by rw [hyu, hau, hzu, mul_assoc y n.t,
      f.relations.comm_at.symm.eq, ← mul_assoc y f.a]

/-- Separation of y and yz inside C_G(z) selects the central factor in (19).
The nonfusion input is local; no global class of y is assumed. -/
public theorem eq19_yc_of_alternative_of_nonfusion (hm : f.OuterMiddleRelations)
    (hnf : ∀ q : centralizer ({z} : Set G),
      (q : G)*(f.x^2*z)*(q : G)⁻¹ ≠ (f.x^2*z)*z)
    (halt : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t ∨
      Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z := by
  rcases halt with hc | hc
  · exfalso
    let H := centralizer ({z} : Set G)
    let y := f.x^2*z
    let g := f.d*f.x*f.d*f.u
    have hd : f.d ∈ H := mem_centralizer_singleton_iff.mpr f.relations.comm_zd.symm
    have hx : f.x ∈ H := mem_centralizer_singleton_iff.mpr f.relations.comm_zx.symm
    have hu : f.u ∈ H := mem_centralizer_singleton_iff.mpr f.relations.comm_zu.symm
    have hcH : f.c ∈ H := mem_centralizer_singleton_iff.mpr f.relations.comm_zc.symm
    have hg : g ∈ H := mul_mem (mul_mem (mul_mem hd hx) hd) hu
    let q : H := ⟨f.c*g⁻¹, mul_mem hcH (inv_mem hg)⟩
    apply hnf q
    change (f.c*g⁻¹)*y*(f.c*g⁻¹)⁻¹=y*z
    calc
      _ = f.c*(g⁻¹*y*g)*f.c⁻¹ := by group
      _ = f.c*(y*f.a*n.t*z)*f.c⁻¹ := by rw [f.y_conj_dxdu hm]
      _ = f.c*((f.c⁻¹*y*f.c)*z)*f.c⁻¹ := by rw [pc_conj hc]; dsimp only [y]; group
      _ = y*z := by
        calc
          _ = y*(f.c*z)*f.c⁻¹ := by group
          _ = _ := by rw [f.relations.comm_zc.symm.eq]; group
  · exact hc

/-- The established seed nonfusion theorem discharges the local class input.
Only the commutator-coset alternative remains to select this central factor. -/
public theorem eq19_yc_of_alternative [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) (hm : f.OuterMiddleRelations)
    (halt : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t ∨
      Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z :=
  f.eq19_yc_of_alternative_of_nonfusion hm (f.square_mul_z_nonfusion hns hN h) halt

/-- Any middle seed gives a middle seed failing the last relations, with the
same marked data n. This obstruction requires no choice of global y-class. -/
public theorem exists_middle_seed_not_outer_last (hm : f.OuterMiddleRelations) :
    ∃ f' : ParrottSylowSeedData n false,
      f'.OuterMiddleRelations ∧ ¬ f'.OuterLastRelations := by
  by_cases hx : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v
  · exact ⟨f.residual, f.residual_middle hm, fun hl => f.residual_xc_ne hx hl.eq19_xc⟩
  · exact ⟨f, hm, fun hl => hx hl.eq19_xc⟩

/-- In the presence of the supplied middle seed, the requested universal
literal-seed implication is false. Ambient simplicity, nonsolvability and
the N₂ condition cannot remove a symmetry inside this same group. -/
public theorem not_forall_outer_last_relations (hm : f.OuterMiddleRelations) :
    ¬ ∀ f' : ParrottSylowSeedData n false,
      f'.OuterMiddleRelations → f'.OuterLastRelations := by
  obtain ⟨f', hm', hn⟩ := f.exists_middle_seed_not_outer_last hm
  exact fun hall => hn (hall f' hm')

end Stellmacher.Recognition.ParrottSylowSeedData
