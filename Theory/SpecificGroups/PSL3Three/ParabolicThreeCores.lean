module

public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.PGroupCore

/-!
# The three-cores of the full parabolics in PSL₃(3)

The kernel of the lower-right block restriction on the first-line stabilizer
consists exactly of the matrices `!![1,a,b; 0,1,0; 0,0,1]`. Its two free
coordinates give order nine, and its kernel description proves normality in
the full parabolic. Given the parabolic order 432, the upper-unitriangular
subgroup of order 27 is Sylow three. The three-core lies in this subgroup and
in its conjugate by a determinant-one matrix exchanging the last two
coordinates; the intersection lies in the kernel.

Inverse transpose identifies the full first-line stabilizer with the
stabilizer of the complementary coordinate plane. The canonical SL₃(3) to
PSL₃(3) isomorphism then transports both intrinsic core orders. The order 432
of each parabolic remains the sole explicit premise of its cardinality theorem.

Source: the concrete parabolics underlying GLS III, Theorem 6.5.3(a),
`refs/KGroup/GLS3/chapter6.tex`; the PSL₃(3) case in Aschbacher–Smith,
combined 1 March 2004 manuscript, proof of Proposition 1.3.4,
printed p.511 (PDF p.528).
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Three
open Matrix.PSL3.LinearThree

private abbrev F := ZMod 3

private def lineBlock : lineStabilizerSL →* Matrix (Fin 2) (Fin 2) F where
  toFun g := !![g.1 1 1, g.1 1 2; g.1 2 1, g.1 2 2]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    obtain ⟨g10, g20⟩ := (mem_lineStabilizerSL_iff g.1).mp g.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, g10, g20]

private theorem line_kernel_shape (g : lineStabilizerSL) (hg : g ∈ lineBlock.ker) :
    g.1.val = !![1, g.1 0 1, g.1 0 2; 0, 1, 0; 0, 0, 1] := by
  obtain ⟨h10, h20⟩ := (mem_lineStabilizerSL_iff g.1).mp g.2
  have hb : lineBlock g = 1 := hg
  have h11 : g.1 1 1 = 1 := congr_fun (congr_fun hb 0) 0
  have h12 : g.1 1 2 = 0 := congr_fun (congr_fun hb 0) 1
  have h21 : g.1 2 1 = 0 := congr_fun (congr_fun hb 1) 0
  have h22 : g.1 2 2 = 1 := congr_fun (congr_fun hb 1) 1
  have h00 : g.1 0 0 = 1 := by
    have hd := g.1.property
    rw [Matrix.det_fin_three] at hd
    simpa [h10, h20, h11, h12, h21, h22] using hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h11, h12, h21, h22]

private def lineRoot (p : F × F) : lineStabilizerSL :=
  ⟨⟨!![1,p.1,p.2; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩,
    (mem_lineStabilizerSL_iff _).mpr ⟨rfl,rfl⟩⟩

private def lineKernelEquiv : F × F ≃ lineBlock.ker where
  toFun p := ⟨lineRoot p, by
    change lineBlock (lineRoot p) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  invFun g := (g.1.1 0 1, g.1.1 0 2)
  left_inv p := rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext (line_kernel_shape g.1 g.2).symm

private theorem card_line_kernel : Nat.card lineBlock.ker = 9 := by
  rw [← Nat.card_congr lineKernelEquiv, Nat.card_prod]
  norm_num [F, Nat.card_eq_fintype_card]

private theorem unipotent_le_line : unipotentSL F ≤ lineStabilizerSL := by
  intro g hg
  have h := (mem_unipotentSL_iff F g).mp hg
  rw [mem_lineStabilizerSL_iff, h]
  exact ⟨rfl, rfl⟩

private theorem card_line_unipotent :
    Nat.card ((unipotentSL F).subgroupOf lineStabilizerSL) = 27 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe unipotent_le_line).toEquiv, card_unipotentSL]
  norm_num [F, Nat.card_eq_fintype_card]

private def lineSwap : lineStabilizerSL :=
  ⟨⟨!![-1,0,0; 0,0,1; 0,1,0], by decide⟩,
    (mem_lineStabilizerSL_iff _).mpr ⟨rfl,rfl⟩⟩

private theorem lineSwap_inv : lineSwap⁻¹ = lineSwap := by decide

private theorem line_core_eq_kernel (hc : Nat.card lineStabilizerSL = 432) :
    pCore 3 lineStabilizerSL = lineBlock.ker := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Sylow 3 lineStabilizerSL := Sylow.ofCard
    ((unipotentSL F).subgroupOf lineStabilizerSL) (by
      rw [card_line_unipotent, hc, show 432 = 3 ^ 3 * 16 by decide,
        Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 16)]
      norm_num)
  have hle : pCore 3 lineStabilizerSL ≤ (unipotentSL F).subgroupOf lineStabilizerSL :=
    pCore_isPGroup.le_sylow_of_normal T
  have shape (x : lineStabilizerSL) (hx : x ∈ pCore 3 lineStabilizerSL) :
      x.1.val = !![1,x.1 0 1,x.1 0 2; 0,1,x.1 1 2; 0,0,1] :=
    (mem_unipotentSL_iff F x.1).mp (hle hx)
  apply le_antisymm
  · intro g hg
    have hu := shape g hg
    have hcg : lineSwap * g * lineSwap⁻¹ ∈ pCore 3 lineStabilizerSL :=
      (pCore_normal (p := 3) (G := lineStabilizerSL)).conj_mem g hg lineSwap
    rw [lineSwap_inv] at hcg
    have hv := shape (lineSwap * g * lineSwap) hcg
    have h21 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 1) hv
    have h12 : g.1 1 2 = 0 := by
      change (
        !![-1,0,0; 0,0,1; 0,1,0] * g.1.val * !![-1,0,0; 0,0,1; 0,1,0] :
          Matrix (Fin 3) (Fin 3) F) 2 1 = 0 at h21
      simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using h21
    have h11 : g.1 1 1 = 1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hu
    have h21 : g.1 2 1 = 0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 1) hu
    have h22 : g.1 2 2 = 1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) hu
    change lineBlock g = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lineBlock, h11, h12, h21, h22]
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (p := 3) (n := 2) card_line_kernel⟩

private theorem transpose_mul (g h : SL) :
    SpecialLinearGroup.transpose (g * h) =
      SpecialLinearGroup.transpose h * SpecialLinearGroup.transpose g :=
  Subtype.ext (Matrix.transpose_mul _ _)

private theorem transpose_inv (g : SL) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ :=
  Subtype.ext (Matrix.adjugate_transpose _)

private def contragredient : SL ≃* SL where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  invFun g := SpecialLinearGroup.transpose g⁻¹
  left_inv g := by
    change SpecialLinearGroup.transpose ((SpecialLinearGroup.transpose g⁻¹)⁻¹) = g
    rw [transpose_inv g, inv_inv]
    exact Subtype.ext (Matrix.transpose_transpose _)
  right_inv g := by
    change SpecialLinearGroup.transpose ((SpecialLinearGroup.transpose g⁻¹)⁻¹) = g
    rw [transpose_inv g, inv_inv]
    exact Subtype.ext (Matrix.transpose_transpose _)
  map_mul' g h := by rw [_root_.mul_inv_rev, transpose_mul]

private def parabolicDuality : lineStabilizerSL ≃* planeStabilizerSL where
  toFun g := ⟨contragredient g.1, (mem_planeStabilizerSL_iff _).mpr
    ((mem_lineStabilizerSL_iff _).mp (lineStabilizerSL.inv_mem g.2))⟩
  invFun g := ⟨contragredient g.1, (mem_lineStabilizerSL_iff _).mpr
    ((mem_planeStabilizerSL_iff _).mp (planeStabilizerSL.inv_mem g.2))⟩
  left_inv g := Subtype.ext (contragredient.left_inv g.1)
  right_inv g := Subtype.ext (contragredient.right_inv g.1)
  map_mul' g h := Subtype.ext (contragredient.map_mul g.1 h.1)

private noncomputable def lineProjectEquiv : lineStabilizerSL ≃* lineStabilizer :=
  lineStabilizerSL.equivMapOfInjective project project_injective

private noncomputable def planeProjectEquiv : planeStabilizerSL ≃* planeStabilizer :=
  planeStabilizerSL.equivMapOfInjective project project_injective

private theorem core_card_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (pCore 3 G) = Nat.card (pCore 3 H) := by
  rw [← pCore_map_iso 3 e, Subgroup.card_map_of_injective e.injective]

/-- The intrinsic three-core of the full first-line stabilizer has order nine,
assuming the order 432 of that parabolic. -/
theorem card_threeCore_lineStabilizer (hline : Nat.card lineStabilizer = 432) :
    Nat.card (pCore 3 lineStabilizer) = 9 := by
  have hc : Nat.card lineStabilizerSL = 432 :=
    (Nat.card_congr lineProjectEquiv.toEquiv).trans hline
  rw [← core_card_congr lineProjectEquiv, line_core_eq_kernel hc, card_line_kernel]

/-- The intrinsic three-core of the full complementary-plane stabilizer has
order nine, assuming the order 432 of that parabolic. -/
theorem card_threeCore_planeStabilizer (hplane : Nat.card planeStabilizer = 432) :
    Nat.card (pCore 3 planeStabilizer) = 9 := by
  let e : lineStabilizer ≃* planeStabilizer :=
    lineProjectEquiv.symm.trans (parabolicDuality.trans planeProjectEquiv)
  rw [← core_card_congr e]
  exact card_threeCore_lineStabilizer ((Nat.card_congr e.toEquiv).trans hplane)

end Matrix.PSL3Three
