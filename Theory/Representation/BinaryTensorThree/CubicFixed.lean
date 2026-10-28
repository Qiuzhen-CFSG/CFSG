module
public import Theory.Representation.BinaryTensorThree.PlaneFixed
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Cubic fixed vectors in the binary three-by-three tensor

In a standard cubic Sylow subgroup, each pair of cubic matrices fixes an
explicit injective copy of a binary three-space. The matrices are checked
only on this small coordinate family. Sylow conjugacy then gives at least
eight fixed vectors for every element with cube one in the full tensor
wreath group. The possibly trivial action image is included.

This is the part of H.4.12(1) needed in 8.3.12: one individual cubic cannot
fix just the point line. The companion Chapter10 application retains both
the five-space/point quotient and the original module/point-core quotient.
Source: Aschbacher--Smith H.4.12(1) and 8.3.12, printed pp.385,726,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation.BinaryOffender
open scoped TensorProduct
namespace BinaryTensorThree.CubicFixed
open PlaneFixed Matrix.PSL3Two
private def model (a b : Three) (x : Natural) : Space :=
  if a = 1 then !![0,0,x 0;0,0,x 1;0,0,x 2]
  else if b = 1 then !![0,0,0;0,0,0;x 0,x 1,x 2]
  else if a = b then !![x 0,x 1,0;x 0+x 1,x 0,0;0,0,x 2]
  else !![x 0,x 1,0;x 1,x 0+x 1,0;0,0,x 2]
private def extract (a b : Three) (X : Space) : Natural :=
  if a = 1 then ![X 0 2,X 1 2,X 2 2]
  else if b = 1 then ![X 2 0,X 2 1,X 2 2]
  else ![X 0 0,X 0 1,X 2 2]
private theorem model_fixed : ∀ a b : Three, ∀ x : Natural,
    (cubic a).val * model a b x * (cubic b).val.transpose = model a b x := by
  decide +kernel
private theorem extract_model : ∀ a b : Three, ∀ x : Natural,
    extract a b (model a b x) = x := by decide +kernel

private theorem matrix_action (a b : SL) (X : Space) :
    action (PointParabolic.tensorHom (pair (a,b))) X = a.val * X * b.val.transpose := by
  rw [tensor_pair,action_baseEmbedding]
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [baseAction_tmul]
    ext i j
    change (a.val.mulVec x) i * (b.val.mulVec y) j = _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,coordinates_tmul,
      Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  | add x y hx hy => simp [map_add,Matrix.mul_add,Matrix.add_mul,hx,hy]

private theorem model_fixed_card (a : Three × Three) :
    8 ≤ Nat.card (fixedSpace (action.comp PointParabolic.tensorHom) (zpowers (cubicPair a))) := by
  let f : Natural → fixedSpace (action.comp PointParabolic.tensorHom) (zpowers (cubicPair a)) :=
    fun x => ⟨model a.1 a.2 x,by
      rw [mem_fixedSpace_zpowers_iff]
      change action (PointParabolic.tensorHom (pair (cubic a.1,cubic a.2))) _ = _
      rw [matrix_action]
      exact model_fixed a.1 a.2 x⟩
  have hf : Function.Injective f := by
    intro x y h
    have he := congrArg (fun w => extract a.1 a.2 w.val) h
    simpa only [f,extract_model] using he
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun,Nat.card_zmod,Nat.card_fin,show 2^3 = 8 by decide] using hc

private theorem model_codim (a : Three × Three) :
    fixedCodim (action.comp PointParabolic.tensorHom) (zpowers (cubicPair a)) ≤ 6 := by
  have hc := model_fixed_card a
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hl : 3 ≤ Module.finrank (ZMod 2)
      (fixedSpace (action.comp PointParabolic.tensorHom) (zpowers (cubicPair a))) :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hd := fixedCodim_add_finrank (action.comp PointParabolic.tensorHom) (zpowers (cubicPair a))
  have hV : Module.finrank (ZMod 2) Space = 9 := by rw [Module.finrank_matrix]; norm_num
  omega

private def cubicSylow : Sylow 3 Actor := Sylow.ofCard cubicPair.range (by
  rw [card_cubic_range,RegularWreathProduct.card,card_SL]
  change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
  rw [Nat.card_zmod]
  decide +kernel)

/-- Every individual cubic in the actual matrix wreath action moves at most six dimensions. -/
theorem actor_cube_fixedCodim_le_six (g : Actor) (hg : g^3 = 1) :
    fixedCodim (action.comp PointParabolic.tensorHom) (zpowers g) ≤ 6 := by
  have hp : IsPGroup 3 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq Actor S cubicSylow
  have hmem : k*g*k⁻¹ ∈ cubicPair.range := by
    have he := congrArg Sylow.toSubgroup hk
    change (S : Subgroup Actor).map (MulAut.conj k).toMonoidHom = cubicPair.range at he
    rw [←he]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom (hS (mem_zpowers g))
  obtain ⟨a,ha⟩ := hmem
  have hh := model_codim a
  rw [ha,fixedCodim_zpowers_conj] at hh
  exact hh

/-- H.4.12(1), expressed as the needed moved-dimension bound of each cubic. -/
theorem cube_fixedCodim_le_six (g : BinaryTensorThree.Group) (hg : g^3 = 1) :
    fixedCodim action (zpowers g) ≤ 6 := by
  let a := PointParabolic.actorEquiv.symm g
  have ha : a^3 = 1 := by rw [←map_pow,hg,map_one]
  have hh := actor_cube_fixedCodim_le_six a ha
  unfold fixedCodim at hh
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hh
  have he : PointParabolic.tensorHom a = g := by
    rw [←PointParabolic.actorEquiv_apply]
    exact PointParabolic.actorEquiv.apply_symm_apply g
  rwa [he] at hh

/-- The source contradiction needs these three independent fixed vectors;
this statement permits a trivial cubic image and retains the action kernel. -/
theorem cube_fixed_card_ge_eight (g : BinaryTensorThree.Group) (hg : g^3 = 1) :
    8 ≤ Nat.card (fixedSpace action (zpowers g)) := by
  have hc := cube_fixedCodim_le_six g hg
  have hd := fixedCodim_add_finrank action (zpowers g)
  have hV : Module.finrank (ZMod 2) Space = 9 := by rw [Module.finrank_matrix]; norm_num
  have hl : 3 ≤ Module.finrank (ZMod 2) (fixedSpace action (zpowers g)) := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hl
end BinaryTensorThree.CubicFixed
