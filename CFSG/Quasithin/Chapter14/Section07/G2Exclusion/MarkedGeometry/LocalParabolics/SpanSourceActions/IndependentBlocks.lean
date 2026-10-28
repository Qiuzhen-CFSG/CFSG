module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSaturation
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Independent blocks in the lifted-pencil action

Surjectivity onto two S₃ factors need not imply surjectivity onto their
product. A nontrivial two-group in the first factor that is killed by the
second factor removes this obstruction. Its normal closure in the first
factor is all S₃, since a normal even-order subgroup of S₃ is S₃ itself.

For the source action, O₂(H) supplies this independent action:
[V₂,O₂(H)]=V₁ is nontrivial, whereas its starred action kills U/V₁.
The full earlier action on V₂ is transported to the literal first block
by comparing the actual centralizer kernels. The quotient-block
surjectivity remains a separate premise here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.4(1),(2)
and 14.7.56(2), printed pp.1043 and 1066. Taking the normal closure inside
the block kernel implements the independent I₂=L₂O₂(H) action without
assuming normality of O₂(H) in N_G(V₂).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions

open Subgroup
private theorem normal_six_eq_top {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 6) (hcore : pCore 2 A = ⊥)
    (P : Subgroup A) [P.Normal] (heven : 2 ∣ Nat.card P) : P = ⊤ := by
  have hd : Nat.card P ∣ 6 := hA ▸ P.card_subgroup_dvd_card
  have hn : Nat.card P = 2 ∨ Nat.card P = 6 := by
    have hl := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hp := Nat.card_pos (α := P)
    interval_cases h : Nat.card P <;> norm_num at *
  rcases hn with h2 | h6
  · have hp : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by simpa using h2)
    have hle : P ≤ pCore 2 A := le_sSup ⟨inferInstance,hp⟩
    have he : P = ⊥ := bot_unique (hcore ▸ hle)
    rw [he,card_bot] at h2
    omega
  · exact eq_top_of_card_eq P (h6.trans hA.symm)

private theorem independent_blocks {X A B : Type*} [Group X] [Group A] [Group B]
    [Finite X] [Finite A] (hA : Nat.card A = 6) (hcore : pCore 2 A = ⊥)
    (f : X →* A × B)
    (hfirst : Function.Surjective ((MonoidHom.fst A B).comp f))
    (hsecond : Function.Surjective ((MonoidHom.snd A B).comp f))
    (Q : Subgroup X) (hQ : IsPGroup 2 Q)
    (hQker : Q ≤ ((MonoidHom.snd A B).comp f).ker)
    (hQne : Q.map ((MonoidHom.fst A B).comp f) ≠ ⊥) : Function.Surjective f := by
  let a := (MonoidHom.fst A B).comp f
  let b := (MonoidHom.snd A B).comp f
  let P := b.ker.map a
  have hn : P.Normal := Normal.map inferInstance a hfirst
  let := hn
  change Q.map a ≠ ⊥ at hQne
  have heven : 2 ∣ Nat.card P := by
    obtain ⟨n,hn⟩ := (hQ.map a).exists_card_eq
    have hpos : n ≠ 0 := by
      intro h0
      apply hQne
      apply card_eq_one.mp
      simpa [h0] using hn
    apply dvd_trans _ (card_dvd_of_le (map_mono hQker))
    rw [hn]
    exact dvd_pow_self 2 hpos
  have hP := normal_six_eq_top hA hcore P heven
  rintro ⟨x,y⟩
  obtain ⟨g,hg⟩ := hsecond y
  obtain ⟨k,hk,he⟩ := (show x * (a g)⁻¹ ∈ P by rw [hP]; trivial)
  refine ⟨k * g, Prod.ext ?_ ?_⟩
  · change a (k * g) = x
    rw [map_mul, he, inv_mul_cancel_right]
  · change b (k * g) = y
    rw [map_mul, MonoidHom.mem_ker.mp hk, one_mul]
    exact hg

open BinaryLinear BinaryLinear.FourParabolicRadical BinaryLinear.SmallParabolicLevi
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open SpanSaturation

private def planeCoordinates : plane ≃ₗ[ZMod 2] Vec where
  toFun x := x.val.1
  invFun x := ⟨(x,0),rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Subtype.ext
    change (x.val.1, 0) = x.val
    exact Prod.ext rfl x.property.symm
  right_inv _ := rfl

private theorem plane_GL_card : Nat.card (BinaryLinear.GL plane) = 6 := by
  let e := (linearGroupCongr planeCoordinates).trans linearTwoEquivSymmetricThree
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

variable {G : Type*} [Group G]

private theorem first_block_kernel
    (V D Y : Subgroup G) (hD : D ≤ V)
    (hspan : normalizer (D : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (D.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup) :
    ((subspaceAction plane).comp (spanCoordinateAction V D Y hD hspan E hE)).ker =
      (ambientAction (normalizer (D : Set G)) D le_rfl).ker := by
  let W := generatedLineFamily V Y
  have hDW := hD.trans (original_le_generated V Y)
  have hmem (w : W) : (E w).toAdd ∈ plane ↔ (w : G) ∈ D := by
    change E w ∈ plane.toAddSubgroup.toSubgroup ↔ w ∈ D.subgroupOf W
    rw [← hE,mem_map_equiv,E.symm_apply_apply]
  ext n
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  constructor
  · intro hn
    ext d
    let w : W := ⟨d,hDW d.property⟩
    let v : plane := ⟨(E w).toAdd, (hmem w).mpr d.property⟩
    have he := congrArg Subtype.val (LinearEquiv.congr_fun hn v)
    change (E (ambientAction _ _ hspan n (E.symm (E w)))).toAdd = (E w).toAdd at he
    rw [E.symm_apply_apply] at he
    have hw : ambientAction _ _ hspan n w = w :=
      E.injective (Multiplicative.toAdd.injective he)
    exact congrArg (fun w : W => (w : G)) hw
  · intro hn
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    let w := E.symm (Multiplicative.ofAdd v.val)
    have hwD : (w : G) ∈ D := (hmem w).mp (by simp only [w, E.apply_symm_apply]; exact v.property)
    have he := congrArg Subtype.val (MulEquiv.congr_fun hn ⟨w,hwD⟩)
    have hw : ambientAction _ _ hspan n w = w := Subtype.ext he
    change (E (ambientAction _ _ hspan n w)).toAdd = v.val
    rw [hw]
    exact congrArg Multiplicative.toAdd (E.apply_symm_apply _)

private theorem first_block_surjective [Finite G]
    (V D Y : Subgroup G) [IsElementaryAbelian 2 D] (hcD : Nat.card D = 4)
    (hD : D ≤ V)
    (hspan : normalizer (D : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (D.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hfull : Function.Surjective (ambientAction (normalizer (D : Set G)) D le_rfl)) :
    Function.Surjective ((subspaceAction plane).comp (spanCoordinateAction V D Y hD hspan E hE)) := by
  let : Finite (BinaryLinear.GL plane) := Finite.of_injective
    (fun a : BinaryLinear.GL plane => (a : plane → plane)) DFunLike.coe_injective
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcD]; decide)
  let : IsKleinFour D := ⟨hcD, IsElementaryAbelian.exponent_eq_prime⟩
  let f := (subspaceAction plane).comp (spanCoordinateAction V D Y hD hspan E hE)
  have hc : Nat.card f.range = Nat.card (BinaryLinear.GL plane) := by
    rw [← index_ker, first_block_kernel V D Y hD hspan E hE, index_ker,
      MonoidHom.range_eq_top.mpr hfull, card_top, IsKleinFour.card_mulAut, plane_GL_card]
  exact MonoidHom.range_eq_top.mp (eq_top_of_card_eq f.range hc)

/-- A genuine independent two-action upgrades the two factor actions to
surjectivity of the literal joint block homomorphism. -/
theorem joint_block_surjective_of_independent_two_action [Finite G]
    (V D Y Q : Subgroup G) [IsElementaryAbelian 2 D] (hcD : Nat.card D = 4)
    (hD : D ≤ V)
    (hspan : normalizer (D : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (D.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hfull : Function.Surjective (ambientAction (normalizer (D : Set G)) D le_rfl))
    (hsecond : Function.Surjective ((quotientAction plane).comp
      (spanCoordinateAction V D Y hD hspan E hE)))
    (hQ : IsPGroup 2 Q) (hQN : Q ≤ normalizer (D : Set G))
    (hQD : ⁅D,Q⁆ ≠ ⊥) (hQW : ⁅generatedLineFamily V Y,Q⁆ ≤ D) :
    Function.Surjective ((blockAction plane).comp
      (spanCoordinateAction V D Y hD hspan E hE)) := by
  let : Finite (BinaryLinear.GL plane) := Finite.of_injective
    (fun a : BinaryLinear.GL plane => (a : plane → plane)) DFunLike.coe_injective
  let f := (blockAction plane).comp (spanCoordinateAction V D Y hD hspan E hE)
  let a := (MonoidHom.fst (BinaryLinear.GL plane) (BinaryLinear.GL (BSpace ⧸ plane))).comp f
  let b := (MonoidHom.snd (BinaryLinear.GL plane) (BinaryLinear.GL (BSpace ⧸ plane))).comp f
  let QN := Q.subgroupOf (normalizer (D : Set G))
  have ha : a = (subspaceAction plane).comp (spanCoordinateAction V D Y hD hspan E hE) := rfl
  have hb : b = (quotientAction plane).comp (spanCoordinateAction V D Y hD hspan E hE) := rfl
  have hp : IsPGroup 2 QN := hQ.of_equiv (subgroupOfEquivOfLe hQN).symm
  have hker : QN ≤ b.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.eq plane).mpr
      let W := generatedLineFamily V Y
      let w := E.symm (Multiplicative.ofAdd v)
      have hd : ambientAction _ W hspan n w / w ∈ D.subgroupOf W := by
        simp only [div_eq_mul_inv]
        change (n : G) * (w : G) * (n : G)⁻¹ * (w : G)⁻¹ ∈ D
        rw [commutator_comm] at hQW
        exact hQW (commutator_mem_commutator hn w.property)
      have hm := mem_map_of_mem E.toMonoidHom hd
      rw [hE] at hm
      change (E (ambientAction _ W hspan n w / w)).toAdd ∈ plane at hm
      rw [map_div] at hm
      change (E (ambientAction _ W hspan n w)).toAdd - (E w).toAdd ∈ plane at hm
      change (E (ambientAction _ W hspan n (E.symm (.ofAdd v)))).toAdd - v ∈ plane
      simpa only [w,E.apply_symm_apply,toAdd_ofAdd] using hm
  have hne : QN.map a ≠ ⊥ := by
    intro hz
    have hk := (map_eq_bot_iff QN).mp hz
    rw [ha,first_block_kernel V D Y hD hspan E hE,ambientAction_kernel] at hk
    have hQC : Q ≤ centralizer (D : Set G) := fun q hq => hk (show
      (⟨q,hQN hq⟩ : normalizer (D : Set G)) ∈ QN from hq)
    exact hQD (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQC))
  exact independent_blocks plane_GL_card (linearGroup_twoCore_eq_bot) f
    (first_block_surjective V D Y hcD hD hspan E hE hfull) hsecond QN hp hker hne

/-- The actual O₂(H)-action discharges block independence. Only the
quotient action remains for the 14.7.55(6) calculation. -/
theorem source_joint_block_surjective_of_quotient_action [Finite G]
    (H V V₁ V₂ Y L₂ T : Subgroup G) [IsElementaryAbelian 2 V₂]
    (hV₂ : V₂ ≤ V) (hV₁ : V₁ ≤ V₂)
    (hD : Nat.card V₂ = 4) (hZ : Nat.card V₁ = 2)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hLT : L₂ ⊔ T ≤ normalizer (V₂ : Set G))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT))
    (hcomm : ⁅V₂,H.pCoreIn 2⁆ = V₁)
    (hstar : ⁅generatedLineFamily V Y,H.pCoreIn 2⁆ ≤ V₁)
    (hsecond : Function.Surjective ((quotientAction plane).comp
      (spanCoordinateAction V V₂ Y hV₂ hspan E hE))) :
    Function.Surjective ((blockAction plane).comp
      (spanCoordinateAction V V₂ Y hV₂ hspan E hE)) := by
  have hn : H.pCoreIn 2 ≤ normalizer (V₂ : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.le.trans hV₁)
  have hfullN : Function.Surjective (ambientAction (normalizer (V₂ : Set G)) V₂ le_rfl) := by
    intro a
    obtain ⟨l,hl⟩ := hfull a
    exact ⟨inclusion hLT l,hl⟩
  apply joint_block_surjective_of_independent_two_action V V₂ Y (H.pCoreIn 2)
    hD hV₂ hspan E hE hfullN hsecond (isPGroup_pCoreIn 2 H) hn _ (hstar.trans hV₁)
  intro hz
  have hc := congrArg (fun K : Subgroup G => Nat.card K) (hcomm.symm.trans hz)
  rw [hZ,card_bot] at hc
  omega

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions
