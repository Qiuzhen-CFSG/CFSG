module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizers
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.PointwiseSingularPlane

/-!
# The equality layer centralizer in the Sylow group

The elementary eight P ∩ V gives a singular plane in P/Z(P). Its pointwise
stabilizer in the orthogonal group has order at most two. A layer element
outside O₂(H) supplies the nontrivial action, so every element centralizing
V differs from a layer element by the outer-action kernel. The kernel
centralizer formula then yields C_H(V) = V C_H(K), and hence
C_T(V) = V C_H(K) with the literal ambient inclusions.

The quaternion-product input is constructed by the canonical pair theorem
in the equality-branch consumer. No quotient splitting or centralizer
order is assumed. Source: Aschbacher–Smith, 6.2.13, printed p.687.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension

private theorem eight_fixed_quotient
    {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (a b : MulAut Q) (ha : quotientAut (center Q) a ≠ 1)
    (hfixa : ∀ x ∈ E, a x = x) (hfixb : ∀ x ∈ E, b x = x) :
    quotientAut (center Q) b = 1 ∨ quotientAut (center Q) b = quotientAut (center Q) a := by
  let : IsExtraspecial 2 Q := d.extraspecial
  have hz : center Q ≤ E :=
    (IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two d.card E hE).2
  let π := QuotientGroup.mk' (center Q)
  let H := E.map π
  have hindex : H.index = E.index := E.index_map_eq
    (QuotientGroup.mk'_surjective (center Q)) (by rw [QuotientGroup.ker_mk'];exact hz)
  have hEindex : E.index=4 := by
    have hh := E.card_mul_index
    rw [hE,d.card] at hh
    omega
  have hHcard : Nat.card H=4 := by
    have hh := H.card_mul_index
    rw [hindex,hEindex,d.quotient_card] at hh
    omega
  let W : Submodule (ZMod 2) d.SquareSpace := {
    carrier := {v | v.toMul∈H}
    zero_mem' := H.one_mem
    add_mem' := fun hx hy=>H.mul_mem hx hy
    smul_mem' := by
      intro r v hv
      have hb : ∀r:ZMod 2,r=0 ∨ r=1 := by decide
      rcases hb r with rfl|rfl
      · rw [zero_smul];exact H.one_mem
      · simpa only [one_smul] using hv }
  have hcW : Nat.card W=4 := by
    let e : W ≃ H := {
      toFun := fun v=>⟨v.val.toMul,v.property⟩
      invFun := fun v=>⟨Additive.ofMul v.val,v.property⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
    exact (Nat.card_congr e).trans hHcard
  have hdW : Module.finrank (ZMod 2) W=2 := by
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [hcW,Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2≤2) hc.symm
  have hsW : ∀v∈W,d.quadraticForm v=0 := by
    intro v hv
    obtain ⟨x,hx,he⟩ := hv
    have hs : x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hev : v=Additive.ofMul (π x) := congrArg Additive.ofMul he.symm
    rw [hev,d.quadraticForm_apply,d.binarySquare_mk]
    have hsq : (⟨x^2,d.square_mem_center x⟩:center Q)=1 := Subtype.ext hs
    rw [hsq,map_one]
    rfl
  let B := W.map d.squareCoordinates.toLinearMap
  have hdB : Module.finrank (ZMod 2) B=2 := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdW
  have hsB : ∀v∈B,BinaryFourPlus.q v=0 := by
    rintro v ⟨w,hw,rfl⟩
    have he := d.squareFormIsometry.map_app' w
    change BinaryFourPlus.q (d.squareFormIsometry w)=d.quadraticForm w at he
    rw [d.squareFormIsometry_apply] at he
    change BinaryFourPlus.q (d.squareCoordinates w)=0
    exact he.trans (hsW w hw)
  have hfix (c : MulAut Q) (hc : ∀ x ∈ E, c x = x) :
      ∀ v ∈ B, (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction c)).val v = v := by
    rintro v ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hxw⟩ := hw
    change (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction c)).val
      (d.squareCoordinates (Additive.ofMul w.toMul)) = d.squareCoordinates (Additive.ofMul w.toMul)
    rw [← d.squareCoordinates_quotientAut c w.toMul, ← hxw, quotientAut_apply_mk, hc x hx]
  have hane : d.quotientWreathAction a ≠ 1 := by
    intro he
    have hi : a ∈ (MulAut.conj : Q →* MulAut Q).range := by
      change a ∈ MulAut.innerSubgroup Q
      rw [← d.quotientWreathAction_ker]
      exact he
    exact ha ((d.quotientAut_eq_one_iff_inner a).mpr hi)
  rcases BinaryFourPlus.eq_one_or_eq_of_fixed_singular_plane
    (d.quotientWreathAction a) (d.quotientWreathAction b) B (by rw [hdB]) hsB hane
    (hfix a hfixa) (hfix b hfixb) with hb | hb
  · left
    apply (d.quotientAut_eq_one_iff_inner b).mpr
    change b ∈ MulAut.innerSubgroup Q
    rw [← d.quotientWreathAction_ker]
    exact hb
  · right
    ext v
    apply Additive.ofMul.injective
    apply d.squareCoordinates.injective
    rw [d.squareCoordinates_quotientAut, d.squareCoordinates_quotientAut, hb]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The pointwise fixed-plane bound gives the actual layer centralizer in H. -/
theorem LocalAnalysis.equality_layer_centralizer_in_H
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    centralizer ((layer L R).subgroupOf (centralizer ({z} : Set G)) :
      Set (centralizer ({z} : Set G))) =
      (layer L R).subgroupOf (centralizer ({z} : Set G)) ⊔
        centralizer (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let V := (layer L R).subgroupOf H
  let E := P ⊓ V
  let D := centralizer (equalityLayerClosure L R z : Set H)
  let f : H →* MulAut P := MulAut.conjNormal
  have hVH : layer L R ≤ H := layer_le_involution_centralizer h611 hz
  let := h611.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion (show E ≤ V from inf_le_right)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (E.subgroupOf P) := IsElementaryAbelian.subgroupOf inf_le_left
  have hc : Nat.card E = 8 := by
    rw [← card_map_of_injective H.subtype_injective]
    change Nat.card ((P ⊓ V).map H.subtype) = 8
    rw [map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hVH,
      inf_comm, equality_layer_inf_core h611 hz]
    exact A.layer_core_card
  have hnot : ¬ layer L R ≤ H.pCoreIn 2 := by
    intro hh
    have he := A.layer_core_card
    rw [inf_eq_left.mpr hh, hnatural.2.1.card] at he
    norm_num at he
  obtain ⟨v, hv, hvQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let vH : H := ⟨v, hVH hv⟩
  have hvV : vH ∈ V := hv
  have hvC : vH ∈ centralizer (V : Set H) := le_centralizer V hvV
  have hvne : quotientAut (center P) (f vH) ≠ 1 := by
    intro he
    have hvker : vH ∈ (equalityOuterAction L R z).ker := by
      change equalityOuterAction L R z vH = 1
      rwa [equalityOuterAction_apply]
    exact hvQ (mem_map_of_mem H.subtype (A.equalityOuterAction_ker_le h611 hnatural hz hplus hvker))
  have hfix (x : H) (hx : x ∈ centralizer (V : Set H)) :
      ∀ p ∈ E.subgroupOf P, f x p = p := by
    intro p hp
    apply Subtype.ext
    change x * (p : H) * x⁻¹ = (p : H)
    rw [← hx p hp.2, mul_inv_cancel_right]
  have hkerC : (equalityOuterAction L R z).ker ⊓ centralizer (V : Set H) ≤ V ⊔ D := by
    rw [A.equality_outer_kernel_layer_centralizer h611 hnatural hz hplus]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  apply le_antisymm
  · intro x hx
    rcases eight_fixed_quotient hplus.some (E.subgroupOf P)
      ((Nat.card_congr (subgroupOfEquivOfLe (show E ≤ P from inf_le_left)).toEquiv).trans hc)
      (f vH) (f x) hvne (hfix vH hvC) (hfix x hx) with hx0 | hxv
    · apply hkerC
      refine ⟨?_, hx⟩
      change equalityOuterAction L R z x = 1
      rwa [equalityOuterAction_apply]
    · have hdiff : vH⁻¹ * x ∈ (equalityOuterAction L R z).ker := by
        change equalityOuterAction L R z (vH⁻¹ * x) = 1
        rw [map_mul, map_inv, equalityOuterAction_apply, equalityOuterAction_apply]
        change (quotientAut (center P) (f vH))⁻¹ * quotientAut (center P) (f x) = 1
        rw [hxv, inv_mul_cancel]
      have hprod := (V ⊔ D).mul_mem (mem_sup_left hvV)
        (hkerC ⟨hdiff, (centralizer (V : Set H)).mul_mem
          ((centralizer (V : Set H)).inv_mem hvC) hx⟩)
      simpa only [mul_inv_cancel_left] using hprod
  · exact sup_le (le_centralizer V) (centralizer_le le_normalClosure)

/-- The first action premise on p.687, with the literal Sylow and ambient maps. -/
theorem LocalAnalysis.equality_sylow_layer_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    (T : Subgroup G) ⊓ centralizer (layer L R : Set G) =
      layer L R ⊔ equalityCentralizer L R z := by
  let H := centralizer ({z} : Set G)
  have hVH := layer_le_involution_centralizer h611 hz
  have hc := congrArg (fun B : Subgroup H => B.map H.subtype)
    (A.equality_layer_centralizer_in_H h611 hnatural hz hplus)
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVH] at hc
  change _ = layer L R ⊔ equalityCentralizer L R z at hc
  apply le_antisymm
  · intro x hx
    rw [← hc]
    refine ⟨⟨x, hTH hx.1⟩, ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hx.2 v hv)
  · apply sup_le
    · let := h611.layer_elementary
      exact le_inf h611.layer_le_T (le_centralizer _)
    · exact le_inf (A.equality_centralizer_le_sylow hTH)
        ((A.equality_centralizer_le_local_core h611 hnatural hz hTH).trans
          (local_core_centralizes_layer h611))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
