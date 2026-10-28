module
public import Glauberman.PushingUpSL2DegreeTwoStep

/-!
# Both natural sections on the reduced Niles diagram

At diagram parameter two, the full core center modulo the ambient center
and the whole core modulo its center are natural modules for the same
original SL₂ marking. The interval indices give the sharp fixed halves.
Perfectness rules out central action on the first factor; the shortest
noncentral gap rules it out on the second. Their exact kernels are O₂.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5 and
Theorem 6.9, pp.51--52,58. Neither a central complement nor a changed field
is used. The actual class-three exclusion consumes these two coordinates
in `Glauberman.PushingUpSL2DegreeBinary`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport Representation
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance twoStepFactorsAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Both natural factors on the literal reduced diagram, with the full
ambient center as lower denominator. -/
theorem sl2_two_step_natural_factors
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) (g : G)
    (hgen : (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (hinter : (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G)
    (hd : NilesTwoStepFullDiagram (Nat.card F) (S : Subgroup G)
      ((S : Subgroup G).map (MulAut.conj g).toMonoidHom)
      (twistedConjugacy (S : Subgroup G) α g))
    (hnc : ¬ ⁅(S : Subgroup G).map (MulAut.conj g).toMonoidHom,
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom⁆ ≤
        centerIn ((S : Subgroup G).map (MulAut.conj g).toMonoidHom)) :
    let ρ := ((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp
      (e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 G)).comp (⊤ : Subgroup G).subtype))
    Nonempty (BinaryConjugationSection ⊤ (centerIn (pCore 2 G)) (center G) ρ) ∧
      Nonempty (BinaryConjugationSection ⊤ (pCore 2 G) (centerIn (pCore 2 G)) ρ) := by
  have hd' := hd
  obtain ⟨hnum,hj,hshort,hindex,hzs,hzt,hzq,hzg,htwice⟩ := hd
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ 6
  let V := centerIn (pCore 2 G)
  let Z := center G
  change centerIn (S : Subgroup G) = X 2 3 at hzs
  change centerIn (T : Subgroup G) = X 3 4 at hzt
  change V = X 2 4 at hzq
  change Z = X 3 3 at hzg
  have hQ : X 1 5 = pCore 2 G := by
    change intervalCell φ 1 1 = _
    rw [intervalCell_intersection,hinter]
  have hVn : V.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
    (normalizes_centerIn (show (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G) from
      le_normalizer_of_normal)))
  let _ := hVn
  have hVQ : V ≤ pCore 2 G := inf_le_left
  have hZV : Z ≤ V := by rw [hzg,hzq]; exact intervalDiagram_mono φ (by decide) (by decide)
  have hVe : IsElementaryAbelian 2 V := by rw [hzq]; exact hshort 2 4 (by decide) (by decide)
  let _ := hVe
  have hVmap : IsElementaryAbelian 2 (V.map (QuotientGroup.mk' Z)) := IsElementaryAbelian.map _
  let _ := hVmap
  have hQS : (pCore 2 G).relIndex (S : Subgroup G) = Nat.card F := by
    rw [←hinter]
    exact hnum.index_left
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hperfect : ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ ⊔ pCore 2 G = ⊤ := by
    have he := CentralExtension.ker_sup_commutator_eq_top_of_surjective f hf
    change _root_.commutator G ⊔ pCore 2 G = ⊤
    simpa only [hk,sup_comm] using he
  have hVcentral : ⁅pCore 2 G,V⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hntV : ¬ ⁅(⊤ : Subgroup G),V⁆ ≤ Z := by
    intro hh
    have hder := derived_centralizes_of_central_action_commutators V
      ((commutator_comm V ⊤).trans_le hh)
    have hVC : V ≤ center G := by
      apply centralizer_eq_top_iff_subset.mp
      apply top_unique
      rw [←hperfect]
      exact sup_le (le_centralizer_iff.mp hder) (le_centralizer_iff.mpr inf_le_right)
    have hidx : (center G).relIndex V = Nat.card F ^ 2 :=
      (original_sl2_full_center_covering e hn hF S α hfit hno).2.1
    rw [relIndex_eq_one.mpr hVC] at hidx
    have := one_lt_pow₀ (by omega : 1 < Nat.card F) (by decide : (2:ℕ) ≠ 0)
    omega
  have hkernelV := sl2_normal_section_kernel e hlarge V Z
    (hVcentral.le.trans bot_le) hntV
  have hidxV : Z.relIndex V = Nat.card F ^ 2 :=
    (original_sl2_full_center_covering e hn hF S α hfit hno).2.1
  have hhalfS : (X 2 3).relIndex V = Nat.card F := by
    rw [hzq]
    change (intervalCell φ 2 3).relIndex (intervalCell φ 2 2) = _
    rw [intervalCell_relIndex φ 2 2 2 3 le_rfl (by decide) (by decide)]
    exact hindex 4 (by decide) (by decide)
  have hhalfT : (X 3 4).relIndex V = Nat.card F := by
    rw [hzq]
    change (intervalCell φ 3 2).relIndex (intervalCell φ 2 2) = _
    rw [intervalCell_relIndex φ 2 2 3 2 (by decide) le_rfl (by decide)]
    exact hindex 4 (by decide) (by decide)
  have hSV : ⁅(S : Subgroup G),X 2 3⁆ ≤ Z := by
    rw [←hzs,commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  have hTV : ⁅(T : Subgroup G),X 3 4⁆ ≤ Z := by
    rw [←hzt,commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  have hcV := Representation.SL2.natural_section_of_fixed_halves e hn hF S T hgen hQS
    V Z (X 2 3) (X 3 4) hZV hkernelV hidxV
    (hzq ▸ intervalDiagram_mono φ le_rfl (by decide))
    (hzq ▸ intervalDiagram_mono φ (by decide) le_rfl) hSV hTV hhalfS hhalfT
  obtain ⟨k,hk5,hk6,hex,hgap⟩ := intervalDiagram_minimal_noncentral_gap φ 2 (by decide)
    hj hshort hzt htwice hnc
  have hk5' : k=5 := by omega
  subst k
  have hVn' : (X 2 4).Normal := hzq ▸ hVn
  have hinterT : (S : Subgroup G) ⊓ (T : Subgroup G) = pCore 2 G := hinter
  have hQQ := (two_step_core_sections φ hd' hinter).1
  have hntQ := intervalDiagram_gap_action_nontrivial φ 2 5 (by decide) (by decide)
    (hinter.symm ▸ hperfect) hzt hex hVn'
    (by change ⁅(⊤ : Subgroup G),X 2 4⁆ ≤ X 2 4
        rw [←hzq]
        exact commutator_le_right _ _)
    (by change ⁅(S : Subgroup G) ⊓ (T : Subgroup G),X 1 5⁆ ≤ X 2 4
        rw [hinterT,hQ,←hzq]
        exact hQQ.trans hZV)
  have hntQ' : ¬ ⁅(⊤ : Subgroup G),pCore 2 G⁆ ≤ V := by
    change ¬ ⁅(⊤ : Subgroup G),X 1 5⁆ ≤ X 2 4 at hntQ
    rwa [hQ,←hzq] at hntQ
  have hkernelQ := sl2_normal_section_kernel e hlarge (pCore 2 G) V (hQQ.trans hZV) hntQ'
  have hQe : IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' V)) := by
    rw [←hQ]
    apply intervalDiagram_elementary_image φ 2 (by decide) hj hshort (by decide : 1 ≤ 5) (by decide)
    rw [QuotientGroup.ker_mk']
    change ⁅X 1 5,X 1 5⁆ ≤ V
    rw [hQ]
    exact hQQ.trans hZV
  let _ := hQe
  have hidxQ : V.relIndex (pCore 2 G) = Nat.card F ^ 2 := by
    rw [hzq,←hQ]
    exact intervalDiagram_gap_layer_index φ 2 5 (Nat.card F) (by decide) (by decide)
      (by decide) (fun i hi hi' => hindex i hi (by omega))
  obtain ⟨_,hAM,_,hBM,hSA,hTB,hiA,hiB⟩ := intervalDiagram_gap_fixed_halves φ 2 5
    (Nat.card F) (by decide) (by decide) (by decide) hj hzs hzt hgap
      (fun i hi hi' => hindex i hi (by omega))
  change X 1 4 ≤ X 1 5 at hAM
  change X 2 5 ≤ X 1 5 at hBM
  change ⁅(S : Subgroup G),X 1 4⁆ ≤ X 2 4 at hSA
  change ⁅(T : Subgroup G),X 2 5⁆ ≤ X 2 4 at hTB
  change (X 1 4).relIndex (X 1 5) = Nat.card F at hiA
  change (X 2 5).relIndex (X 1 5) = Nat.card F at hiB
  rw [hQ] at hAM hBM hiA hiB
  rw [←hzq] at hSA hTB
  have hcQ := Representation.SL2.natural_section_of_fixed_halves e hn hF S T hgen hQS
    (pCore 2 G) V (X 1 4) (X 2 5) hVQ hkernelQ hidxQ hAM hBM hSA hTB hiA hiB
  exact ⟨hcV,hcQ⟩

end Glauberman
