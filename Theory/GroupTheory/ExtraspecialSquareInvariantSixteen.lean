module

public import Theory.GroupTheory.ExtraspecialSquareSubgroups
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupAction.Defs

/-!
# Lifting an invariant singular plane to the original extraspecial group

The subgroup is the actual preimage of the supplied singular plane in the
central quotient. Faithfulness on that plane and the exact conjugation kernel
force its ambient centralizer into the original extraspecial group.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.ExtraspecialSquare
variable {G : Type*} [Group G] [Finite G]

theorem exists_invariant_selfcentralizing_sixteen
    (P Y : Subgroup G) [IsExtraspecial 2 P]
    (hPc : Nat.card P = 128) (_hPY : P ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G))
    (e : (form P).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)))
    (f : Y →* Equiv.Perm (Fin 8)) (hker : f.ker = P.subgroupOf Y)
    (hmark : ∀ (y : Y) (v : P ⧸ center P),
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val (e (Additive.ofMul v)) =
        e (Additive.ofMul (quotientAut (center P)
          (P.normalizerMonoidHom (inclusion hYP y)) v)))
    (S : Submodule (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)))
    (hS : Nat.card S = 8)
    (hsing : ∀ v ∈ S, ClassicalOrthogonal.formD 3 (ZMod 2) v = 0)
    (hinv : ∀ (y : Y) v, v ∈ S →
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v ∈ S)
    (hfaith : ∀ y : Y, (∀ v ∈ S,
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v = v) → f y = 1) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ centerIn P ≤ A ∧ A ≤ P ∧
      Nat.card A = 16 ∧ Y ≤ normalizer (A : Set G) ∧
      Y ⊓ centralizer (A : Set G) ≤ A := by
  let U := S.comap e.toLinearEquiv.toLinearMap
  let B : Subgroup P := U.toAddSubgroup.toSubgroup'.comap (QuotientGroup.mk' (center P))
  let A := B.map P.subtype
  have hB (x : P) : x ∈ B ↔ e (Additive.ofMul (QuotientGroup.mk' (center P) x)) ∈ S := Iff.rfl
  have hZB : center P ≤ B := by
    intro x hx
    have hx0 : QuotientGroup.mk' (center P) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hB, hx0]
    change e 0 ∈ S
    simpa only [map_zero] using S.zero_mem
  have himage : (imageSpace P B).map e.toLinearEquiv.toLinearMap = S := by
    apply le_antisymm
    · rintro v ⟨w, ⟨x, hx, he⟩, rfl⟩
      have hw : w = Additive.ofMul (QuotientGroup.mk' (center P) x) :=
        congrArg Additive.ofMul he.symm
      rw [hw]
      exact (hB x).mp hx
    · intro v hv
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) (e.symm v).toMul
      have he : e (Additive.ofMul (QuotientGroup.mk' (center P) x)) = v := by
        rw [hx]
        exact e.apply_symm_apply v
      refine ⟨_, ⟨x, (hB x).mpr (he ▸ hv), rfl⟩, he⟩
  have hcard : Nat.card (imageSpace P B) = 8 := by
    rw [← hS, ← himage]
    exact Nat.card_congr (e.toLinearEquiv.submoduleMap (imageSpace P B)).toEquiv
  have hBc : Nat.card B = 16 := by
    have hh := imageSpace_card P B hZB
    rw [hcard] at hh
    exact hh.symm
  let : IsElementaryAbelian 2 B := elementary_of_imageSpace_singular B (by
    intro v hv
    have hs := hsing (e v) (himage ▸ Submodule.mem_map_of_mem hv)
    exact (e.map_app v).symm.trans hs)
  have hCB : centralizer (B : Set P) = B :=
    extraspecial_two_centralizer_eq_of_card_sq B hZB (by rw [hBc, hPc]; norm_num)
  have hAP : A ≤ P := map_subtype_le B
  have hYA : Y ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    rintro y hy a ⟨x, hx, rfl⟩
    let aut := P.normalizerMonoidHom (inclusion hYP ⟨y, hy⟩)
    refine ⟨aut x, ?_, rfl⟩
    apply (hB _).mpr
    have hh := hinv ⟨y, hy⟩ _ ((hB x).mp hx)
    rw [hmark, quotientAut_apply_mk] at hh
    exact hh
  refine ⟨A, IsElementaryAbelian.map P.subtype, ?_, hAP, ?_, hYA, ?_⟩
  · rw [centerIn_eq_map_center]
    exact map_mono hZB
  · exact (card_map_of_injective P.subtype_injective).trans hBc
  · rintro y ⟨hy, hc⟩
    have hfy : f ⟨y, hy⟩ = 1 := by
      apply hfaith
      intro v hv
      have hm : v ∈ (imageSpace P B).map e.toLinearEquiv.toLinearMap := himage ▸ hv
      obtain ⟨w, ⟨x, hx, he⟩, rfl⟩ := hm
      have hw : w = Additive.ofMul (QuotientGroup.mk' (center P) x) :=
        congrArg Additive.ofMul he.symm
      rw [hw]
      change (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f ⟨y, hy⟩)).val
        (e (Additive.ofMul (QuotientGroup.mk' (center P) x))) =
        e (Additive.ofMul (QuotientGroup.mk' (center P) x))
      rw [hmark, quotientAut_apply_mk]
      have hax : P.normalizerMonoidHom (inclusion hYP ⟨y, hy⟩) x = x := by
        apply Subtype.ext
        change y * (x : G) * y⁻¹ = x
        have hh := hc x (mem_map_of_mem P.subtype hx)
        rw [← hh, mul_inv_cancel_right]
      rw [hax]
    have hyP : y ∈ P := by
      have hm : (⟨y, hy⟩ : Y) ∈ f.ker := hfy
      rw [hker] at hm
      exact hm
    have hyB : (⟨y, hyP⟩ : P) ∈ B := by
      rw [← hCB]
      intro x hx
      apply Subtype.ext
      exact hc x (mem_map_of_mem P.subtype hx)
    exact mem_map_of_mem P.subtype hyB

end Theory.GroupTheory.ExtraspecialSquare
