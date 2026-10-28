module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePointImages
public import Theory.GroupTheory.SylowPreimageNormalizer

/-!
# Augmentation point images with an arbitrary action kernel

The original first action core is a Sylow subgroup of the full preimage
of its point-radical image. Frattini's argument therefore transfers the
point stabilizer's normalization to the Thompson image, even when it
does not normalize the chosen preimage Sylow itself. The finite offender
calculation then gives the trivial, transposition and full-radical images.
In the full case both Thompson and Baumann images are the entire point
radical and the original action is onto S₆.

The full kernel is retained; only its prescribed Sylow intersection is
identified with the ambient two-core. FirstFlagImages applies this to
the literal R₁ in both original quotient rows.
Source: Aschbacher--Smith B.3.4(2)(v), 13.2.1--2, pp.84--85,877--878.
-/

public noncomputable section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterB
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePoint

/-- Frattini lifting transfers image normalizers to the elementary Thompson
image of a Sylow preimage, without requiring its full kernel to be a two-group. -/
theorem thompson_image_normalized_of_sylow_preimage
    {H B : Type*} [Group H] [Finite H] [Group B]
    (R P : Subgroup H) (q : H →* B)
    (hR : IsPGroup 2 R) (S : Sylow 2 q.ker)
    (hS : (S : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker)
    (hRP : R ≤ P) (hkP : q.ker ≤ P)
    (hn : P.map q ≤ normalizer (R.map q : Set B)) :
    P.map q ≤ normalizer ((elementaryAbelianMaxJ R).map q : Set B) := by
  let W := (R.map q).comap q
  have hRW : R ≤ W := le_comap_map q R
  obtain ⟨S0,hS0⟩ := exists_sylow_preimage_of_kernel_intersection R hR q S hS
  have hW : W ≤ P := by
    rw [show W = (R.map q).comap q from rfl,comap_map_eq]
    exact sup_le hRP hkP
  have hPW : P ≤ normalizer (W : Set H) := by
    apply le_normalizer_iff.mpr
    intro p hp w hw
    change q (p * w * p⁻¹) ∈ R.map q
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hn (mem_map_of_mem q hp)) (q w)).mp hw
  have hfr := le_normalizer_sylow_sup W P hW hPW S0
  rw [hS0,map_subgroupOf_eq_of_le hRW] at hfr
  have hN : normalizer (R : Set H) ≤ normalizer (elementaryAbelianMaxJ R : Set H) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp hg
  have hNq := (map_mono (f := q) hN).trans (le_normalizer_map q)
  apply (map_mono hfr).trans
  rw [Subgroup.map_sup]
  refine sup_le hNq ?_
  have hWq : W.map q = R.map q := map_comap_eq_self (map_le_range q R)
  rw [hWq]
  exact (map_mono R.le_normalizer).trans hNq

end CFSG.Quasithin.ChapterB.Offenders.SixCorePoint

namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {H : Type*} [Group H] [Finite H]

private theorem unmap_conjugate (A B : Subgroup S) (a : S)
    (h : A.map (MulAut.conj a⁻¹).toMonoidHom = B) :
    A = B.map (MulAut.conj a).toMonoidHom := by
  rw [←h]
  symm
  rw [map_map]
  have hh : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id S := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hh,map_id]

/-- The point-radical image trichotomy for a Sylow preimage with arbitrary
kernel. The full case also identifies the original action image as S₆. -/
theorem point_baumann_alternative_of_kernel_sylow
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* S) (e : V ≃* Multiplicative W)
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)
    (R : Subgroup H) (hVR : V ≤ R) (hQR : pCore 2 H ≤ R)
    (hRC : R ⊓ centralizer (V : Set H) = pCore 2 H)
    (hRtwo : IsPGroup 2 R)
    (hSyl : ∃ S : Sylow 2 q.ker, (S : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker)
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : V)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd)
    (hRP : R ≤ centralizer ({z.val} : Set H))
    (hRm : R.map q = (BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range).pCoreIn 2) :
    ((baumann R).map q = ⊥ ∨ ∃ r : S, r.IsSwap ∧ (baumann R).map q = zpowers r) ∨
      (Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
        (elementaryAbelianMaxJ R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        (baumann R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        R.map q = pointCore.map (MulAut.conj a.val).toMonoidHom) := by
  let P : Subgroup H := centralizer ({z.val} : Set H)
  obtain ⟨a,ha⟩ := BinaryPermutation.SixCorePoint.exists_point_stabilizer (e z).toAdd hz
  let c := (MulAut.conj a.val⁻¹).toMonoidHom
  let q0 := c.comp q
  let e0 := e.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
    (rho.asGroupHom a.val⁻¹)).toAddEquiv.toMultiplicative
  have he0 (g : H) (v : V) : (e0 (MulAut.conjNormal g v)).toAdd = rho (q0 g) (e0 v).toAdd := by
    change rho a.val⁻¹ (e (MulAut.conjNormal g v)).toAdd =
      rho (a.val⁻¹*q g*(a.val⁻¹)⁻¹) (rho a.val⁻¹ (e v).toAdd)
    rw [he,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel_right]
  have hk0 : q0.ker = q.ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a.val⁻¹).injective
  have hSyl0 : ∃ S : Sylow 2 q0.ker,
      (S : Subgroup q0.ker).map q0.ker.subtype = R ⊓ q0.ker := by
    rw [hk0]
    exact hSyl
  have hb : R.map q ≤ pointCore.map (MulAut.conj a.val).toMonoidHom := by
    rw [hRm]
    apply (BinaryPermutation.SixCorePoint.point_core_le q.range hY (e z).toAdd).trans_eq
    rw [ha,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,H1_core_eq_pointCore]
  have hR0 : R.map q0 ≤ pointCore := by
    rw [show q0 = c.comp q from rfl,←map_map]
    apply (map_mono hb).trans_eq
    change (pointCore.map (MulAut.conj a.val).toMonoidHom).map
      (MulAut.conj a.val⁻¹).toMonoidHom = pointCore
    rw [map_map]
    have hh : (MulAut.conj a.val⁻¹).toMonoidHom.comp (MulAut.conj a.val).toMonoidHom = MonoidHom.id S := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [hh,map_id]
  have hKP : K ≤ P.map q0 := by
    intro k hkK
    have hke : k ∈ alternatingGroup (Fin 6) := (K_le_L1 hkK).2
    have hconj : a.val*k*a.val⁻¹ ∈ q.range := hY
      ((alternatingGroup (Fin 6)).mul_mem ((alternatingGroup (Fin 6)).mul_mem a.property hke)
        ((alternatingGroup (Fin 6)).inv_mem a.property))
    have hpoint : a.val*k*a.val⁻¹ ∈ BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd := by
      rw [ha]
      exact mem_map_of_mem _ (K_le_H1 hkK)
    have hm : a.val*k*a.val⁻¹ ∈ P.map q := by
      rw [point_image V q e he z]
      exact ⟨hpoint,hconj⟩
    obtain ⟨x,hx,hxq⟩ := hm
    refine ⟨x,hx,?_⟩
    change a.val⁻¹*q x*(a.val⁻¹)⁻¹ = k
    rw [hxq]
    simp [mul_assoc]
  have him : R.map q0 = (P.map q0).pCoreIn 2 := by
    rw [show q0 = c.comp q from rfl,←map_map,hRm]
    rw [←point_image V q e he z,map_pCoreIn_of_injective 2 _ c
      (MulAut.conj a.val⁻¹).injective,map_map]
  obtain ⟨S0,hS0⟩ := hSyl0
  have hPn : P.map q0 ≤ normalizer (R.map q0 : Set S) := by
    rw [him]
    exact (P.map q0).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hKP0 : q0.ker ≤ P := by
    rw [hk0,kernel_centralizer V q e he]
    exact centralizer_le (Set.singleton_subset_iff.mpr z.property)
  have hn : K ≤ normalizer ((elementaryAbelianMaxJ R).map q0 : Set S) :=
    hKP.trans (thompson_image_normalized_of_sylow_preimage R P q0 hRtwo S0 hS0 hRP hKP0 hPn)
  have htri : (baumann R).map q0 = ⊥ ∨ (baumann R).map q0 = zpowers swap45 ∨
      ((elementaryAbelianMaxJ R).map q0 = pointCore ∧ (baumann R).map q0 = pointCore) := by
    by_cases hzJ : (elementaryAbelianMaxJ R).map q0 = ⊥
    · left
      have hJ : thompsonJ R 0 ≤ centralizer (V : Set H) := by
        rw [thompsonJ_zero,←kernel_centralizer V q0 e0 he0]
        exact (Subgroup.map_eq_bot_iff _).mp hzJ
      have hb := (lemma_B_2_10_centralizing V R hVR hQR hRC.symm hJ).2.1
      rw [hb]
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [kernel_centralizer V q0 e0 he0]
      exact (show baumann (pCore 2 H) ≤ pCore 2 H from inf_le_left).trans
        (hRC.symm ▸ show R ⊓ centralizer (V : Set H) ≤ centralizer (V : Set H) from inf_le_right)
    by_cases hs : (elementaryAbelianMaxJ R).map q0 ≤ zpowers swap45
    · exact Or.inr (Or.inl (point_baumann_swap V q0 e0 he0 R hVR hR0 hzJ hs))
    · exact Or.inr (Or.inr (point_thompson_full V q0 e0 he0 R hVR hR0 hn hs))
  rcases htri with h0 | hs | hf
  · left;left
    have hh : ((baumann R).map q).map c = ⊥ := by rw [map_map];exact h0
    exact ((baumann R).map q).map_eq_bot_iff_of_injective (MulAut.conj a.val⁻¹).injective |>.mp hh
  · left;right
    have hs' : (baumann R).map q = (zpowers swap45).map (MulAut.conj a.val).toMonoidHom :=
      unmap_conjugate _ _ a.val (by rw [map_map];exact hs)
    refine ⟨(MulAut.conj a.val) swap45,?_,?_⟩
    · change (a.val * Equiv.swap 4 5 * a.val⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,a.val.injective.ne (by decide),rfl⟩
    · rw [MonoidHom.map_zpowers] at hs'
      exact hs'
  · right
    have hJ : (elementaryAbelianMaxJ R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom :=
      unmap_conjugate _ _ a.val (by rw [map_map];exact hf.1)
    have hB : (baumann R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom :=
      unmap_conjugate _ _ a.val (by rw [map_map];exact hf.2)
    have hR : R.map q = pointCore.map (MulAut.conj a.val).toMonoidHom :=
      le_antisymm hb (hB.symm ▸ map_mono inf_le_left)
    refine ⟨?_,a,hJ,hB,hR⟩
    have hd : q.range.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hY
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
    · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
    · have hr := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
      have ht : swap45 ∈ pointCore := by rw [pointCore_eq_closure];exact subset_closure (Or.inl rfl)
      have hs : a.val*swap45*a.val⁻¹ ∈ q.range :=
        (map_le_range q R) (hR.symm ▸ mem_map_of_mem (MulAut.conj a.val).toMonoidHom ht)
      rw [hr,Equiv.Perm.mem_alternatingGroup] at hs
      have hsign : Equiv.Perm.sign swap45 = -1 := by decide
      simp only [map_mul,map_inv,hsign,mul_neg,neg_mul,mul_one,mul_inv_cancel] at hs
      exact ((by decide : (-1 : ℤˣ) ≠ 1) hs).elim
end CFSG.Quasithin.ChapterB.Offenders.SixCorePoint

