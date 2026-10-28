module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePoint
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# Thompson and Baumann images on the augmentation point radical

The actual maximum elementary images are offenders on the five-dimensional
core. Inside a duad radical every such nontrivial image contains its
transposition. Normality under the even point stabilizer then forces a
larger Thompson image to be the entire order-eight radical. The fixed-space
centralizer calculation identifies the small Baumann image as well.

Even conjugation transports this trichotomy to the literal centralizer of
either nonconstant weight. The full case also proves that the original
permutation action is onto S₆; no natural submodule or splitting is assumed.
The Chapter 13 augmentation consumer uses this to isolate the full-image
branch in the selected doubled component. The subsequent Baumann argument
and short-block reconstruction remain distinct obligations.

Source: Aschbacher–Smith B.3.4(2)(v), C.1.37, printed pp.84–85,142–143;
application to 13.2.2(7) and 13.4.10(4), printed pp.878,909.
-/

public noncomputable section
open Subgroup Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
private theorem pointCore_eq_exceptional : pointCore = exceptional 6 (by decide) := by
  rw [pointCore_eq_closure]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl)
    · exact Six.last_le_exceptional (subset_closure rfl)
    · exact Six.plus_le_exceptional (subset_closure (Or.inl rfl))
    · exact Six.klein_le_exceptional (subset_closure (Or.inr rfl))
  · apply (closure_le _).mpr
    rintro x ((rfl | rfl) | ⟨i,hi,rfl⟩)
    · exact subset_closure (Or.inr (Or.inl rfl))
    · exact subset_closure (Or.inr (Or.inr rfl))
    · have hi2 : i = 2 := by apply Fin.ext; have := i.isLt; dsimp at *; omega
      subst i
      exact subset_closure (Or.inl rfl)

variable {H : Type*} [Group H] [Finite H]
variable (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
  (q : H →* S) (e : V ≃* Multiplicative W)
  (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)

private def coordinates : Additive V ≃ₗ[ZMod 2] W := by
  let a : Additive V ≃+ W := {
    toFun := fun v => (e v.toMul).toAdd
    invFun := fun w => Additive.ofMul (e.symm (Multiplicative.ofAdd w))
    left_inv := fun v => e.symm_apply_apply v
    right_inv := fun w => e.apply_symm_apply (Multiplicative.ofAdd w)
    map_add' := fun v w => e.map_mul v.toMul w.toMul }
  exact { a with map_smul' := ZMod.map_smul a }

include he

/-- A nontrivial image of a maximum elementary subgroup is an offender on
 the original augmentation core, even when the image group is only A6. -/
theorem maximum_image_isOffender (R A : Subgroup H) (hVR : V ≤ R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : A.map q ≠ ⊥) :
    IsOffender rho (A.map q) := by
  let q0 := q.rangeRestrict
  have hq0 := q.rangeRestrict_surjective
  have hk0 : q0.ker = centralizer (V : Set H) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_centralizer V q e he
  let r := Representation.NormalElementaryQuotient.representation V q0 hq0 hk0
  have hn0 : A.map q0 ≠ ⊥ := by
    intro hz
    apply hne
    have hm := congrArg (map q.range.subtype) hz
    rw [map_map,Subgroup.map_bot] at hm
    exact hm
  have hb := Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    V q0 hq0 hk0 R A hVR hA hn0
  have heq (a : q.range) (v : Additive V) :
      coordinates V e (r a v) = rho a.val (coordinates V e v) := by
    obtain ⟨a,rfl⟩ := hq0 a
    have hh := Representation.NormalElementaryQuotient.representation_apply V q0 hq0 hk0 a v
    have hv : (r (q0 a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext hh
    change (e _).toAdd = rho (q a) (e v.toMul).toAdd
    rw [hv]
    exact he a v.toMul
  have hh := (hb.isOffender r).map_equivariant r rho q.range.subtype
    q.range.subtype_injective (coordinates V e) heq
  rw [map_map] at hh
  exact hh

private theorem point_maximum_contains_swap (R A : Subgroup H)
    (hVR : V ≤ R) (hRq : R.map q ≤ pointCore)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : A.map q ≠ ⊥) :
    swap45 ∈ A.map q := by
  have hb := maximum_image_isOffender V q e he R A hVR hA hne
  have ha : A.map q ≤ exceptional 6 (by decide) :=
    ((map_mono hA.1).trans hRq).trans_eq pointCore_eq_exceptional
  exact (Six.exceptional_last_mem_iff ha).mpr
    ((Six.caseBFamily_le_exceptional_iff ha).mp ((Six.isOffender_core_iff _).mp hb))

/-- In a canonical point radical, a nonzero Thompson image contains the
actual transposition on the distinguished pair. -/
theorem point_thompson_contains_swap (R : Subgroup H) (hVR : V ≤ R)
    (hRq : R.map q ≤ pointCore)
    (hne : (elementaryAbelianMaxJ R).map q ≠ ⊥) :
    swap45 ∈ (elementaryAbelianMaxJ R).map q := by
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hz
    apply hne
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact sSup_le fun A hA => (Subgroup.map_eq_bot_iff _).mp (hz A hA)
  obtain ⟨A,hA,hn⟩ := hex
  exact map_mono (le_sSup hA) (point_maximum_contains_swap V q e he R A hVR hRq hA hn)

/-- The full image branch of C.1.37 on the augmentation core. The even
point stabilizer suffices for normality, so no S6 surjection is assumed. -/
theorem point_thompson_full (R : Subgroup H) (hVR : V ≤ R)
    (hRq : R.map q ≤ pointCore)
    (hn : K ≤ normalizer ((elementaryAbelianMaxJ R).map q : Set S))
    (hne : ¬ (elementaryAbelianMaxJ R).map q ≤ zpowers swap45) :
    (elementaryAbelianMaxJ R).map q = pointCore ∧ (baumann R).map q = pointCore := by
  have hJ : (elementaryAbelianMaxJ R).map q = pointCore :=
    PointCoreNormal.eq_core _ ((map_mono (sSup_le fun _ hA => hA.1)).trans hRq) hn
      (point_thompson_contains_swap V q e he R hVR hRq
        (fun hz => hne (hz ▸ bot_le))) hne
  refine ⟨hJ,le_antisymm ((map_mono inf_le_left).trans hRq) ?_⟩
  rw [←hJ]
  exact map_mono (elementaryAbelianMaxJ_le_baumann R)

omit he in
private theorem core_last_fixer :
    subspaceKernel rho (fixedSpace rho (zpowers swap45)) pointCore ≤ zpowers swap45 := by
  intro g hg
  have htest (v : W) (hv : rho swap45 v = v) : rho g v = v := by
    apply hg.2
    rw [zpowers_eq_closure]
    apply (mem_fixedSpace_closure_iff rho {swap45} v).mpr
    rintro x rfl
    exact hv
  let v01 : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
  let v02 : W := ⟨![1,0,1,0,0,0],by rw [mem_core];decide⟩
  have h01 := htest v01 (by decide)
  have h02 := htest v02 (by decide)
  have hgE : g ∈ exceptional 6 (by decide) :=
    pointCore_eq_exceptional.le hg.1
  obtain ⟨i,rfl⟩ := (Six.mem_exceptional_iff g).mp hgE
  have hcert : ∀ i : Fin 8, rho (Six.exceptionalWords i) v01 = v01 →
      rho (Six.exceptionalWords i) v02 = v02 →
      Six.exceptionalWords i = 1 ∨ Six.exceptionalWords i = swap45 := by decide
  rcases hcert i h01 h02 with hh | hh
  · rw [hh];exact one_mem _
  · rw [hh];exact mem_zpowers _

omit [Finite H] [IsElementaryAbelian 2 V] in
private theorem core_last_fixer_image (R : Subgroup H) (hRq : R.map q ≤ pointCore) :
    (R ⊓ centralizer
      (V ⊓ centralizer ((zpowers swap45).comap q : Set H) : Set H)).map q ≤ zpowers swap45 := by
  rintro _ ⟨a,ha,rfl⟩
  apply core_last_fixer
  refine ⟨hRq (mem_map_of_mem q ha.1),?_⟩
  intro w hw
  let v : V := e.symm (Multiplicative.ofAdd w)
  have hvcoord : (e v).toAdd = w := e.apply_symm_apply _
  have hv : (v : H) ∈ V ⊓ centralizer ((zpowers swap45).comap q : Set H) := by
    refine ⟨v.property,fun b hb => ?_⟩
    have hfix : rho (q b) w = w := hw ⟨q b,hb⟩
    have heq : MulAut.conjNormal b v = v := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,hvcoord,hfix]
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val heq)
  have hcomm : (v : H) * a = a * (v : H) := ha.2 v hv
  have hfix : MulAut.conjNormal a v = v := by
    apply Subtype.ext
    change a * (v : H) * a⁻¹ = (v : H)
    rw [←hcomm,mul_inv_cancel_right]
  rw [←hvcoord,←he,hfix]

/-- The small nonzero Thompson image gives exactly the same Baumann image
on the five-space, with its literal centralizer. -/
theorem point_baumann_swap (R : Subgroup H) (hVR : V ≤ R)
    (hRq : R.map q ≤ pointCore)
    (hne : (elementaryAbelianMaxJ R).map q ≠ ⊥)
    (hle : (elementaryAbelianMaxJ R).map q ≤ zpowers swap45) :
    (baumann R).map q = zpowers swap45 := by
  apply (thompson_baumann_image_of_unique_maximum_image V R q (zpowers swap45)
    hVR (fun h => hne ((Subgroup.map_eq_bot_iff _).mpr h)) ?_
    (core_last_fixer_image V q e he R hRq)).2
  intro A hA hn
  exact le_antisymm ((map_mono (le_sSup hA)).trans hle)
    (zpowers_le.mpr (point_maximum_contains_swap V q e he R A hVR hRq hA hn))

/-- The complete canonical Baumann-image trichotomy on the augmentation
core. The zero Thompson image makes Baum(R) normal, hence part of O2(H). -/
theorem point_baumann_trichotomy (R : Subgroup H) (hVR : V ≤ R)
    (hQR : pCore 2 H ≤ R) (hk : q.ker = pCore 2 H)
    (hRq : R.map q ≤ pointCore)
    (hn : K ≤ normalizer ((elementaryAbelianMaxJ R).map q : Set S)) :
    (baumann R).map q = ⊥ ∨ (baumann R).map q = zpowers swap45 ∨
      ((elementaryAbelianMaxJ R).map q = pointCore ∧ (baumann R).map q = pointCore) := by
  by_cases hz : (elementaryAbelianMaxJ R).map q = ⊥
  · left
    have hc : pCore 2 H = R ⊓ centralizer (V : Set H) := by
      rw [←kernel_centralizer V q e he,hk,inf_eq_right.mpr hQR]
    have hJ : thompsonJ R 0 ≤ centralizer (V : Set H) := by
      rw [thompsonJ_zero,←kernel_centralizer V q e he]
      exact (Subgroup.map_eq_bot_iff _).mp hz
    have hb := (lemma_B_2_10_centralizing V R hVR hQR hc hJ).2.1
    rw [hb]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (show baumann (pCore 2 H) ≤ pCore 2 H from inf_le_left).trans_eq hk.symm
  by_cases hs : (elementaryAbelianMaxJ R).map q ≤ zpowers swap45
  · exact Or.inr (Or.inl (point_baumann_swap V q e he R hVR hRq hz hs))
  · exact Or.inr (Or.inr (point_thompson_full V q e he R hVR hRq hn hs))
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

/-- The literal augmentation point radical has only the two small Baumann
images or the full point radical. In the full case its Thompson and Baumann
images coincide, and the original permutation action is onto S6. -/
theorem point_baumann_alternative
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* S) (e : V ≃* Multiplicative W)
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)
    (hk : q.ker = pCore 2 H) (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : V)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd) :
    let R := (centralizer ({z.val} : Set H)).pCoreIn 2
    ((baumann R).map q = ⊥ ∨ ∃ r : S, r.IsSwap ∧ (baumann R).map q = zpowers r) ∨
      (Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
        (elementaryAbelianMaxJ R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        (baumann R).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        R.map q = pointCore.map (MulAut.conj a.val).toMonoidHom) := by
  let P : Subgroup H := centralizer ({z.val} : Set H)
  let R := P.pCoreIn 2
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
  have hk0 : q0.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a.val⁻¹).injective]
    exact hk
  have hQP : pCore 2 H ≤ P := by
    rw [←hk,kernel_centralizer V q e he]
    exact centralizer_le (Set.singleton_subset_iff.mpr z.property)
  have hQR : pCore 2 H ≤ R := le_pCoreIn_of_normalizes pCore_isPGroup hQP le_normalizer_of_normal
  have hVR : V ≤ R := (show V ≤ pCore 2 H from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  have hRm : R.map q = (BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range).pCoreIn 2 :=
    pointRadical_image V q e he hk z
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
  have hPN : P ≤ normalizer (elementaryAbelianMaxJ R : Set H) := by
    have hPR : P ≤ normalizer (R : Set H) :=
      P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (hPR hg)
  have hn : K ≤ normalizer ((elementaryAbelianMaxJ R).map q0 : Set S) :=
    hKP.trans ((map_mono hPN).trans (le_normalizer_map q0))
  rcases point_baumann_trichotomy V q0 e0 he0 R hVR hQR hk0 hR0 hn with h0 | hs | hf
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
