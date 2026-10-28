module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.SpecificGroups.SymmetricFive.RadicalRange

/-!
# Components of the actual symmetric-five wreath group

The index-two base is the direct product of two symmetric groups. Perfectness
puts each C-component in that base, where the residual-factor theorem identifies
it with one of the two alternating groups. The coordinate exchange interchanges
the factors, so their normalizers have index two. The base has trivial radical;
consequently the wreath radical is a two-group. An index-two product overgroup
normalizes each C-component, supplying the actual Thompson-image application.

Source: Aschbacher--Smith 15.1.12(3) and 15.2.4, printed pp.1090,1106.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.WreathComponents
abbrev Sym := Equiv.Perm (Fin 5)
abbrev C2 := Multiplicative (ZMod 2)
abbrev W := RegularWreathProduct Sym C2
def swap : C2 := Multiplicative.ofAdd 1
theorem swap_ne_one : swap ≠ 1 := by decide
theorem index_cases (i : C2) : i = 1 ∨ i = swap := by revert i; decide
abbrev base : Subgroup W := RegularWreathProduct.rightHom.ker

noncomputable def baseHom : Sym × Sym →* W where
  toFun p := ⟨fun i => if i = 1 then p.1 else p.2,1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i; simp
    · rfl
  map_mul' p q := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases hi : i = 1 <;> simp [hi,RegularWreathProduct.mul_left]
    · rfl

/-- The base embedding uses the two literal coordinates of the regular wreath product. -/
theorem baseHom_apply (p : Sym × Sym) :
    baseHom p = ⟨fun i => if i = 1 then p.1 else p.2,1⟩ := by rfl

theorem baseHom_injective : Function.Injective baseHom := by
  intro p q h
  apply Prod.ext
  · simpa [baseHom] using congrArg (fun w : W => w.left 1) h
  · simpa [baseHom,swap_ne_one] using congrArg (fun w : W => w.left swap) h

noncomputable def baseEquiv : Sym × Sym ≃* base :=
  MulEquiv.ofBijective (baseHom.codRestrict base (fun _ => rfl))
    ⟨fun p q h => baseHom_injective (congrArg Subtype.val h), by
      rintro ⟨w,hw⟩
      refine ⟨(w.left 1,w.left swap),Subtype.ext ?_⟩
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simp [baseHom]
        · simp [baseHom,swap_ne_one]
      · exact hw.symm⟩

theorem base_index : base.index = 2 := by
  rw [index_ker, MonoidHom.range_eq_top.mpr (fun x =>
    ⟨RegularWreathProduct.inl x,rfl⟩),card_top]
  simp [C2,Nat.card_eq_fintype_card]

theorem symmetric_residual : solvableResidual Sym = alternatingGroup (Fin 5) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply le_antisymm
  · have h := solvableResidual_le_derivedSeries (G := Sym) 1
    rw [derivedSeries_one] at h
    exact h.trans_eq (alternatingGroup.commutator_perm_eq (by simp))
  · exact le_solvableResidual_of_isPerfect _

theorem symmetric_residual_quasisimple : IsQuasisimple (solvableResidual Sym) := by
  rw [symmetric_residual]
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩

theorem product_component {K : Subgroup (Sym × Sym)} (hK : K.IsCComponent) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) ∧ K.Normal := by
  rcases cComponent_eq_residual_factor (Or.inr symmetric_residual_quasisimple)
    (Or.inr symmetric_residual_quasisimple) hK with rfl | rfl
  · exact ⟨⟨residualLeftEquiv.trans (MulEquiv.subgroupCongr symmetric_residual)⟩,inferInstance⟩
  · exact ⟨⟨residualRightEquiv.trans (MulEquiv.subgroupCongr symmetric_residual)⟩,inferInstance⟩

theorem component_le_base {K : Subgroup W} (hK : K.IsCComponent) : K ≤ base := by
  let := hK.perfect
  exact le_of_isPerfect_of_index_eq_two K base base_index

theorem component_base_normal {K : Subgroup W} (hK : K.IsCComponent) :
    (K.subgroupOf base).Normal := by
  let e := baseEquiv.symm
  have h := product_component ((hK.subgroupOf (component_le_base hK)).map_equiv e)
  let := h.2
  have hn : (((K.subgroupOf base).map e.toMonoidHom).comap e.toMonoidHom).Normal :=
    inferInstance
  rw [comap_map_eq_self_of_injective e.injective] at hn
  exact hn

theorem component_equiv {K : Subgroup W} (hK : K.IsCComponent) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  let L := K.subgroupOf base
  obtain ⟨e⟩ := (product_component ((hK.subgroupOf (component_le_base hK)).map_equiv
    baseEquiv.symm)).1
  exact ⟨(subgroupOfEquivOfLe (component_le_base hK)).symm.trans
    ((baseEquiv.symm.subgroupMap L).trans e)⟩

theorem base_le_component_normalizer {K : Subgroup W} (hK : K.IsCComponent) :
    base ≤ normalizer (K : Set W) := by
  let := component_base_normal hK
  exact (normal_subgroupOf_iff_le_normalizer (component_le_base hK)).mp inferInstance

theorem swap_conjugate (p : Sym × Sym) :
    RegularWreathProduct.inl swap * baseHom p * (RegularWreathProduct.inl swap)⁻¹ =
      baseHom (p.2,p.1) := by
  have hs : swap⁻¹ = swap := by decide
  have hss : swap * swap = 1 := by decide
  apply RegularWreathProduct.ext
  · funext i
    rcases index_cases i with rfl | rfl <;>
      simp [baseHom,RegularWreathProduct.mul_left,hs,hss,swap_ne_one]
  · simp [baseHom]

theorem component_eq_factor {K : Subgroup W} (hK : K.IsCComponent) :
    K = ((solvableResidual Sym).prod (⊥ : Subgroup Sym)).map baseHom ∨
      K = ((⊥ : Subgroup Sym).prod (solvableResidual Sym)).map baseHom := by
  let e := baseEquiv.symm
  have he : (((K.subgroupOf base).map e.toMonoidHom).map baseHom) = K := by
    rw [map_map]
    have hi : baseHom.comp e.toMonoidHom = base.subtype := by
      apply MonoidHom.ext
      intro x
      exact congrArg Subtype.val (baseEquiv.apply_symm_apply x)
    rw [hi,map_subgroupOf_eq_of_le (component_le_base hK)]
  rcases cComponent_eq_residual_factor (Or.inr symmetric_residual_quasisimple)
    (Or.inr symmetric_residual_quasisimple)
    ((hK.subgroupOf (component_le_base hK)).map_equiv e) with h | h
  · exact Or.inl (he.symm.trans (congrArg (map baseHom) h))
  · exact Or.inr (he.symm.trans (congrArg (map baseHom) h))

theorem component_not_normal {K : Subgroup W} (hK : K.IsCComponent) : ¬ K.Normal := by
  intro hn
  let : Nontrivial (solvableResidual Sym) := by
    rw [symmetric_residual]
    infer_instance
  obtain ⟨a,ha⟩ := exists_ne (1 : solvableResidual Sym)
  have hane : (a : Sym) ≠ 1 := fun h => ha (Subtype.ext h)
  rcases component_eq_factor hK with hk | hk
  · have hm : baseHom (a,1) ∈ K := hk ▸ mem_map_of_mem baseHom ⟨a.property,rfl⟩
    have hc := hn.conj_mem _ hm (RegularWreathProduct.inl swap)
    rw [swap_conjugate,hk] at hc
    obtain ⟨x,hx,hxe⟩ := hc
    have he := congrArg Prod.snd (baseHom_injective hxe)
    exact hane (he.symm.trans hx.2)
  · have hm : baseHom (1,a) ∈ K := hk ▸ mem_map_of_mem baseHom ⟨rfl,a.property⟩
    have hc := hn.conj_mem _ hm (RegularWreathProduct.inl swap)
    rw [swap_conjugate,hk] at hc
    obtain ⟨x,hx,hxe⟩ := hc
    have he := congrArg Prod.fst (baseHom_injective hxe)
    exact hane (he.symm.trans hx.1)

theorem component_normalizer_index {K : Subgroup W} (hK : K.IsCComponent) :
    (normalizer (K : Set W)).index = 2 := by
  have hd := index_dvd_of_le (base_le_component_normalizer hK)
  rw [base_index] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · exact (component_not_normal hK (normalizer_eq_top_iff.mp (index_eq_one.mp h))).elim
  · exact h

theorem base_radical_eq_bot : solvableRadical base = ⊥ := by
  let f := (MonoidHom.fst Sym Sym).comp baseEquiv.symm.toMonoidHom
  let g := (MonoidHom.snd Sym Sym).comp baseEquiv.symm.toMonoidHom
  have hf : Function.Surjective f := Prod.fst_surjective.comp baseEquiv.symm.surjective
  have hg : Function.Surjective g := Prod.snd_surjective.comp baseEquiv.symm.surjective
  have hrf := FivePointSylowParabolic.solvable_normal_le_ker f
    (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top) (solvableRadical base)
  have hrg := FivePointSylowParabolic.solvable_normal_le_ker g
    (by rw [MonoidHom.range_eq_top.mpr hg]; exact le_top) (solvableRadical base)
  apply bot_unique
  intro x hx
  apply baseEquiv.symm.injective
  apply Prod.ext
  · rw [map_one]
    exact hrf hx
  · rw [map_one]
    exact hrg hx

theorem radical_isTwoGroup : IsPGroup 2 (solvableRadical W) := by
  let R := solvableRadical W
  let f : R →* C2 := RegularWreathProduct.rightHom.comp R.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxb : (x : W) ∈ base := hx
    have hxr : (⟨x,hxb⟩ : base) ∈ solvableRadical base := by
      rw [← radical_subgroupOf_normal base]
      exact x.property
    have he : (⟨x,hxb⟩ : base) = 1 := base_radical_eq_bot.le hxr
    exact Subtype.ext (congrArg (fun z : base => (z : W)) he)
  have hp : IsPGroup 2 C2 := IsPGroup.of_card (n := 1) (by
    simp [C2,Nat.card_eq_fintype_card])
  exact hp.of_injective f hf

theorem radical_eq_bot_of_twoCore (hc : pCore 2 W = ⊥) : solvableRadical W = ⊥ := by
  exact bot_unique ((le_sSup ⟨inferInstance,radical_isTwoGroup⟩ :
    solvableRadical W ≤ pCore 2 W).trans hc.le)

theorem not_solvable : ¬ Group.IsSolvable W := by
  intro hs
  let := hs
  let A := alternatingGroup (Fin 5)
  let j : A →* W := baseHom.comp (A.subtype.prod (1 : A →* Sym))
  have hj : Function.Injective j := by
    intro x y h
    have he := congrArg Prod.fst (baseHom_injective h)
    exact Subtype.ext he
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable A
    (Group.isSolvable_of_isSolvable_injective hj)

theorem product_overgroup_normalizes {D : Type*} [Group D] [Finite D]
    (L : Subgroup D) (e : L ≃* Sym × Sym) (hi : L.index = 2)
    {K : Subgroup D} (hK : K.IsCComponent) : L ≤ normalizer (K : Set D) := by
  let := hK.perfect
  have hKL := le_of_isPerfect_of_index_eq_two K L hi
  have hc := (product_component ((hK.subgroupOf hKL).map_equiv e)).2
  let := hc
  have hn : (((K.subgroupOf L).map e.toMonoidHom).comap e.toMonoidHom).Normal :=
    inferInstance
  rw [comap_map_eq_self_of_injective e.injective] at hn
  exact (normal_subgroupOf_iff_le_normalizer hKL).mp hn

end Theory.SpecificGroups.SymmetricFive.WreathComponents
