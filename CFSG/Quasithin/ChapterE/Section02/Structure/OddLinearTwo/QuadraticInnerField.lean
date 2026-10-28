module

public import Theory.GroupTheory.InnerInvolutionExtension
public import Theory.SpecificGroups.PSL2.OddSquareFieldFixedIndex
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticMaxSolvability
/-!
# Excluding inner-field automizers in the quadratic odd PSL₂ row

Assume every ambient action on the normal PSL₂(p²) component is inner times
a coefficient automorphism. The fixed PGL₂(p) subgroup has odd index, is
proper and is nonsolvable. On the other hand the actual maximal overgroup is
solvable because its intersection with the component is an involution
centralizer. Conjugating its Sylow subgroup into the unique maximal gives the
contradiction. The proof retains the literal conjugation map and fixed
subgroup, with no model conclusion assumed.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
/-- Some actual ambient action is not inner-field. -/
theorem quadratic_linear_not_inner_field
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F) :
    ∃ a : H, ¬ ∃ g : PSL2 F, ∃ σ : F ≃+* F,
      MulAut.congr eK (MulAut.conjNormal a) = MulAut.conj g * psl2FieldAut F σ := by
  classical
  let q : H →* MulAut (PSL2 F) :=
    (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut K)
  have hqK : ∀ k : K, q (k : H) = MulAut.conj (eK k) := by
    intro k
    change MulAut.congr eK (MulAut.conjNormal (k : H)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hcent : eK k ∈ center (PSL2 F) := (centerCongr eK ⟨k, hk⟩).property
    rw [psl2_center_eq_bot F, mem_bot] at hcent
    exact mem_bot.mpr (eK.injective (by simpa only [map_one] using hcent))
  have hfaith := MulAut.conjNormal_injective_of_centralizer_eq_bot K
    (centralizer_eq_bot_of_centerless_sylow_supplement T K hgen hZ hO)
  have hq : Function.Injective q := (MulAut.congr eK).injective.comp hfaith
  have hsolv := quadratic_linear_source_max_isSolvable T hP K hgen ho hF hp eK
  let : Finite (F ≃+* F) := Finite.of_injective (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hfcard : Nat.card (F ≃+* F) = 2 := FiniteField.card_ringAut_of_card_prime_pow Fact.out hF
  obtain ⟨σ₀, hσ₀⟩ := exists_prime_orderOf_dvd_card' (G := F ≃+* F) 2 (by rw [hfcard])
  let P₀ := (psl2FieldAut F σ₀).fixedSubgroup
  have hP₀ := Theory.PSL2.OddSquareFieldFixed.coefficient_fixed_odd_index_nonsolvable ho hp hF σ₀ hσ₀
  by_contra! hcover
  change ∀ h : H, ∃ g : PSL2 F, ∃ σ : F ≃+* F, q h = MulAut.conj g * psl2FieldAut F σ at hcover
  by_cases hK : K = ⊤
  · let eH : H ≃* PSL2 F :=
      (topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm)).trans eK
    let N := P₀.map eH.symm.toMonoidHom
    have hNne : N ≠ ⊤ := by
      intro hh
      apply hP₀.2.1
      exact (map_injective eH.symm.injective)
        (hh.trans (map_top_of_surjective eH.symm.toMonoidHom eH.symm.surjective).symm)
    have hNodd : Odd N.index := by
      rw [index_map_of_bijective eH.symm.bijective]
      exact hP₀.1
    let := proper_odd_index_isSolvable_of_max_isSolvable T hP hsolv N hNne hNodd
    exact hP₀.2.2 (Group.isSolvable_of_isSolvable_injective
      (f := (P₀.equivMapOfInjective eH.symm.toMonoidHom eH.symm.injective).toMonoidHom)
      (P₀.equivMapOfInjective eH.symm.toMonoidHom eH.symm.injective).injective)
  · obtain ⟨a, ha, _, hi, σ, hσ, hqa⟩ :=
      exists_outer_involution_of_inner_times_two_action K eK q hq hqK
        (psl2FieldAut F) hfcard hcover hK
    let C := centralizer ({a} : Set H)
    let D := C.subgroupOf K
    let P := (psl2FieldAut F σ).fixedSubgroup
    have hfixed := Theory.PSL2.OddSquareFieldFixed.coefficient_fixed_odd_index_nonsolvable ho hp hF σ hσ
    have hDP : D.map eK.toMonoidHom = P := by
      ext x
      rw [mem_map_equiv, MulAut.mem_fixedSubgroup]
      change (eK.symm x : H) ∈ C ↔ psl2FieldAut F σ x = x
      rw [← hqa]
      change (eK.symm x : H) ∈ C ↔
        eK (MulAut.conjNormal a (eK.symm x)) = x
      rw [← eK.apply_symm_apply x, eK.injective.eq_iff]
      rw [mem_centralizer_singleton_iff, Subtype.ext_iff]
      simp only [eK.symm_apply_apply, MulAut.conjNormal_apply]
      constructor
      · intro h
        rw [← h]; group
      · intro h
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have hCodd : Odd C.index := by
      rw [centralizer_index_eq_restriction_of_index_two K hi a ha]
      have hh := index_map_of_bijective (H := D) (f := eK.toMonoidHom) eK.bijective
      rw [hDP] at hh
      exact hh ▸ hfixed.1
    have hCne : C ≠ ⊤ := by
      intro hh
      have hDtop : D = ⊤ := by change C.subgroupOf K = ⊤; rw [hh, top_subgroupOf]
      have he : P = ⊤ := by rw [← hDP, hDtop, map_top_of_surjective eK.toMonoidHom eK.surjective]
      exact hfixed.2.1 he
    let := proper_odd_index_isSolvable_of_max_isSolvable T hP hsolv C hCne hCodd
    let f : D →* C := {
      toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : H)) hh))
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective hf
    let e := (D.equivMapOfInjective eK.toMonoidHom eK.injective).trans (MulEquiv.subgroupCongr hDP)
    exact hfixed.2.2 (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
end CFSG.Quasithin.ChapterE.Structure

namespace CFSG.Quasithin.ChapterE.Structure
/-- The source Sylow automizer contains an actual non-inner-field action. -/
theorem quadratic_linear_source_sylow_not_inner_field
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F) :
    ∃ a ∈ (T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K),
      ¬ ∃ g : PSL2 F, ∃ σ : F ≃+* F,
        MulAut.congr eK a = MulAut.conj g * psl2FieldAut F σ := by
  obtain ⟨a, ha⟩ := quadratic_linear_not_inner_field T hP K hgen hO ho hF hp eK
  have haKT : a ∈ K ⊔ (T : Subgroup H) := hgen ▸ mem_top _
  obtain ⟨k, hk, t, ht, hkt⟩ := (mem_sup_of_normal_left).mp haKT
  refine ⟨MulAut.conjNormal t, mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
  rintro ⟨g, σ, he⟩
  apply ha
  refine ⟨eK ⟨k, hk⟩ * g, σ, ?_⟩
  rw [← hkt, map_mul, map_mul]
  have hkq : MulAut.congr eK (MulAut.conjNormal k) = MulAut.conj (eK ⟨k, hk⟩) := by
    change MulAut.congr eK (MulAut.conjNormal ((⟨k, hk⟩ : K) : H)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  rw [hkq, he, map_mul, mul_assoc]
end CFSG.Quasithin.ChapterE.Structure

namespace CFSG.Quasithin.ChapterE.Structure
/-- The same witness uses the literal entrywise SL₂ quotient formula. -/
theorem quadratic_linear_source_matrix_not_inner_field
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F) :
    ∃ a ∈ (T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K),
      ¬ ∃ g : PSL2 F, ∃ σ : F ≃+* F,
        ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
          MulAut.congr eK a (QuotientGroup.mk' _ x) =
            g * QuotientGroup.mk' _ (Matrix.SpecialLinearGroup.map σ.toRingHom x) * g⁻¹ := by
  obtain ⟨a, ha, hnot⟩ := quadratic_linear_source_sylow_not_inner_field T hP K hgen hO ho hF hp eK
  refine ⟨a, ha, ?_⟩
  rintro ⟨g, σ, he⟩
  apply hnot
  refine ⟨g, σ, ?_⟩
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center (Matrix.SpecialLinearGroup (Fin 2) F)) z
  simpa only [MulAut.mul_apply, MulAut.conj_apply, psl2FieldAut_apply, psl2RingEquiv_mk] using he x
end CFSG.Quasithin.ChapterE.Structure
