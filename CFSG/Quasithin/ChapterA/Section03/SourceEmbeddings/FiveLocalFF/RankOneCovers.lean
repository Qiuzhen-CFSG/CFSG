module
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.GroupTheory.CComponent.SolvableQuotient
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import GorensteinWalter.PSL2Cardinality

/-!
# Local components in a rank-one core cover

A nonsolvable full-Sylow overgroup of a two-kernel SL₂ cover is the whole
cover. If that cover is perfect, its only C-component is itself. These two
facts identify the smaller local component once geometry places it and the
full Sylow inside the literal parabolic residual. Order comparison then
forces field order four when its two-core quotient is A₅.

Source: the rank-two local rows of Aschbacher–Smith A.3.12 and their use in
10.2.9, printed pp.47–48 and 751–752.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem nonsolvable_cover_eq_top {A : Type*} [Group A] [Finite A]
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 A) (H : Subgroup A)
    (hSH : (S : Subgroup A) ≤ H) (hH : ¬ Group.IsSolvable H) : H = ⊤ := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  have him : H.map f = ⊤ := by
    by_contra hne
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
      (S.mapSurjective hf) (H.map f) (map_mono hSH) hne
    let := isSolvable_comap_of_solvable_ker f (H.map f)
    exact hH (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (le_comap_map f H)) (inclusion_injective _))
  have hh := congrArg (comap f) him
  simpa only [comap_map_eq, comap_top,
    sup_eq_left.mpr ((hk.le_sylow_of_normal S).trans hSH)] using hh

private theorem cComponent_eq_top_of_sl2_core {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] (hF : 2 < Nat.card F)
    (e : (A ⧸ pCore 2 A) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (C : Subgroup A) (hC : C.IsCComponent) : C = ⊤ := by
  let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
  let : Group.IsSolvable (pCore 2 A) := inferInstance
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup_congr.mpr
    (Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF)
  have hm : C.map (QuotientGroup.mk' (pCore 2 A)) = ⊤ := by
    rcases (hC.map_quotient (pCore 2 A)).subnormal.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup (A ⧸ pCore 2 A)) with hb | ht
    · exact ((hC.map_quotient (pCore 2 A)).ne_bot hb).elim
    · exact ht
  have hsup : C ⊔ pCore 2 A = ⊤ := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 A))) hm
  let := hC.perfect
  exact (hC.subnormal.eq_solvableResidual_of_sup_eq_top (pCore 2 A) hsup).trans
    Subgroup.solvableResidual_eq_top

theorem local_eq_of_sl2_core_quotient {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [Group.IsPerfect K] (hF : 2 < Nat.card F)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hBK : B ≤ K) (hSK : (S : Subgroup G) ≤ K) : B = K := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 K := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [he]
    exact pCore_isPGroup
  have hHK : B ⊔ (S : Subgroup G) ≤ K := sup_le hBK hSK
  have hne : ¬ Group.IsSolvable ((B ⊔ (S : Subgroup G)).subgroupOf K) := by
    intro hsol
    let := hsol
    let j : B.subgroupOf (B ⊔ (S : Subgroup G)) →*
        (B ⊔ (S : Subgroup G)).subgroupOf K :=
      { toFun := fun b => ⟨⟨b.val.val, hBK b.property⟩, b.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := j) (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val.val) h))))
  have ht := nonsolvable_cover_eq_top f hf hk (S.subtype hSK)
    ((B ⊔ (S : Subgroup G)).subgroupOf K)
    (fun _ hs => (show (S : Subgroup G) ≤ B ⊔ (S : Subgroup G) from le_sup_right) hs) hne
  have hjoin : B ⊔ (S : Subgroup G) = K := le_antisymm hHK (subgroupOf_eq_top.mp ht)
  have hc : (B.subgroupOf K).IsCComponent := by
    change (B.subgroupOf (B ⊔ (S : Subgroup G))).IsCComponent at hB
    rwa [hjoin] at hB
  exact le_antisymm hBK (subgroupOf_eq_top.mp (cComponent_eq_top_of_sl2_core hF e _ hc))

omit [CharP F 2] in
theorem field_four_of_sl2_five_section {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (a : (A ⧸ pCore 2 A) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Nat.card F = 4 := by
  have hc : Nat.card F * (Nat.card F ^ 2 - 1) = 60 := by
    rw [← GorensteinWalter.sl2_card_formula,
      Nat.card_congr (a.symm.trans e).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hl : Nat.card F ≤ 4 := by
    by_contra! hb
    have hsq : 24 ≤ Nat.card F ^ 2 - 1 := by
      have hh : 25 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have hh := Nat.mul_le_mul (show 5 ≤ Nat.card F by omega) hsq
    omega
  interval_cases h : Nat.card F <;> simp_all
end
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
