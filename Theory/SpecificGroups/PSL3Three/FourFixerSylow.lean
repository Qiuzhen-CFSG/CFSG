module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer.FullNormalizer
public import Theory.SpecificGroups.PSL3Three.EvenLocals
public import Theory.GroupTheory.NormalSemidihedralSixteenFourNormalizer
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Four-group fixers in specified automorphism Sylow subgroups of PSL₃(3)

The inner intersection of an automorphism Sylow subgroup is SD16. Its two
four-groups give a normalizer of index at most two in that Sylow subgroup,
so the intersection with the order-48 full normalizer has its entire
order-16 Sylow subgroup. The order-eight pointwise fixer is normal in the
full normalizer and therefore lies in that intersection.

This proves the actual PSL₃(3) containment in Aschbacher--Smith 2.5.8(5), p.556.
-/

public section
open Subgroup
namespace Matrix.PSL3Three
open GraphWitnesses.EightCentralizers

private def swapSubgroupOf {A : Type*} [Group A] (B C : Subgroup A) :
    B.subgroupOf C ≃* C.subgroupOf B where
  toFun a := ⟨⟨a.val, a.property⟩, a.val.property⟩
  invFun a := ⟨⟨a.val, a.property⟩, a.val.property⟩
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sylow_semidihedral (S : Sylow 2 PSL) :
    Nonempty (S ≃* Semidihedral.StandardModel 4 (by omega)) := by
  let Q := S.mapSurjective (f := equiv.symm.toMonoidHom) equiv.symm.surjective
  let eS := (S : Subgroup PSL).equivMapOfInjective equiv.symm.toMonoidHom equiv.symm.injective
  obtain ⟨a, b, ha, hb, hab, hgen⟩ := sylowTwo_generators_SL Q
  have hc : Nat.card Q = 16 := by
    rw [Q.card_eq_multiplicity, card_SL]
    decide +kernel
  obtain ⟨e⟩ := Semidihedral.standardModel_equiv_of_presentation
    (by omega : 4 ≤ 4) a b ha hb hab hgen hc
  exact ⟨eS.trans e⟩

/-- Every pointwise four-group fixer belongs to each full automorphism Sylow
subgroup containing the inner image of that four-group. -/
theorem four_fixed_mem_sylow (P : Sylow 2 (MulAut PSL))
    (F : Subgroup PSL) [IsKleinFour F] (hFP : F.map MulAut.conj ≤ P)
    (a : MulAut PSL) (ha : ∀ x ∈ F, a x = x) : a ∈ P := by
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hi : Function.Injective (MulAut.conj : PSL →* MulAut PSL) :=
    MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
  let I := MulAut.innerSubgroup PSL
  let eI : PSL ≃* I := MonoidHom.ofInjective hi
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_subnormal I
    (inferInstance : I.Normal).isSubnormal
  let S := R.mapSurjective (f := eI.symm.toMonoidHom) eI.symm.surjective
  let eR := (R : Subgroup I).equivMapOfInjective eI.symm.toMonoidHom eI.symm.injective
  let D := I.subgroupOf (P : Subgroup (MulAut PSL))
  let eD : D ≃* R := (swapSubgroupOf I (P : Subgroup (MulAut PSL))).trans
    (MulEquiv.subgroupCongr hR.symm)
  obtain ⟨eS⟩ := sylow_semidihedral S
  let J := F.map (MulAut.conj : PSL →* MulAut PSL)
  let E := J.subgroupOf (P : Subgroup (MulAut PSL))
  let eF := (F.equivMapOfInjective MulAut.conj hi).trans (subgroupOfEquivOfLe hFP).symm
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  have hED : E ≤ D := by
    rintro x ⟨f, _, hf⟩
    exact ⟨f, hf⟩
  have hindex := Semidihedral.normalizer_index_dvd_two_of_normal_sixteen
    D E (eD.trans (eR.trans eS)) hED
  let N := normalizer (J : Set (MulAut PSL))
  let B := (P : Subgroup (MulAut PSL)).subgroupOf N
  have hPc : Nat.card P = 32 := by
    rw [P.card_eq_multiplicity, FourGeometry.card_fullAutomorphismGroup]
    decide +kernel
  have hNc : Nat.card N = 48 := card_four_fullNormalizer F inferInstance IsKleinFour.card_four
  have hBc : 16 ≤ Nat.card B := by
    rw [Nat.card_congr (swapSubgroupOf (P : Subgroup (MulAut PSL)) N).toEquiv]
    have hm := (normalizer (E : Set P)).card_mul_index
    have hi2 := Nat.le_of_dvd (by omega : 0 < 2) hindex
    rw [hPc] at hm
    rw [subgroupOf_normalizer_eq hFP]
    nlinarith
  obtain ⟨T, hBT⟩ := P.isPGroup'.comap_subtype.exists_le_sylow (P := B)
  have hTc : Nat.card T = 16 := by
    rw [T.card_eq_multiplicity, hNc]
    decide +kernel
  have hBT_eq : B = (T : Subgroup N) := eq_of_le_of_card_ge hBT (by rw [hTc]; exact hBc)
  have hC : centralizer (J : Set (MulAut PSL)) = fixingSubgroup (MulAut PSL) (F : Set PSL) := by
    ext b
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hb x hx
      change b x = x
      apply hi
      have hh := hb (MulAut.conj x) (mem_map_of_mem MulAut.conj hx)
      have hc : b * MulAut.conj x * b⁻¹ = MulAut.conj (b x) := by ext y; simp
      rw [← hc, mul_inv_eq_iff_eq_mul]
      exact hh.symm
    · intro hb
      change ∀ x ∈ F, b x = x at hb
      rintro _ ⟨x, hx, rfl⟩
      have hc : b * MulAut.conj x * b⁻¹ = MulAut.conj (b x) := by ext y; simp
      rw [hb x hx, mul_inv_eq_iff_eq_mul] at hc
      exact hc.symm
  have hCp : IsPGroup 2 (centralizer (J : Set (MulAut PSL))) :=
    IsPGroup.of_card (n := 3) (by rw [hC]; exact card_four_fixer F inferInstance IsKleinFour.card_four)
  have hac : a ∈ centralizer (J : Set (MulAut PSL)) := by
    rw [hC, mem_fixingSubgroup_iff]
    exact ha
  have han : a ∈ N := centralizer_le_normalizer _ hac
  let : ((centralizer (J : Set (MulAut PSL))).subgroupOf N).Normal := by
    change ((centralizer (J : Set (MulAut PSL))).subgroupOf (normalizer (J : Set (MulAut PSL)))).Normal
    infer_instance
  have hCpN : IsPGroup 2 ((centralizer (J : Set (MulAut PSL))).subgroupOf N) := hCp.comap_subtype
  have ht := hCpN.le_sylow_of_normal T (show
    (⟨a, han⟩ : N) ∈ (centralizer (J : Set (MulAut PSL))).subgroupOf N from hac)
  rw [← hBT_eq] at ht
  exact ht

end Matrix.PSL3Three
