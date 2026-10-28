module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowUniqueContaining
public import Theory.SpecificGroups.BinaryLinear.SylowComponentUnique
public import Theory.SpecificGroups.BinaryLinear.ThreeFreeSylowOvergroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Binary linear containing quotients through dimension five

A three-free full-Sylow overgroup in GL(n,2) is its Sylow subgroup itself.
Thus the original local factor has order divisible by three. For n at most
five, uniqueness of C-components in full-Sylow overgroups also proves the
containing components distinct. The existing ranked-enlargement theorem
then excludes the actual pair, preserving both factors, their exchanger,
relative normality and the literal half-join.

These applications include the previously open PSL(4,2) and PSL(5,2) rows.
No distinctness or cubic-divisor callback is retained. The remaining
containing rows and zero-kernel normalizer stay with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt comes from
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control owns its final
discharge and unconditional assembly.
Source: Aschbacher--Smith A.3.12(4--5) and 10.2.6,
printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private instance (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
    (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective

private theorem binary_linear_three_free (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (BinaryLinear.OuterCyclic.LinearGroup n)) (P : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n))
    (hSP : (S : Subgroup _) ≤ P) (h3 : ¬ 3 ∣ Nat.card P) : IsPGroup 2 P := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [BinaryLinear.ThreeFreeSylowOvergroups.eq_sylow_of_three_free S P hSP h3]
  exact S.isPGroup'

/-- Every positive-dimensional binary projective linear containing quotient forces a cubic divisor. -/
theorem ContainingPair.three_dvd_of_binary_linear_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {n : ℕ} (hnn : 0 < n) (d : (K ⧸ pCore 2 K) ≃* PSL(n,ZMod 2)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) :=
  C.three_dvd_of_solvable_three_free_sylow_overgroups hn hs hK hBK
    (d.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear hnn))
    (fun S P hSP h3 => by
      let := (binary_linear_three_free n hnn S P hSP h3).isNilpotent
      infer_instance)

/-- Exclude the first binary linear quotient in dimensions at most five. -/
theorem ContainingPair.impossible_of_first_binary_linear_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n) (hn5 : n ≤ 5)
    (d : (K₁ ⧸ pCore 2 K₁) ≃* PSL(n,ZMod 2)) : False := by
  have hne := C.distinct_of_first_sylow_unique_quotient
    (d.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear hnn))
    (BinaryLinear.sylow_overgroup_component_unique_le_five n hn5)
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K₁.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  have hLK : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K₁.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.first_le
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  exact C.three_dvd_of_binary_linear_quotient hn (one_mem _) hK hLK hnn b

/-- Exclude the second binary linear quotient with the original exchanger. -/
theorem ContainingPair.impossible_of_second_binary_linear_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n) (hn5 : n ≤ 5)
    (d : (K₂ ⧸ pCore 2 K₂) ≃* PSL(n,ZMod 2)) : False := by
  have hne := C.distinct_of_second_sylow_unique_quotient
    (d.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear hnn))
    (BinaryLinear.sylow_overgroup_component_unique_le_five n hn5)
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K₂.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  exact C.three_dvd_of_binary_linear_quotient hn C.t_mem hK hLK hnn b

/-- Either literal binary linear quotient excludes the containing pair. -/
theorem ContainingPair.impossible_of_binary_linear_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n) (hn5 : n ≤ 5)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* PSL(n,ZMod 2)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* PSL(n,ZMod 2))) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_binary_linear_quotient hchoice hmany hn hna hnn hn5 e
  · exact C.impossible_of_second_binary_linear_quotient hchoice hmany hn hna hnn hn5 e

/-- The literal binary-linear predicate of Theorem C needs no chosen field. -/
theorem ContainingPair.impossible_of_binary_linear_model
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n) (hn5 : n ≤ 5)
    (he : ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) n 2 ∨
      ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) n 2) : False := by
  rcases he with ⟨F,_,_,hF,⟨d⟩⟩ | ⟨F,_,_,hF,⟨d⟩⟩
  all_goals
    let : Fintype F := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq
      (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hF)
  · exact C.impossible_of_first_binary_linear_quotient hchoice hmany hn hna hnn hn5
      (d.trans (Atlas.fieldEquivPSL n a))
  · exact C.impossible_of_second_binary_linear_quotient hchoice hmany hn hna hnn hn5
      (d.trans (Atlas.fieldEquivPSL n a))

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
