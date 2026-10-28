module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowUniqueContaining
public import Theory.SpecificGroups.PSL2.QuadraticSylowComponents
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.PrimeLinearContaining

/-!
# Quadratic odd PSL₂ containing-component exclusion

The full-Sylow Dickson sieve gives unique C-components and solvability of
three-free full-Sylow overgroups in PSL₂(p²). The original containing
components are therefore distinct, and their smaller original quotient
has a cubic divisor. The existing ranked-enlargement contradiction closes
both literal pair applications, preserving the exchanger and half-join.
The final adapter combines prime and quadratic field degrees into the
complete odd PSL₂ row of Theorem C.

Remaining source cases and final assembly stay with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent input of
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its
final discharge.
Source: Aschbacher--Smith A.3.12(8), C.2.7 and 10.2.6, pp.47--48,145--147,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Every quadratic odd PSL₂ containing quotient forces a cubic divisor. -/
theorem ContainingPair.three_dvd_of_quadratic_linear_two_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2) (d : (K ⧸ pCore 2 K) ≃* PSL(2,F)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) :=
  C.three_dvd_of_solvable_three_free_sylow_overgroups hn hs hK hBK d
    (Theory.PSL2.QuadraticSylowComponents.isSolvable_of_three_free hp ho hF)

/-- Exclude the first quadratic odd PSL₂ quotient. -/
theorem ContainingPair.impossible_of_first_quadratic_linear_two_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (d : (K₁ ⧸ pCore 2 K₁) ≃* PSL(2,F)) : False := by
  let : Group.IsNilpotent (pCore 2 K₁) := pCore_isNilpotent
  have ht : (⊤ : Subgroup K₁).IsCComponent := by
    simpa only [subgroupOf_self] using C.first_component.subgroupOf le_rfl
  have htop : (⊤ : Subgroup PSL(2,F)).IsCComponent := by
    have hh := (ht.map_quotient (pCore 2 K₁)).map_equiv d
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      map_top_of_surjective d.toMonoidHom d.surjective] using hh
  have hne := C.distinct_of_first_sylow_unique_quotient d
    (Theory.PSL2.QuadraticSylowComponents.sylow_unique hp ho hF htop)
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
  exact C.three_dvd_of_quadratic_linear_two_quotient hn (one_mem _) hK hLK hp ho hF b

/-- Exclude the second quadratic odd PSL₂ quotient with the original exchanger. -/
theorem ContainingPair.impossible_of_second_quadratic_linear_two_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (d : (K₂ ⧸ pCore 2 K₂) ≃* PSL(2,F)) : False := by
  let : Group.IsNilpotent (pCore 2 K₂) := pCore_isNilpotent
  have ht : (⊤ : Subgroup K₂).IsCComponent := by
    simpa only [subgroupOf_self] using C.second_component.subgroupOf le_rfl
  have htop : (⊤ : Subgroup PSL(2,F)).IsCComponent := by
    have hh := (ht.map_quotient (pCore 2 K₂)).map_equiv d
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      map_top_of_surjective d.toMonoidHom d.surjective] using hh
  have hne := C.distinct_of_second_sylow_unique_quotient d
    (Theory.PSL2.QuadraticSylowComponents.sylow_unique hp ho hF htop)
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K₂.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  exact C.three_dvd_of_quadratic_linear_two_quotient hn C.t_mem hK hLK hp ho hF b

/-- Either literal quadratic odd PSL₂ quotient excludes the containing pair. -/
theorem ContainingPair.impossible_of_quadratic_linear_two_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* PSL(2,F)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* PSL(2,F))) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_quadratic_linear_two_quotient hchoice hmany hn hna hp ho hF e
  · exact C.impossible_of_second_quadratic_linear_two_quotient hchoice hmany hn hna hp ho hF e

/-- The actual quadratic-field Theorem C predicate discharges either containing row. -/
theorem ContainingPair.impossible_of_quadratic_linear_two_model
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) 2 (p ^ 2) ∨
      ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) 2 (p ^ 2)) : False := by
  rcases he with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · exact C.impossible_of_first_quadratic_linear_two_quotient hchoice hmany hn hna hp ho hF e
  · exact C.impossible_of_second_quadratic_linear_two_quotient hchoice hmany hn hna hp ho hF e

/-- Both original odd-field degrees in Theorem C now discharge the pair contradiction. -/
theorem ContainingPair.impossible_of_odd_linear_two_model
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hm : ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) 2 (p ^ e) ∨
      ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) 2 (p ^ e)) : False := by
  rcases he with rfl | rfl
  · exact C.impossible_of_prime_linear_two_model hchoice hmany hn hna hp ho
      (by simpa only [pow_one] using hm)
  · exact C.impossible_of_quadratic_linear_two_model hchoice hmany hn hna hp ho hm

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
