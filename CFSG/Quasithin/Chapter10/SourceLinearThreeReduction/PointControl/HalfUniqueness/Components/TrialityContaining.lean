module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowUniqueContaining
public import Theory.SpecificGroups.Triality.ThreeFreeSylowOvergroups

/-!
# The binary triality containing-component row

Three-free full-Sylow overgroups of the actual binary triality carrier are
solvable. Passing the original local component through the containing
component's two-core quotient therefore forces a cubic divisor in its own
intrinsic quotient. Independently, full-Sylow component uniqueness shows
that the two normal containing components are distinct. The proved ranked-
enlargement contradiction excludes the actual pair.

Both first- and second-component applications retain the original exchanger,
relative normality, full Sylow and literal half-join. The final adapter uses
the exact IsTrialityGroupAt predicate of the Theorem C catalogue. No
component-distinctness, cubic-divisor or model-recognition callback remains
in this row.

The remaining containing rows, the three-free enlargement, the zero-kernel
binary-three normalizer and final assembly belong to
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent source
input from qt-d-10-nona5-point-selection, with its final discharge retained
by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Every binary triality containing quotient forces a cubic divisor. -/
theorem ContainingPair.three_dvd_of_triality_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {n : ℕ} (hnn : 0 < n) (d : (K ⧸ pCore 2 K) ≃* Triality.Standard.BinaryCarrier n hnn) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) :=
  C.three_dvd_of_solvable_three_free_sylow_overgroups hn hs hK hBK d
    (Triality.Standard.ThreeFreeSylowOvergroups.isSolvable_of_three_free n hnn)

/-- Exclude the first binary triality quotient. -/
theorem ContainingPair.impossible_of_first_triality_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n)
    (d : (K₁ ⧸ pCore 2 K₁) ≃* Triality.Standard.BinaryCarrier n hnn) : False := by
  let := C.first_component.perfect
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hnn) :=
    Group.IsPerfect.ofSurjective
      (f := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K₁)))
      (d.surjective.comp (QuotientGroup.mk'_surjective _))
  have hne := C.distinct_of_first_sylow_unique_quotient d
    (Triality.Standard.binary_sylow_overgroup_component_unique n hnn)
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
  exact C.three_dvd_of_triality_quotient hn (one_mem _) hK hLK hnn b

/-- Exclude the second binary triality quotient with the original exchanger. -/
theorem ContainingPair.impossible_of_second_triality_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n)
    (d : (K₂ ⧸ pCore 2 K₂) ≃* Triality.Standard.BinaryCarrier n hnn) : False := by
  let := C.second_component.perfect
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hnn) :=
    Group.IsPerfect.ofSurjective
      (f := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K₂)))
      (d.surjective.comp (QuotientGroup.mk'_surjective _))
  have hne := C.distinct_of_second_sylow_unique_quotient d
    (Triality.Standard.binary_sylow_overgroup_component_unique n hnn)
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K₂.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  exact C.three_dvd_of_triality_quotient hn C.t_mem hK hLK hnn b

/-- Either literal binary triality quotient excludes the containing pair. -/
theorem ContainingPair.impossible_of_triality_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Triality.Standard.BinaryCarrier n hnn) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Triality.Standard.BinaryCarrier n hnn)) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_triality_quotient hchoice hmany hn hna hnn e
  · exact C.impossible_of_second_triality_quotient hchoice hmany hn hna hnn e

/-- The literal triality predicate of Theorem C discharges either containing row. -/
theorem ContainingPair.impossible_of_triality_model
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 0 < n)
    (he : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K₁ ⧸ pCore 2 K₁) ∨
      Triality.Standard.IsTrialityGroupAt (2 ^ n) (K₂ ⧸ pCore 2 K₂)) : False := by
  apply C.impossible_of_triality_quotient hchoice hmany hn hna hnn
  exact he.imp ((Triality.Standard.isTrialityGroupAt_binary_iff _ n hnn).mp)
    ((Triality.Standard.isTrialityGroupAt_binary_iff _ n hnn).mp)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
