module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SolvableImages
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SmallContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.BinaryLinearContaining
public import Theory.GroupTheory.CComponent.TwoRankObstruction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Alternating containing quotients in source 10.2.6

The first Suzuki group is too large to survive in A₇, A₈ or the central
three-cover of A₇. The original quotient therefore contains a cubic.
For A₇, sixteen does not divide the order, so every Sylow overgroup has
at most one C-component. For A₈ the actual PSL₄(2) isomorphism supplies
that uniqueness. It lifts through the central kernel for the cover.

The applications prove distinctness and exclude either literal containing
factor, preserving the original exchanger and half-join. Together with the
previous A₅ and A₆ results this closes every alternating Theorem C row.
The remaining source branches and final assembly belong to
qt-d-10-nona5-half-sylow-unique; only ModuleChoiceAt is external, with its
final discharge retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private instance (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
    (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective

/-- A small literal quotient with full-Sylow uniqueness excludes either pair member. -/
theorem ContainingPair.impossible_of_small_unique_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] (hu : SylowOvergroupComponentUnique X)
    (hc : Nat.card X < 29120)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* X) ∨ Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* X)) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K₁))
    have hk : q.ker = pCore 2 K₁ := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
    exact C.impossible_of_first_small_solvable_image hchoice hmany hn hna q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) hu hc
  · let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K₂))
    have hk : q.ker = pCore 2 K₂ := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
    exact C.impossible_of_second_small_solvable_image hchoice hmany hn hna q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) hu hc

private theorem seven_unique : SylowOvergroupComponentUnique (alternatingGroup (Fin 7)) := by
  apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Exclude either actual A₇ quotient, with no separate distinctness premise. -/
theorem ContainingPair.impossible_of_alternating_seven_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* alternatingGroup (Fin 7))) : False := by
  apply C.impossible_of_small_unique_quotient hchoice hmany hn hna seven_unique _ he
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The A₈ row uses its actual binary linear marking. -/
theorem ContainingPair.impossible_of_alternating_eight_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 8)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* alternatingGroup (Fin 8))) : False := by
  let e := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  apply C.impossible_of_small_unique_quotient hchoice hmany hn hna
    (.of_equiv e (BinaryLinear.sylow_overgroup_component_unique_le_five 4 (by decide))) _ he
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- All alternating rows of the genuine Theorem C catalogue are excluded. -/
theorem ContainingPair.impossible_of_alternating_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (he : Section02.LocalModels.IsAlternating (K₁ ⧸ pCore 2 K₁) n ∨
      Section02.LocalModels.IsAlternating (K₂ ⧸ pCore 2 K₂) n) : False := by
  interval_cases n
  · exact C.impossible_of_small_alternating_quotient hchoice hmany hn hna (Or.inl rfl) he
  · exact C.impossible_of_small_alternating_quotient hchoice hmany hn hna (Or.inr rfl) he
  · exact C.impossible_of_alternating_seven_quotient hchoice hmany hn hna he
  · exact C.impossible_of_alternating_eight_quotient hchoice hmany hn hna he

private theorem seven_cover_tests {X : Type*} [Group X] [Finite X]
    (hm : Section02.LocalModels.IsAlternatingCover X 7) :
    SylowOvergroupComponentUnique X ∧ Nat.card X < 29120 := by
  obtain ⟨_,⟨ez⟩,⟨e⟩⟩ := hm
  let : Group.IsSolvable (center X) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  refine ⟨.of_quotient (center X) (.of_equiv e seven_unique),?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (center X),
    Nat.card_congr e.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The central A₇ cover retains its literal center quotient and has order 7560. -/
theorem ContainingPair.impossible_of_central_seven_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Section02.LocalModels.IsAlternatingCover (K₁ ⧸ pCore 2 K₁) 7 ∨
      Section02.LocalModels.IsAlternatingCover (K₂ ⧸ pCore 2 K₂) 7) : False := by
  rcases he with he | he
  · obtain ⟨hu,hc⟩ := seven_cover_tests he
    exact C.impossible_of_small_unique_quotient hchoice hmany hn hna hu hc
      (Or.inl ⟨MulEquiv.refl _⟩)
  · obtain ⟨hu,hc⟩ := seven_cover_tests he
    exact C.impossible_of_small_unique_quotient hchoice hmany hn hna hu hc
      (Or.inr ⟨MulEquiv.refl _⟩)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
