module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
public import Theory.SpecificGroups.Alternating.SevenFiveRestrictionLift

/-!
# No intermediate point component in an alternating-seven cover

The original field-four seed has literal A₅ two-core quotient. The full
Sylow normalizes both it and the point component. The seven-letter
restriction then makes the point component equal to the seed or to the
whole containing component. Its lift through O₂,Z retains both the two-core
and the covering center. Both alternatives contradict the strict chain.

The chosen-flag application derives field four and seed membership from
the earlier checked catalogue. SourceModules uses this to exclude every
remaining B.4/B.5 central-quotient alternative without assuming a shortened
embedding list. Earlier geometry and the seed marking retain final
discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith A.3.14(2), pp.49--50, and 11.4.2, p.776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- A full-Sylow-normalized A₅ core section has no intermediate perfect
full-Sylow-normalized subgroup in an A₇ central core cover. -/
theorem five_seven_intermediate {U B J : Subgroup G}
    (hU : U ∈ Chapter1.L G (T : Subgroup G))
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hUB : U ≤ B) (hBJ : B ≤ J)
    (eU : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5))
    (eJ : ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ≃*
      alternatingGroup (Fin 7)) : B = U ∨ B = J := by
  have hUJ := hUB.trans hBJ
  let a := (centralPreimageQuotientEquiv (pCore 2 J)).trans eJ
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 J)))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralPreimage (pCore 2 J) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  let u := subgroupOfEquivOfLe hUJ
  let b := subgroupOfEquivOfLe hBJ
  let := Chapter1.mem_L_isPerfect hU
  let := Chapter1.mem_L_isPerfect hB
  let := Chapter1.mem_L_isPerfect hJ
  let : Group.IsPerfect (U.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  let : Group.IsPerfect (B.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  have hu : (P : Subgroup J) ≤ normalizer (U.subgroupOf J : Set J) := by
    rw [hP,← subgroupOf_normalizer_eq hUJ]
    exact comap_mono hTU
  have hb : (P : Subgroup J) ≤ normalizer (B.subgroupOf J : Set J) := by
    rw [hP,← subgroupOf_normalizer_eq hBJ]
    exact comap_mono hTB
  rcases Theory.SpecificGroups.Alternating.SevenFivePlacement.perfect_overgroup_eq_or_top_of_centralPreimage
      q hq hk (U.subgroupOf J) (B.subgroupOf J)
      ((QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans eU) P hu hb
      (comap_mono hUB) with he | he
  · left
    have hh := congrArg (map J.subtype) he
    simpa only [map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hUJ] using hh
  · exact Or.inr (le_antisymm hBJ (subgroupOf_eq_top.mp he))

private def seven_central_quotient {A : Type*} [Group A]
    (hm : IsAlternating A 7 ∨ IsAlternatingCover A 7) :
    (A ⧸ center A) ≃* alternatingGroup (Fin 7) := Classical.choice <| by
  rcases hm with ha | hc
  · let e := ha.some
    exact ⟨(QuotientGroup.congr _ _ e (center_map_equiv e)).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)⟩
  · exact hc.2.2

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- Both alternating-seven containing models contradict the strict source chain. -/
theorem not_alternating_seven_overcomponent
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K)
    (hU : E.L₁ ∈ Chapter1.L G (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G))
    (eU : (E.L₁ ⧸ pCore 2 E.L₁) ≃* alternatingGroup (Fin 5))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : E.Kz < J) :
    ¬ (IsAlternating (J ⧸ pCore 2 J) 7 ∨ IsAlternatingCover (J ⧸ pCore 2 J) 7) := by
  intro hm
  rcases five_seven_intermediate hU h.point_mem_local_family hJ hTU
      (sylow_normalizes_point h) (sylow_normalizes_overcomponent h hJ hlt.le)
      (le_conjugateSpanBy _ _) hlt.le eU (seven_central_quotient hm) with he | he
  · exact (h.strict_comparison hf hne).2.1.ne he.symm
  · exact hlt.ne he

/-- The original chosen flag supplies field four and the actual A₅ seed marking. -/
theorem ofFlag_not_alternating_seven_overcomponent
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ (IsAlternating (J ⧸ pCore 2 J) 7 ∨ IsAlternatingCover (J ⧸ pCore 2 J) 7) := by
  have hd := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card S.field.Carrier = 4 by rw [S.field.card_eq,hd]; norm_num)
  exact not_alternating_seven_overcomponent h (fixed_and_transitive D S _ hlinear h1132).1 hne
    (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm)
    (f.sylow_normalizes_Li 0) (e.trans a) hJ hlt

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
