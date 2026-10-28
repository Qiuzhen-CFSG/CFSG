module
public import Stellmacher.SectionTen.TenOneSmallDerived
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The middle four-center lies in the neighborhood derived subgroup

In the ambient Section Ten geometry, the derived subgroup of the generated
middle neighborhood contains the middle four-center. No small-module or
large-module hypothesis is needed.

The neighborhood is nonabelian: otherwise the first module centralizes the
terminal module and critical noncontainment contradicts the endpoint
centralizer bound. Its derived subgroup is normal in the middle two-core
and lies in the elementary first module. A nontrivial normal subgroup of
a finite two-group meets its center; exponent two puts the resulting point
inside the middle omega center. The derived/center intersection is invariant
under the middle stabilizer. The proved absence of an invariant line, and
the center's order four, make that intersection the entire center.

This is the lower-bound step for the common derived equality in Stellmacher
(10.1), Journal of Algebra 190 (1997), printed p.60, from
`refs/files/stellmacher-n-group.pdf` and its local opening hypotheses.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The middle center is contained in the actual generated-neighborhood derived subgroup. -/
public theorem ten_one_middle_center_le_neighborhood_derived
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ZAt ctx.Γ middle ≤ DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle) := by
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let D := DerivedAmbient W
  let Q := QAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hWQ : W ≤ Q := nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hDW : D ≤ W := Subgroup.map_subtype_le _
  have hDQ : D ≤ Q := hDW.trans hWQ
  have hQP : Q ≤ GAt ctx.Γ middle := by
    dsimp only [Q]
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hDnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hD : D = ⁅W, W⁆ := Subgroup.map_subtype_commutator W
    rw [hD]
    have hWmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle hactor)
    rw [Subgroup.map_commutator, hWmap]
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hzero : ⁅W, W⁆ = ⊥ := by
      change (_root_.commutator W).map W.subtype = ⊥ at hbot
      rwa [Subgroup.map_subtype_commutator] at hbot
    have hVW (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
        VAt ctx.Γ vertex ≤ W :=
      le_sSup ⟨vertex, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
    have hpair : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
        VAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono (hVW _ hfirst) (hVW _ hterminal)).trans_eq hzero)
    exact hopen.first_noncontainment
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hpair).trans hopen.endpoint_centralizer)
  have hDFirst : D ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    (ten_one_generated_derived_le_intersection ctx middle hpath).trans inf_le_left
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case
      (by omega : 1 < ctx.criticalPath.length)).1
  let _ : (D.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr (hQP.trans hDnorm)
  let _ : Nontrivial (D.subgroupOf Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv]
      exact (Subgroup.one_lt_card_iff_ne_bot D).mpr hDne)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 Q) := ⟨by
    change IsPGroup 2 (ctx.Γ.twoCoreAt middle)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt ctx.Γ middle)).map _⟩
  obtain ⟨x, hxne, hxcenter⟩ :=
    exists_nontrivial_center_mem_normal (D.subgroupOf Q) (p := 2)
  have hxD : ((x : Q) : G) ∈ D := x.property
  have hxpow : ((x : Q) : G) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (hDFirst hxD)
  have hxZ : ((x : Q) : G) ∈ Z := by
    rw [show Z = omegaOneCenter Q from hopen.center_omega]
    refine ⟨(x : Q), ?_, rfl⟩
    refine ⟨(⟨x, hxcenter⟩ : Subgroup.center Q), ?_, rfl⟩
    apply Subgroup.subset_closure
    change (⟨x, hxcenter⟩ : Subgroup.center Q) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hxpow
  let U := D ⊓ Z
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hxone : ((x : Q) : G) = 1 := by
      have hm : ((x : Q) : G) ∈ U := ⟨hxD, hxZ⟩
      simpa [hbot] using hm
    exact hxne (Subtype.ext (Subtype.ext hxone))
  have hUnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hDnorm (stabilizer_le_normalizer_z ctx.Γ middle)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcardNeTwo := ten_one_no_invariant_middle_line ctx middle hpath U inf_le_right hUnorm
  have hpositive := (Subgroup.one_lt_card_iff_ne_bot U).mpr hUne
  have hdiv : Nat.card U ∣ 4 := hopen.center_card ▸ Subgroup.card_dvd_of_le
    (inf_le_right : U ≤ Z)
  have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have hcard : Nat.card U = 4 := by
    interval_cases h : Nat.card U <;> norm_num at *
  have hUeq : U = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by
    rw [hcard, show Nat.card Z = 4 from hopen.center_card])
  exact hUeq.symm.le.trans inf_le_left

end Stellmacher.SectionTen
