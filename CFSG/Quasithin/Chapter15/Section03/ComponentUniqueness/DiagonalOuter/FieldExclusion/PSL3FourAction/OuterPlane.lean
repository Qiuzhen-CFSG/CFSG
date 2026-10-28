module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.Descent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.FixedIndex
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveField
public import Theory.SpecificGroups.PSL3Four.OuterPlane.FieldFixer
public import Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence

/-!
# Excluding a PSL₃(4) plane with no nonidentity inner actor

The solvable residual of an actor's fixed subgroup in the simple quotient
has a perfect lift fixed by that actor. The TI restriction fixes this lift
under the entire plane. Its image is therefore fixed by the whole projected
plane, even when arbitrary fixed points do not lift through the central cover.
Relabeling the quotient commutes with this construction.

Standard automorphism coverage and the field-occurrence calculation give an
actor conjugate to entrywise Frobenius. The standard automorphisms fixing its
binary fixed subgroup are just identity and Frobenius, so the faithful plane
would have at most two elements, a contradiction. The final theorem derives
relative normalization from C_G(f) and forces a nonidentity inner actor.
All three matrix inputs are discharged by the imported model theorems.

This closes the branch with no nonidentity inner actor for every finite
quasisimple central cover, including SL₃(4). The stronger conclusion uses
neither the joint residual nor the component centralizer alternative, and
does not require an order-27 subgroup. The branch with an inner actor and
the final source-theorem assembly remain with the parent module's owner.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137 (PDF p.1154). The standard matrix representatives are
those in GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction.OuterPlane
variable {K A : Type*} [Group K] [Group A] [Group.IsPerfect K]

/-- The covering-map descent and the characteristic-quotient descent agree
through the specified model equivalence. -/
theorem projectiveAutMap_eq_centralQuotientAction
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    projectiveAutMap e = MulAut.centralQuotientAction e := by
  ext a x
  obtain ⟨y, rfl⟩ := (projectiveCover e).surjective x
  exact (projectiveAutMap_apply e a y).trans
    (MulAut.centralQuotientAction_apply e a y).symm

private theorem perfect_isPPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The binary subgroup fixed by Frobenius is perfect, so its embedded
solvable residual is the entire fixed subgroup. This uses the actual fixed
subgroup isomorphism, not a group-family label. -/
theorem field_fixedPerfectResidual_eq :
    MulAut.fixedPerfectResidual Matrix.PSL3Four.pslFrobenius =
      Matrix.PSL3Four.pslFrobenius.fixedSubgroup := by
  let e := Matrix.PSL3Four.projectiveFieldFixedEquiv
  let := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Four.pslFrobenius.fixedSubgroup :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  simp only [MulAut.fixedPerfectResidual, solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.subtype_range]

omit [Group.IsPerfect K] in
/-- The coverage theorem's simplicity and nonsolvability hypotheses are
inherited from the supplied quasisimple cover. -/
theorem projectiveModel_hypotheses [IsQuasisimple K]
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    IsSimpleGroup Matrix.PSL3Four.PSL ∧ ¬ Group.IsSolvable Matrix.PSL3Four.PSL := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup Matrix.PSL3Four.PSL := e.symm.isSimpleGroup
  let : Group.IsPerfect Matrix.PSL3Four.PSL :=
    Group.IsPerfect.ofSurjective (f := (projectiveCover e).toMonoidHom)
      (projectiveCover e).surjective
  exact ⟨inferInstance, Group.IsPerfect.not_isSolvable _⟩

/-- Perfect residuals of quotient fixed subgroups lift far enough for the
TI restriction to force fixation by the entire projected plane. -/
theorem fixedPerfectResidual_le_projective_fixedSubgroup [Finite K]
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (hφ : FixesTwoPerfectSubgroups φ) (a : A) (ha : a ≠ 1) :
    MulAut.fixedPerfectResidual (projectiveAction e φ a) ≤
      fixedSubgroupOfAction (projectiveAction e φ) := by
  obtain ⟨D, hD, hfix, hmap⟩ := MulAut.exists_perfect_fixed_lift e (φ a)
  let := hD
  have hDφ : D ≤ fixedSubgroupOfAction φ := by
    intro x hx b
    exact hφ a ha D perfect_isPPerfect
      (fun y => (MulAut.mem_fixedSubgroup (φ a) y).mp (hfix y.property)) b ⟨x, hx⟩
  have hm : D.map (projectiveCover e).toMonoidHom =
      MulAut.fixedPerfectResidual (projectiveAction e φ a) := by
    simpa only [projectiveCover, projectiveAction, MonoidHom.comp_apply,
      projectiveAutMap_eq_centralQuotientAction] using hmap
  rw [← hm]
  exact (map_mono hDφ).trans (projective_fixedSubgroup_le e φ)

/-- Changing the quotient identification conjugates the actual projective
action; no lift of the relabeling automorphism to the cover is needed. -/
theorem projectiveAction_relabel
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (d : MulAut Matrix.PSL3Four.PSL)
    (φ : A →* MulAut K) (a : A) :
    projectiveAction (e.trans d) φ a = MulAut.congr d (projectiveAction e φ a) := by
  ext x
  obtain ⟨y, rfl⟩ := (projectiveCover (e.trans d)).surjective x
  rw [show projectiveAction (e.trans d) φ a = projectiveAutMap (e.trans d) (φ a) from rfl,
    projectiveAutMap_apply]
  change d (e ((φ a y : K) : K ⧸ center K)) =
    d (projectiveAction e φ a (d.symm (d (e (y : K ⧸ center K)))))
  rw [d.symm_apply_apply]
  congr 1
  exact (projectiveAutMap_apply e (φ a) y).symm

/-- The absence of nonidentity inner actors survives faithful descent. -/
theorem projectiveAction_noInner
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (houter : ∀ a : A, a ≠ 1 → φ a ∉ MulAut.innerSubgroup K) :
    ∀ a : A, a ≠ 1 → projectiveAction e φ a ∉
      MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
  intro a ha h
  exact houter a ha ((projectiveAutMap_mem_inner_iff e (φ a)).mp h)

omit [Group.IsPerfect K] in
private theorem injective_of_noInner (φ : A →* MulAut K)
    (houter : ∀ a : A, a ≠ 1 → φ a ∉ MulAut.innerSubgroup K) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro a ha
  apply mem_bot.mpr
  by_contra h
  exact houter a h (ha ▸ (MulAut.innerSubgroup K).one_mem)

/-- One field actor suffices, provided the standard pointwise-fixer
calculation holds and the relabeled plane consists of standard automorphisms. -/
theorem contradiction_of_field_occurrence [Finite K] [IsKleinFour A]
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (hinj : Function.Injective φ) (hφ : FixesTwoPerfectSubgroups φ)
    (a : A) (ha : a ≠ 1) (d : MulAut Matrix.PSL3Four.PSL)
    (hd : MulAut.congr d (projectiveAction e φ a) = Matrix.PSL3Four.pslFrobenius)
    (hstandard : ∀ b : A, projectiveAction (e.trans d) φ b ∈
      Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F)
    (hfixer : ∀ b : MulAut Matrix.PSL3Four.PSL,
      b ∈ Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F →
      (∀ x ∈ Matrix.PSL3Four.pslFrobenius.fixedSubgroup, b x = x) →
      b = 1 ∨ b = Matrix.PSL3Four.pslFrobenius) : False := by
  classical
  let ψ := projectiveAction (e.trans d) φ
  have hψ : Function.Injective ψ := projectiveAction_injective _ φ hinj
  have hψa : ψ a = Matrix.PSL3Four.pslFrobenius :=
    (projectiveAction_relabel e d φ a).trans hd
  have hfixed : Matrix.PSL3Four.pslFrobenius.fixedSubgroup ≤
      fixedSubgroupOfAction ψ := by
    rw [← field_fixedPerfectResidual_eq, ← hψa]
    exact fixedPerfectResidual_le_projective_fixedSubgroup _ φ hφ a ha
  have hcases (b : A) : b = 1 ∨ b = a := by
    rcases hfixer (ψ b) (hstandard b) (fun x hx => hfixed hx b) with h | h
    · exact Or.inl (hψ (h.trans (map_one ψ).symm))
    · exact Or.inr (hψ (h.trans hψa.symm))
  let : Finite A := Nat.finite_of_card_ne_zero (by simp)
  let : Fintype A := Fintype.ofFinite A
  have hsub : (Finset.univ : Finset A) ⊆ {1, a} := by
    intro b _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases b
  have hc := Finset.card_le_card hsub
  have htwo : ({1, a} : Finset A).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, IsKleinFour.card_four'] at hc
  omega

/-- Conditional assembly from standard coverage and the two independent
matrix calculations. Their proved instantiations are supplied below. -/
theorem contradiction_of_standard_model_facts [Finite K] [IsKleinFour A]
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (hφ : FixesTwoPerfectSubgroups φ)
    (houter : ∀ a : A, a ≠ 1 → φ a ∉ MulAut.innerSubgroup K)
    (hcoverage : Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F = ⊤)
    (hoccurrence : ∀ ψ : A →* MulAut Matrix.PSL3Four.PSL,
      (∀ b : A, ψ b ∈ Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F) →
      (∀ b : A, b ≠ 1 → ψ b ∉ MulAut.innerSubgroup Matrix.PSL3Four.PSL) →
      ∃ a : A, a ≠ 1 ∧ ∃ d : MulAut Matrix.PSL3Four.PSL,
        MulAut.congr d (ψ a) = Matrix.PSL3Four.pslFrobenius)
    (hfixer : ∀ b : MulAut Matrix.PSL3Four.PSL,
      b ∈ Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F →
      (∀ x ∈ Matrix.PSL3Four.pslFrobenius.fixedSubgroup, b x = x) →
      b = 1 ∨ b = Matrix.PSL3Four.pslFrobenius) : False := by
  obtain ⟨a, ha, d, hd⟩ := hoccurrence (projectiveAction e φ)
    (fun _ => hcoverage ▸ mem_top _) (projectiveAction_noInner e φ houter)
  exact contradiction_of_field_occurrence e φ (injective_of_noInner φ houter) hφ
    a ha d hd (fun _ => hcoverage ▸ mem_top _) hfixer

/-- Relative normality in C_G(f) supplies the actual action. The TI geometry
and the three model facts then force a nonidentity inner actor, without any
restriction on the center of the quasisimple cover. -/
theorem exists_inner_actor_of_standard_model_facts
    {G : Type*} [Group G] [Finite G] (U L : Subgroup G) [IsKleinFour U]
    [IsQuasisimple L]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U) (f : G)
    (hLf : L ≤ centralizer ({f} : Set G))
    (hn : (L.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL)
    (hcoverage : Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F = ⊤)
    (hoccurrence : ∀ ψ : U →* MulAut Matrix.PSL3Four.PSL,
      (∀ b : U, ψ b ∈ Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F) →
      (∀ b : U, b ≠ 1 → ψ b ∉ MulAut.innerSubgroup Matrix.PSL3Four.PSL) →
      ∃ a : U, a ≠ 1 ∧ ∃ d : MulAut Matrix.PSL3Four.PSL,
        MulAut.congr d (ψ a) = Matrix.PSL3Four.pslFrobenius)
    (hfixer : ∀ b : MulAut Matrix.PSL3Four.PSL,
      b ∈ Matrix.PSL3.OuterSolvable.standard Matrix.PSL3Four.F →
      (∀ x ∈ Matrix.PSL3Four.pslFrobenius.fixedSubgroup, b x = x) →
      b = 1 ∨ b = Matrix.PSL3Four.pslFrobenius) :
    ∃ hUN : U ≤ normalizer (L : Set G),
      ∃ a : U, a ≠ 1 ∧
        (L.normalizerMonoidHom.comp (inclusion hUN)) a ∈ MulAut.innerSubgroup L := by
  have hUN : U ≤ normalizer (L : Set G) :=
    hUf.trans ((normal_subgroupOf_iff_le_normalizer hLf).mp hn)
  refine ⟨hUN, ?_⟩
  by_contra! houter
  exact contradiction_of_standard_model_facts e _
    (conjugation_fixes_twoPerfect U L hU hUN) houter hcoverage hoccurrence hfixer

/-- A four-group acting on a finite perfect central cover of the actual
PSL₃(4), with the TI fixed-subgroup restriction, cannot have every
nonidentity actor outer. All model inputs are discharged. -/
theorem contradiction_of_no_inner_actor [Finite K] [IsKleinFour A]
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (hφ : FixesTwoPerfectSubgroups φ)
    (houter : ∀ a : A, a ≠ 1 → φ a ∉ MulAut.innerSubgroup K) : False := by
  exact contradiction_of_standard_model_facts e φ hφ houter
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card
      Matrix.PSL3Four.F (m := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F))
    Matrix.PSL3Four.OuterPlane.FieldOccurrence.exists_frobenius_actor
    Matrix.PSL3Four.OuterPlane.FieldFixer.standard_fixer_eq_one_or_frobenius

/-- Relative normality in C_G(f) gives normalization by the TI four-group,
and its action on a quasisimple PSL₃(4) cover has a nonidentity inner actor.
This excludes the outer-plane branch before using any residual hypothesis. -/
theorem exists_inner_actor
    {G : Type*} [Group G] [Finite G] (U L : Subgroup G) [IsKleinFour U]
    [IsQuasisimple L]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U) (f : G)
    (hLf : L ≤ centralizer ({f} : Set G))
    (hn : (L.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) :
    ∃ hUN : U ≤ normalizer (L : Set G),
      ∃ a : U, a ≠ 1 ∧
        (L.normalizerMonoidHom.comp (inclusion hUN)) a ∈ MulAut.innerSubgroup L := by
  have hUN : U ≤ normalizer (L : Set G) :=
    hUf.trans ((normal_subgroupOf_iff_le_normalizer hLf).mp hn)
  refine ⟨hUN, ?_⟩
  by_contra! houter
  exact contradiction_of_no_inner_actor e _
    (conjugation_fixes_twoPerfect U L hU hUN) houter

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction.OuterPlane
