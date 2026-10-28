module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.QuotientKernel
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import CFSG.Quasithin.ChapterK.Defs

/-!
# The marked offender on the ten-dimensional exterior module

For the actual SL₅(2) action on Λ²(F₂⁵), the last-column shear subgroup X
has rank four, fixes the six-space V₆ and acts quadratically, giving ratio one.
Each nontrivial subgroup moves at least three dimensions; a noncyclic subgroup
fixes exactly V₆. Thus X is the only offender below itself and is a minimal
best offender. The quotient-kernel calculation also proves faithfulness.

The literal B.7.1 restriction excludes other minimal best offenders that
preserve and move V₆, conditional only on the absence of strong offenders in
the six-dimensional action image. Its A₈ identification, the passage from an
arbitrary Sylow offender to that restriction, the global lower bound, and
module recognition remain source obligations. In particular the upper bound
proved here is not the completed K.3.2 classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.3,
printed p.455, with §§B.7.1 and 12.5.
-/

public section
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open Representation.BinaryOffender
open scoped ENNReal

namespace CFSG.Quasithin.ChapterK.Linear.Exterior

private theorem dim_V₆ : Module.finrank (ZMod 2) V₆ = 6 :=
  standard_dimensions.2.2.2.1

theorem shear_rank : rank shearSubgroup = 4 := by
  rw [rank, card_shearSubgroup]
  decide

theorem shear_elementary : IsElementaryTwo shearSubgroup := by
  refine ⟨?_, inferInstance⟩
  intro h
  have hr := shear_rank
  rw [h, BinaryOffender.rank_bot] at hr
  contradiction

theorem shear_fixedCodim : fixedCodim (exteriorAction 2) shearSubgroup = 4 := by
  have h := fixedCodim_add_finrank (exteriorAction 2) shearSubgroup
  rw [fixedSpace_shearSubgroup, dim_V₆, finrank_exteriorModule_two] at h
  omega

theorem shear_actionRatio : actionRatio (exteriorAction 2) shearSubgroup = 1 := by
  rw [actionRatio, shear_fixedCodim, shear_rank]
  exact ENNReal.div_self (by norm_num) (by simp)

theorem shear_quadratic : IsQuadratic (exteriorAction 2) shearSubgroup := by
  intro a ha b hb v
  obtain ⟨u, rfl⟩ := (mem_shearSubgroup a).mp ha
  obtain ⟨w, rfl⟩ := (mem_shearSubgroup b).mp hb
  have hw : exteriorAction 2 (shear w) v - v ∈ V₆ := by
    change SL5ExteriorSquare.displacement (shear w) v ∈ V₆
    rw [shear_displacement]
    exact shearWedge_mem_V₆ _ _
  rw [← fixedSpace_shearSubgroup] at hw
  exact hw ⟨shear u, shear_mem u⟩

private theorem shear_fixedSpace_le (u : ShearParameter) (hu : u ≠ 0) :
    SL5ExteriorSquare.fixedSpace (shear u) ≤
      V₆ ⊔ Submodule.span (ZMod 2) {shearSection u} := by
  intro v hv
  rcases (fixed_shear_iff u hu v).mp hv with h | h
  · exact Submodule.mem_sup_left ((mem_V₆_iff_shearQuotient v).mpr h)
  · apply Submodule.mem_sup.mpr
    refine ⟨v - shearSection u, ?_, shearSection u, Submodule.subset_span (by simp),
      sub_add_cancel _ _⟩
    rw [mem_V₆_iff_shearQuotient, map_sub, h, shearQuotient_section, sub_self]

private theorem shear_fixed_dimension_le (u : ShearParameter) (hu : u ≠ 0) :
    Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace (shear u)) ≤ 7 := by
  have hle := Submodule.finrank_mono (shear_fixedSpace_le u hu)
  have hn : shearSection u ≠ 0 := by
    intro h
    have he := congrArg shearQuotient h
    exact hu (by simpa only [shearQuotient_section, map_zero] using he)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    V₆ (Submodule.span (ZMod 2) {shearSection u})
  rw [dim_V₆, finrank_span_singleton hn] at hdim
  omega

/-- Every nontrivial subgroup of the marked radical moves at least three dimensions. -/
theorem subgroup_fixedCodim_ge_three {B : Subgroup Group}
    (hB : B ≤ shearSubgroup) (hne : B ≠ ⊥) :
    3 ≤ fixedCodim (exteriorAction 2) B := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp (hB hg)
  have hu : u ≠ 0 := by simpa using hg1'
  have hle : BinaryOffender.fixedSpace (exteriorAction 2) B ≤
      SL5ExteriorSquare.fixedSpace (shear u) := by
    intro v hv
    exact (mem_fixedSpace _ _).mpr (hv ⟨shear u, hg⟩)
  have hd := (Submodule.finrank_mono hle).trans (shear_fixed_dimension_le u hu)
  have he := fixedCodim_add_finrank (exteriorAction 2) B
  rw [finrank_exteriorModule_two] at he
  omega

/-- A noncyclic subgroup of the radical has exactly the same fixed space as the radical. -/
theorem noncyclic_fixedSpace {B : Subgroup Group} (hB : B ≤ shearSubgroup)
    (hr : 1 < rank B) : BinaryOffender.fixedSpace (exteriorAction 2) B = V₆ := by
  apply le_antisymm
  · intro v hv
    rw [mem_V₆_iff_shearQuotient]
    by_contra hv0
    have hchoice (g : B) : g.val = 1 ∨ g.val = shear (shearQuotient v) := by
      obtain ⟨u, hu⟩ := (mem_shearSubgroup g.val).mp (hB g.property)
      by_cases hu0 : u = 0
      · exact Or.inl (hu.symm.trans (hu0 ▸ shear_zero))
      · have hf : v ∈ SL5ExteriorSquare.fixedSpace (shear u) := by
          apply (mem_fixedSpace _ _).mpr
          rw [hu]
          exact hv g
        have he := ((fixed_shear_iff u hu0 v).mp hf).resolve_left hv0
        exact Or.inr (hu.symm.trans (congrArg shear he.symm))
    classical
    let f : B → Bool := fun g => decide (g.val = 1)
    have hf : Function.Injective f := by
      intro g h he
      apply Subtype.ext
      have he' : (g.val = 1) ↔ (h.val = 1) := by
        simpa only [f, decide_eq_decide] using he
      rcases hchoice g with hg | hg
      · exact hg.trans (he'.mp hg).symm
      · rcases hchoice h with hh | hh
        · exact (he'.mpr hh).trans hh.symm
        · exact hg.trans hh.symm
    have hc : Nat.card B ≤ 2 := by
      simpa using Nat.card_le_card_of_injective f hf
    have hl := Nat.log_mono_right (b := 2) hc
    change rank B ≤ Nat.log 2 2 at hl
    rw [show Nat.log 2 2 = 1 by decide] at hl
    omega
  · rw [← fixedSpace_shearSubgroup]
    exact fixedSpace_antitone (exteriorAction 2) hB

/-- Noncyclic subgroups of X have fixed codimension four. -/
theorem noncyclic_fixedCodim {B : Subgroup Group} (hB : B ≤ shearSubgroup)
    (hr : 1 < rank B) : fixedCodim (exteriorAction 2) B = 4 := by
  have h := fixedCodim_add_finrank (exteriorAction 2) B
  rw [noncyclic_fixedSpace hB hr, dim_V₆, finrank_exteriorModule_two] at h
  omega

private theorem subgroup_rank_le {B : Subgroup Group} (hB : B ≤ shearSubgroup) :
    rank B ≤ 4 := by
  have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hB)
  change rank B ≤ rank shearSubgroup at h
  rwa [shear_rank] at h

/-- X is the only offender among its own subgroups; this does not yet assert
uniqueness inside an ambient Sylow subgroup. -/
theorem offender_below_shear_iff {B : Subgroup Group} (hB : B ≤ shearSubgroup) :
    IsOffender (exteriorAction 2) B ↔ B = shearSubgroup := by
  constructor
  · intro ho
    have hc := subgroup_fixedCodim_ge_three hB ho.1.1
    have ho2 := ho.2
    have hr : 1 < rank B := by omega
    rw [noncyclic_fixedCodim hB hr] at ho2
    have hcard := ho.1.card_eq_two_pow_rank
    apply Subgroup.eq_of_le_of_card_ge hB
    rw [card_shearSubgroup, hcard]
    have hr4 : rank B = 4 := by have := subgroup_rank_le hB; omega
    rw [hr4]
    decide
  · rintro rfl
    exact ⟨shear_elementary, by rw [shear_fixedCodim, shear_rank]⟩

/-- The marked shear subgroup is a best offender on the actual exterior square. -/
theorem shear_bestOffender : IsBestOffender (exteriorAction 2) shearSubgroup := by
  refine ⟨shear_elementary, ?_⟩
  intro B hB
  have hweight : weight (exteriorAction 2) shearSubgroup = 10 := by
    rw [weight, shear_rank, fixedSpace_shearSubgroup, dim_V₆]
  rw [hweight]
  by_cases hb : B = ⊥
  · rw [hb, weight_bot, finrank_exteriorModule_two]
  have hd := fixedCodim_add_finrank (exteriorAction 2) B
  rw [finrank_exteriorModule_two] at hd
  have hr := subgroup_rank_le hB
  by_cases hr1 : 1 < rank B
  · have hc := noncyclic_fixedCodim hB hr1
    unfold weight
    omega
  · have hc := subgroup_fixedCodim_ge_three hB hb
    unfold weight
    omega

/-- The concrete P*(G,V) assertion used in K.3.2.3. -/
theorem shear_minimalBestOffender : IsMinimalBestOffender (exteriorAction 2) shearSubgroup := by
  refine ⟨shear_bestOffender, ?_⟩
  intro B hB hle
  exact (offender_below_shear_iff hle.1).mp (hB.isOffender _)

/-- The marked actor proves the first global bound in K.3.2.3. -/
theorem quadraticRatio_le_one : quadraticRatio (exteriorAction 2) ≤ 1 := by
  exact iInf_le_of_le shearSubgroup
    (iInf_le_of_le ⟨shear_elementary, shear_quadratic⟩ shear_actionRatio.le)

/-- Faithfulness of the actual ten-dimensional model, proved from its quotient
kernel and the fixed-space bound for nonidentity shears. -/
theorem exterior_faithful : Function.Injective (exteriorAction 2) := by
  apply (injective_iff_map_eq_one (exteriorAction 2)).mpr
  intro g hg
  have hq : ∀ v : V, exteriorAction 2 g v - v ∈ V₆ := by
    intro v
    rw [hg]
    simp
  obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp ((quotient_kernel g).mp hq)
  by_contra hne
  have hu : u ≠ 0 := by simpa using hne
  have hfixed : SL5ExteriorSquare.fixedSpace (shear u) = ⊤ := by
    ext v
    simp only [mem_fixedSpace, Submodule.mem_top, iff_true]
    rw [hg]
    rfl
  have hd := shear_fixed_dimension_le u hu
  rw [hfixed, finrank_top, finrank_exteriorModule_two] at hd
  omega

/-- The literal B.7.1 step in K.3.2.3. The remaining local input is the absence of strong offenders on the
six-dimensional image. Faithfulness and the kernel on V/V₆ are proved for the
literal exterior action; no ten-dimensional offender conclusion is assumed. -/
theorem restriction_exclusion
    {A : Subgroup Group} (hA : IsMinimalBestOffender (exteriorAction 2) A)
    (hstable : ∀ a ∈ A, ∀ w ∈ V₆, exteriorAction 2 a w ∈ V₆)
    (hmove : subspaceCommutator (exteriorAction 2) V₆ A ≠ ⊥)
    (himage : ¬ IsStrongFFModule
      (subspaceImageRepresentation (exteriorAction 2) V₆)) : False := by
  have hbest := ChapterB.source_lemma_B_7_1_1 (exteriorAction 2) V₆ exterior_faithful hA.1
    hstable hmove
  have heq := ((isBestOffender_iff_of_not_strong
    (subspaceImageRepresentation (exteriorAction 2) V₆) himage
    (restrictedSubgroup (exteriorAction 2) V₆ A)).mp hbest).2
  have hspan := (ChapterB.source_lemma_B_7_1_2 (exteriorAction 2) V₆ exterior_faithful hA
    hstable hmove).2 heq.symm |>.2
  have hAX : A ≤ shearSubgroup := by
    intro a ha
    apply (quotient_kernel a).mp
    intro v
    have hv : v ∈ V₆ ⊔ BinaryOffender.fixedSpace (exteriorAction 2) A := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    have hcfix : exteriorAction 2 a c = c := hc ⟨a, ha⟩
    simpa only [map_add, hcfix, add_sub_add_right_eq_sub] using
      V₆.sub_mem (hstable a ha w hw) hw
  apply hmove
  apply (subspaceCommutator_eq_bot_iff (exteriorAction 2) V₆ A).mpr
  rw [← fixedSpace_shearSubgroup]
  exact fixedSpace_antitone (exteriorAction 2) hAX

end CFSG.Quasithin.ChapterK.Linear.Exterior
