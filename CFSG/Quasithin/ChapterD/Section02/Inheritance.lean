module

public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryOffender.RatioInheritance

/-!
# Inheritance of minimal action ratios

This proves D.2.2–D.2.8 of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), printed pp.178–180.
Restriction always uses the faithful image of the setwise stabilizer on
`U`, and the actor is the actual image of `A`, isomorphic to `A/C_A(U)`.
The kernel is normal in `A`, not necessarily in `G`.

The equality alternatives in D.2.2–D.2.4 use `r = r_{A,V}`. The source's
arbitrary-upper-bound consequences D.2.5 and D.2.6 remain valid and are
proved separately. Numerator balance forces equality of the fixed-space
sum; inclusion minimality of a global cubic minimizer excludes the
nontrivial-kernel equality branch. This also gives the strict decrease on
a noncentralized hyperplane fixed space used in D.2.13.
-/

public section
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Iterated commutators of the restricted image embed in the ambient ones. -/
theorem iteratedCommutator_restricted_le (U : Submodule (ZMod 2) V) (A : Subgroup G)
    (k : ℕ) :
    iteratedCommutator (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) k ≤
      (iteratedCommutator ρ A k).comap U.subtype := by
  induction k with
  | zero => exact le_top
  | succ k ih =>
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    exact Submodule.subset_span ⟨g, hg, (v : V), ih hv, rfl⟩

/-- Vanishing iterated commutators descend to the actual action image. -/
theorem iteratedCommutator_restricted_eq_bot (U : Submodule (ZMod 2) V)
    {A : Subgroup G} {k : ℕ} (hk : iteratedCommutator ρ A k = ⊥) :
    iteratedCommutator (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) k = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have h := iteratedCommutator_restricted_le ρ U A k hv
  rw [hk] at h
  exact Subtype.ext h

/-- A cubic actor stays cubic on the restricted image. -/
theorem isCubic_restrictedSubgroup (U : Submodule (ZMod 2) V)
    {A : Subgroup G} (hc : IsCubic ρ A) :
    IsCubic (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) := by
  apply (iteratedCommutator_three_eq_bot_iff _ _).mp
  exact iteratedCommutator_restricted_eq_bot ρ U
    ((iteratedCommutator_three_eq_bot_iff ρ A).mpr hc)

/-- The source minimum condition supplies local ratio minimality. -/
theorem QhatStar.mem_RPlus {A : Subgroup G} (hA : A ∈ QhatStar ρ) : A ∈ RPlus ρ := by
  apply RPlus.of_iterated_minimum ρ hA.1.2.1 3
    ((iteratedCommutator_three_eq_bot_iff ρ A).mpr hA.1.2.2.1)
  simpa only [iteratedRatio_three] using hA.1.2.2.2

/-- Minimality is strict on each nontrivial proper subactor. -/
theorem QhatStar.ratio_lt_of_lt {A B : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hBA : B < A) (hB : B ≠ ⊥) : actionRatio ρ A < actionRatio ρ B := by
  have hplus := QhatStar.mem_RPlus ρ hA
  refine lt_of_le_of_ne (hplus.2 B hBA.le hB) ?_
  intro heq
  have hBc : IsCubic ρ B := by
    apply (iteratedCommutator_three_eq_bot_iff ρ B).mp
    exact le_bot_iff.mp ((iteratedCommutator_mono ρ hBA.le 3).trans_eq
      ((iteratedCommutator_three_eq_bot_iff ρ A).mpr hA.1.2.2.1))
  have hmin : B ∈ QhatMin ρ := ⟨hA.1.1, hplus.1.of_le hBA.le hB, hBc,
    heq.symm.trans hA.1.2.2.2⟩
  exact hBA.ne (hA.2 B hmin hBA.le)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- In the faithful spanning branch every image subactor retains its original ratio. -/
theorem RPlus.restricted_of_faithful_span {A : Subgroup G} (hA : A ∈ RPlus ρ)
    (U : Submodule (ZMod 2) V) (hU : A ≤ subspaceStabilizer ρ U)
    (hn : ¬ U ≤ fixedSpace ρ A) (hk : subspaceKernel ρ U A = ⊥)
    (hs : U ⊔ fixedSpace ρ A = ⊤) :
    restrictedSubgroup ρ U A ∈ RPlus (subspaceImageRepresentation ρ U) := by
  refine ⟨hA.1.restrictedSubgroup ρ U hU hn, fun D hD hDn => ?_⟩
  obtain ⟨B, hBA, _, hBD⟩ := exists_subgroup_restrictedSubgroup ρ U hU D hD
  have hB : B ≠ ⊥ := by
    intro hb
    exact hDn (by rw [← hBD, hb, restrictedSubgroup_bot])
  rw [← hBD, actionRatio_restricted_subactor_eq ρ U hA.1 hU hk hs hBA,
    actionRatio_restricted_subactor_eq ρ U hA.1 hU hk hs le_rfl]
  exact hA.2 B hBA hB

/-- D.2.4, at the exact action ratio: the kernel-decrease case is excluded. -/
theorem RPlus.restriction_alternatives {A : Subgroup G} (hA : A ∈ RPlus ρ)
    (U : Submodule (ZMod 2) V) (hU : A ≤ subspaceStabilizer ρ U)
    (hn : ¬ U ≤ fixedSpace ρ A) :
    actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) <
        actionRatio ρ A ∨
    (subspaceKernel ρ U A = ⊥ ∧ U ⊔ fixedSpace ρ A = ⊤ ∧
      restrictedSubgroup ρ U A ∈ RPlus (subspaceImageRepresentation ρ U) ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
        actionRatio ρ A ∧
      ∀ D ≤ A, D ≠ ⊥ →
        fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U D) =
          fixedCodim ρ D ∧
        actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U D) =
          actionRatio ρ D ∧ actionRatio ρ A ≤ actionRatio ρ D) ∨
    (subspaceKernel ρ U A ∈ RPlus ρ ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
        actionRatio ρ A ∧
      actionRatio ρ (subspaceKernel ρ U A) = actionRatio ρ A ∧
      U ⊔ fixedSpace ρ A = fixedSpace ρ (subspaceKernel ρ U A)) := by
  rcases actionRatio_restriction_alternatives ρ U hA.1 hU hn with
    hi | ⟨hB, hb⟩ | ⟨hk, heq, hs⟩ | ⟨hB, hi, hb, hs⟩
  · exact Or.inl hi
  · exact (not_lt_of_ge (hA.2 _ (subspaceKernel_le ρ U A) hB.1) hb).elim
  · refine Or.inr (Or.inl ⟨hk, hs,
      RPlus.restricted_of_faithful_span ρ hA U hU hn hk hs, heq, ?_⟩)
    intro D hDA hD
    exact ⟨fixedCodim_restricted_subactor_eq ρ U hU hs hDA,
      actionRatio_restricted_subactor_eq ρ U hA.1 hU hk hs hDA, hA.2 D hDA hD⟩
  · exact Or.inr (Or.inr ⟨RPlus.of_equal_ratio ρ hA (subspaceKernel_le ρ U A) hB.1 hb,
      hi, hb, hs⟩)

/-- D.2.5: the genuine arbitrary-upper-bound inheritance theorem. -/
theorem RPlusBound.restricted {A : Subgroup G} {r : ℝ≥0∞}
    (hA : A ∈ RPlusBound ρ r) (U : Submodule (ZMod 2) V)
    (hU : A ≤ subspaceStabilizer ρ U) (hn : ¬ U ≤ fixedSpace ρ A) :
    restrictedSubgroup ρ U A ∈ R (subspaceImageRepresentation ρ U) r := by
  refine ⟨hA.1.1.restrictedSubgroup ρ U hU hn, ?_⟩
  rcases RPlus.restriction_alternatives ρ hA.2 U hU hn with h | h | h
  · exact h.le.trans hA.1.2
  · exact h.2.2.2.1.trans_le hA.1.2
  · exact h.2.1.trans_le hA.1.2

/-- D.2.6: a lower bound on the restricted global minimum forces equality.
The bound `r` is arbitrary; equality is proved, not assumed. -/
theorem RIteratedPlus.restriction_of_le_minimum {A : Subgroup G} {r : ℝ≥0∞} {k : ℕ}
    (hA : A ∈ RIteratedPlus ρ k r) (U : Submodule (ZMod 2) V)
    (hU : A ≤ subspaceStabilizer ρ U) (hn : ¬ U ≤ fixedSpace ρ A)
    (hmin : r ≤ iteratedRatio (subspaceImageRepresentation ρ U) k) :
    iteratedRatio (subspaceImageRepresentation ρ U) k = r ∧
    actionRatio ρ A = r ∧
    actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) = r ∧
    ((subspaceKernel ρ U A = ⊥ ∧ U ⊔ fixedSpace ρ A = ⊤ ∧
      restrictedSubgroup ρ U A ∈ RPlus (subspaceImageRepresentation ρ U)) ∨
    (subspaceKernel ρ U A ∈ RPlus ρ ∧
      actionRatio ρ (subspaceKernel ρ U A) = r ∧
      U ⊔ fixedSpace ρ A = fixedSpace ρ (subspaceKernel ρ U A))) := by
  have hI := RPlusBound.restricted ρ ⟨hA.1.1, hA.2⟩ U hU hn
  have hk := iteratedCommutator_restricted_eq_bot ρ U hA.1.2
  have hlow := iteratedRatio_le (subspaceImageRepresentation ρ U) k hI.1 hk
  have hq : iteratedRatio (subspaceImageRepresentation ρ U) k = r :=
    le_antisymm (hlow.trans hI.2) hmin
  have heq : actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) = r :=
    le_antisymm hI.2 (hmin.trans hlow)
  have hiA := (RPlusBound.restricted ρ
    (show A ∈ RPlusBound ρ (actionRatio ρ A) from ⟨⟨hA.2.1, le_rfl⟩, hA.2⟩) U hU hn).2
  have ha : actionRatio ρ A = r := le_antisymm hA.1.1.2 (heq ▸ hiA)
  refine ⟨hq, ha, heq, ?_⟩
  rcases RPlus.restriction_alternatives ρ hA.2 U hU hn with hi | h | h
  · exact (ne_of_lt hi (heq.trans ha.symm)).elim
  · exact Or.inl ⟨h.1, h.2.1, h.2.2.1⟩
  · exact Or.inr ⟨h.1, h.2.2.1.trans ha, h.2.2.2⟩

/-- D.2.7: a minimal global cubic actor has either strict decrease or faithful span. -/
theorem QhatStar.restriction_alternatives {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (U : Submodule (ZMod 2) V) (hU : A ≤ subspaceStabilizer ρ U)
    (hn : ¬ U ≤ fixedSpace ρ A) :
    A ∈ RIteratedPlus ρ 3 (cubicRatio ρ) ∧
    actionRatio ρ A = cubicRatio ρ ∧
    ((restrictedSubgroup ρ U A ∈ Qhat (subspaceImageRepresentation ρ U) ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) < cubicRatio ρ) ∨
      (subspaceKernel ρ U A = ⊥ ∧ U ⊔ fixedSpace ρ A = ⊤)) := by
  have hp := QhatStar.mem_RPlus ρ hA
  have hc := hA.1.2.2.1
  have he := hA.1.2.2.2
  refine ⟨⟨⟨⟨hp.1, he.le⟩, (iteratedCommutator_three_eq_bot_iff ρ A).mpr hc⟩, hp⟩, he, ?_⟩
  rcases RPlus.restriction_alternatives ρ hp U hU hn with hi | h | h
  · have hlt := hi.trans_eq he
    exact Or.inl ⟨⟨hp.1.restrictedSubgroup ρ U hU hn, isCubic_restrictedSubgroup ρ U hc,
      hlt.le.trans hA.1.1⟩, hlt⟩
  · exact Or.inr ⟨h.1, h.2.1⟩
  · have hlt := QhatStar.ratio_lt_of_lt ρ hA
      (lt_of_le_of_ne (subspaceKernel_le ρ U A) (subspaceKernel_ne_self ρ U hn)) h.1.1.1
    exact (ne_of_lt hlt h.2.2.1.symm).elim

/-- D.2.8: the lower bound on the new cubic minimum preserves starred minimality. -/
theorem QhatStar.restricted_of_le_minimum {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (U : Submodule (ZMod 2) V) (hU : A ≤ subspaceStabilizer ρ U)
    (hn : ¬ U ≤ fixedSpace ρ A)
    (hmin : cubicRatio ρ ≤ cubicRatio (subspaceImageRepresentation ρ U)) :
    cubicRatio (subspaceImageRepresentation ρ U) = cubicRatio ρ ∧
    subspaceKernel ρ U A = ⊥ ∧ U ⊔ fixedSpace ρ A = ⊤ ∧
    restrictedSubgroup ρ U A ∈ QhatStar (subspaceImageRepresentation ρ U) := by
  obtain ⟨_, he, hcases⟩ := QhatStar.restriction_alternatives ρ hA U hU hn
  have hI := hA.1.2.1.restrictedSubgroup ρ U hU hn
  have hIc := isCubic_restrictedSubgroup ρ U hA.1.2.2.1
  have hlow : cubicRatio (subspaceImageRepresentation ρ U) ≤
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨hI, hIc⟩ le_rfl)
  rcases hcases with ⟨_, hlt⟩ | ⟨hk, hs⟩
  · exact (not_lt_of_ge (hmin.trans hlow) hlt).elim
  · have hratio := actionRatio_restricted_subactor_eq ρ U hA.1.2.1 hU hk hs le_rfl
    have hq : cubicRatio (subspaceImageRepresentation ρ U) = cubicRatio ρ :=
      le_antisymm (hlow.trans_eq (hratio.trans he)) hmin
    refine ⟨hq, hk, hs, ⟨?_, ?_⟩⟩
    · exact ⟨hq ▸ hA.1.1, hI, hIc, hratio.trans (he.trans hq.symm)⟩
    · intro D hD hDA
      obtain ⟨B, hBA, _, hBD⟩ := exists_subgroup_restrictedSubgroup ρ U hU D hDA
      have hB : B ≠ ⊥ := by
        intro hb
        exact hD.2.1.1 (by rw [← hBD, hb, restrictedSubgroup_bot])
      have hrB : actionRatio ρ B = actionRatio ρ A := by
        rw [← actionRatio_restricted_subactor_eq ρ U hA.1.2.1 hU hk hs hBA,
          hBD, hD.2.2.2, hq, he]
      have hBeq : B = A := by
        by_contra hne
        exact (ne_of_lt (QhatStar.ratio_lt_of_lt ρ hA (lt_of_le_of_ne hBA hne) hB)) hrB.symm
      rw [← hBD, hBeq]

/-- D.2.7 on a noncentralized fixed space of a nontrivial subactor: only strict decrease remains. -/
theorem QhatStar.fixedSpace_ratio_drop {A B : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hBA : B ≤ A) (hB : B ≠ ⊥)
    (hn : subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥) :
    restrictedSubgroup ρ (fixedSpace ρ B) A ∈ Qhat
        (subspaceImageRepresentation ρ (fixedSpace ρ B)) ∧
      actionRatio (subspaceImageRepresentation ρ (fixedSpace ρ B))
        (restrictedSubgroup ρ (fixedSpace ρ B) A) < cubicRatio ρ := by
  have hn' : ¬ fixedSpace ρ B ≤ fixedSpace ρ A :=
    fun h => hn ((subspaceCommutator_eq_bot_iff _ _ _).mpr h)
  rcases (QhatStar.restriction_alternatives ρ hA (fixedSpace ρ B)
    (fixedSpace_subactor_stabilized ρ hA.1.2.1 hBA) hn').2.2 with h | ⟨hk, _⟩
  · exact h
  · exact (hB (le_bot_iff.mp ((subactor_le_fixedSpace_kernel ρ hBA).trans_eq hk))).elim

/-- The D.2.13 hyperplane application: the exact kernel, rank-one image and strict ratio drop. -/
theorem QhatStar.hyperplane_fixedSpace_ratio_drop {A B : Subgroup G}
    (hA : A ∈ QhatStar ρ) (hBA : B ≤ A) (hB : B ≠ ⊥)
    (hhyper : rank B + 1 = rank A)
    (hn : subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥) :
    subspaceKernel ρ (fixedSpace ρ B) A = B ∧
    rank (restrictedSubgroup ρ (fixedSpace ρ B) A) = 1 ∧
    restrictedSubgroup ρ (fixedSpace ρ B) A ∈ Qhat
        (subspaceImageRepresentation ρ (fixedSpace ρ B)) ∧
      actionRatio (subspaceImageRepresentation ρ (fixedSpace ρ B))
        (restrictedSubgroup ρ (fixedSpace ρ B) A) < cubicRatio ρ := by
  have hdrop := QhatStar.fixedSpace_ratio_drop ρ hA hBA hB hn
  have hstab := fixedSpace_subactor_stabilized ρ hA.1.2.1 hBA
  have hBK := subactor_le_fixedSpace_kernel ρ hBA
  have hBel := hA.1.2.1.of_le hBA hB
  have hKel := hA.1.2.1.of_le (subspaceKernel_le ρ (fixedSpace ρ B) A)
    (fun h => hB (le_bot_iff.mp (hBK.trans_eq h)))
  let _ : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hr := rank_subspaceKernel_add_image ρ (fixedSpace ρ B) A hstab
    (IsElementaryAbelian.isPGroup 2 A)
  have hIr := hdrop.1.1.rank_pos
  have hkr : rank (subspaceKernel ρ (fixedSpace ρ B) A) ≤ rank B := by omega
  have hkeq : subspaceKernel ρ (fixedSpace ρ B) A = B := by
    apply (Subgroup.eq_of_le_of_card_ge hBK ?_).symm
    rw [hKel.card_eq_two_pow_rank, hBel.card_eq_two_pow_rank]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hkr
  exact ⟨hkeq, by rw [hkeq] at hr; omega, hdrop⟩

/-- D.2.7 with the faithful finite source action and its commutator nontriviality hypothesis. -/
theorem source_lemma_D_2_7 (_hρ : Function.Injective ρ) {A : Subgroup G}
    (hA : A ∈ QhatStar ρ) (U : Submodule (ZMod 2) V)
    (hU : A ≤ subspaceStabilizer ρ U) (hn : subspaceCommutator ρ U A ≠ ⊥) :
    A ∈ RIteratedPlus ρ 3 (cubicRatio ρ) ∧ actionRatio ρ A = cubicRatio ρ ∧
    ((restrictedSubgroup ρ U A ∈ Qhat (subspaceImageRepresentation ρ U) ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) < cubicRatio ρ) ∨
      (Function.Injective (subgroupActionHom ρ U A hU) ∧ U ⊔ fixedSpace ρ A = ⊤)) := by
  obtain ⟨hp, heq, hcases⟩ := QhatStar.restriction_alternatives ρ hA U hU
    (fun h => hn ((subspaceCommutator_eq_bot_iff ρ U A).mpr h))
  refine ⟨hp, heq, ?_⟩
  rcases hcases with h | ⟨hk, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨(subgroupActionHom_injective_iff ρ U A hU).mpr hk, hs⟩

/-- D.2.8 on the actual faithful image, with no equality conclusion assumed. -/
theorem source_lemma_D_2_8 (_hρ : Function.Injective ρ) {A : Subgroup G}
    (hA : A ∈ QhatStar ρ) (U : Submodule (ZMod 2) V)
    (hU : A ≤ subspaceStabilizer ρ U) (hn : subspaceCommutator ρ U A ≠ ⊥)
    (hmin : cubicRatio ρ ≤ cubicRatio (subspaceImageRepresentation ρ U)) :
    cubicRatio (subspaceImageRepresentation ρ U) = cubicRatio ρ ∧
    Function.Injective (subgroupActionHom ρ U A hU) ∧ U ⊔ fixedSpace ρ A = ⊤ ∧
    restrictedSubgroup ρ U A ∈ QhatStar (subspaceImageRepresentation ρ U) := by
  obtain ⟨hq, hk, hs, hstar⟩ := QhatStar.restricted_of_le_minimum ρ hA U hU
    (fun h => hn ((subspaceCommutator_eq_bot_iff ρ U A).mpr h)) hmin
  exact ⟨hq, (subgroupActionHom_injective_iff ρ U A hU).mpr hk, hs, hstar⟩

end CFSG.Quasithin.ChapterD
