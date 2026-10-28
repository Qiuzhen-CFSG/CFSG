module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Restriction of action ratios

The pointwise kernel `B = C_A(U)` and the faithful image on `U` split the
binary rank of `A`. The dimension balance for `C_V(A) ≤ C_V(B)` then gives
a strict decrease in one of the two ratios, or equality and the exact
fixed-space sum. If the kernel is trivial, equality detects `V = U + C_V(A)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.2–D.2.4,
printed pp.178–179. Equality alternatives use the exact ratio of `A`;
an arbitrary upper bound cannot replace that ratio in the equalities.
-/

public section
namespace Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)

omit [FiniteDimensional (ZMod 2) V] in
/-- An elementary nontrivial actor has a finite action ratio. -/
theorem actionRatio_ne_top {A : Subgroup G} (hA : IsElementaryTwo A) :
    actionRatio ρ A ≠ ⊤ := by
  apply ENNReal.div_ne_top (by simp)
  exact_mod_cast (Nat.ne_of_gt hA.rank_pos)

omit [Finite G] in
/-- The numerator on the actual image is `dim U - dim (U ∩ C_V(A))`. -/
theorem fixedCodim_restrictedSubgroup (A : Subgroup G)
    (hU : A ≤ subspaceStabilizer ρ U) :
    fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
      Module.finrank (ZMod 2) U -
        Module.finrank (ZMod 2) (U ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) := by
  have h := fixedCodim_add_finrank (subspaceImageRepresentation ρ U)
    (restrictedSubgroup ρ U A)
  have he := (restrictedFixedSpaceEquiv ρ U A hU).finrank_eq
  omega

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The source fixed-space containment for the actual pointwise kernel. -/
theorem sup_fixedSpace_le_kernel_fixedSpace (A : Subgroup G) :
    U ⊔ fixedSpace ρ A ≤ fixedSpace ρ (subspaceKernel ρ U A) :=
  sup_le (le_fixedSpace_subspaceKernel ρ U A)
    (fixedSpace_antitone ρ (subspaceKernel_le ρ U A))

omit [Finite G] in
/-- The numerator balance underlying inheritance, on the literal action image. -/
theorem fixedCodim_kernel_add_restricted_le (A : Subgroup G)
    (hU : A ≤ subspaceStabilizer ρ U) :
    fixedCodim ρ (subspaceKernel ρ U A) +
      fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) ≤
        fixedCodim ρ A := by
  rw [fixedCodim_restrictedSubgroup ρ U A hU]
  exact Submodule.quotient_finrank_add_relative_le U (fixedSpace ρ A)
    (fixedSpace ρ (subspaceKernel ρ U A)) (sup_fixedSpace_le_kernel_fixedSpace ρ U A)

omit [Finite G] in
/-- Equality of the numerator balance is exactly the source fixed-space sum. -/
theorem fixedCodim_kernel_add_restricted_eq_iff (A : Subgroup G)
    (hU : A ≤ subspaceStabilizer ρ U) :
    fixedCodim ρ (subspaceKernel ρ U A) +
      fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
        fixedCodim ρ A ↔ U ⊔ fixedSpace ρ A = fixedSpace ρ (subspaceKernel ρ U A) := by
  rw [fixedCodim_restrictedSubgroup ρ U A hU]
  exact Submodule.quotient_finrank_add_relative_eq_iff U (fixedSpace ρ A)
    (fixedSpace ρ (subspaceKernel ρ U A)) (sup_fixedSpace_le_kernel_fixedSpace ρ U A)

/-- The exact-ratio version of D.2.2, including the faithful-kernel case. -/
theorem actionRatio_restriction_alternatives {A : Subgroup G} (hA : IsElementaryTwo A)
    (hU : A ≤ subspaceStabilizer ρ U) (hn : ¬ U ≤ fixedSpace ρ A) :
    actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) <
        actionRatio ρ A ∨
    (IsElementaryTwo (subspaceKernel ρ U A) ∧
      actionRatio ρ (subspaceKernel ρ U A) < actionRatio ρ A) ∨
    (subspaceKernel ρ U A = ⊥ ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
        actionRatio ρ A ∧ U ⊔ fixedSpace ρ A = ⊤) ∨
    (IsElementaryTwo (subspaceKernel ρ U A) ∧
      actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
        actionRatio ρ A ∧
      actionRatio ρ (subspaceKernel ρ U A) = actionRatio ρ A ∧
      U ⊔ fixedSpace ρ A = fixedSpace ρ (subspaceKernel ρ U A)) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have hI := hA.restrictedSubgroup ρ U hU hn
  have hr := rank_subspaceKernel_add_image ρ U A hU (IsElementaryAbelian.isPGroup 2 A)
  have hbalance := fixedCodim_kernel_add_restricted_le ρ U A hU
  by_cases hB : subspaceKernel ρ U A = ⊥
  · have hrI : rank (restrictedSubgroup ρ U A) = rank A := by
      simpa only [hB, rank_bot, zero_add] using hr
    have hz : fixedCodim ρ (subspaceKernel ρ U A) = 0 := by
      rw [hB, fixedCodim, fixedSpace_bot]
      exact Module.finrank_zero_of_subsingleton
    by_cases hlt : fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) <
        fixedCodim ρ A
    · left
      simp only [actionRatio, hrI]
      apply (ENNReal.div_lt_div_iff_left (by exact_mod_cast (Nat.ne_of_gt hA.rank_pos))
        (by simp)).mpr
      exact_mod_cast hlt
    · have heq : fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
          fixedCodim ρ A := by omega
      refine Or.inr (Or.inr (Or.inl ⟨hB, ?_, ?_⟩))
      · simp only [actionRatio, heq, hrI]
      · have hsum := (fixedCodim_kernel_add_restricted_eq_iff ρ U A hU).mp
          (by rw [hz, zero_add, heq])
        simpa only [hB, fixedSpace_bot] using hsum
  · have hBel := hA.of_le (subspaceKernel_le ρ U A) hB
    have hbr : (0 : ℝ) < rank (subspaceKernel ρ U A) := by exact_mod_cast hBel.rank_pos
    have hir : (0 : ℝ) < rank (restrictedSubgroup ρ U A) := by exact_mod_cast hI.rank_pos
    have ht := Submodule.restriction_ratio_alternative U (fixedSpace ρ A)
      (fixedSpace ρ (subspaceKernel ρ U A))
      (sup_fixedSpace_le_kernel_fixedSpace ρ U A) hbr hir
    have hrR : (rank A : ℝ) =
        (rank (subspaceKernel ρ U A) : ℝ) + rank (restrictedSubgroup ρ U A) := by
      exact_mod_cast hr.symm
    have hiR : (actionRatio (subspaceImageRepresentation ρ U)
        (restrictedSubgroup ρ U A)).toReal =
        (Module.finrank (ZMod 2) U -
          Module.finrank (ZMod 2) (U ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) : ℕ) /
          (rank (restrictedSubgroup ρ U A) : ℝ) := by
      simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast,
        fixedCodim_restrictedSubgroup ρ U A hU]
    have haR : (actionRatio ρ A).toReal =
        (Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ A) : ℝ) /
          ((rank (subspaceKernel ρ U A) : ℝ) + rank (restrictedSubgroup ρ U A)) := by
      simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast, hrR, fixedCodim]
    have hbR : (actionRatio ρ (subspaceKernel ρ U A)).toReal =
        (Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ (subspaceKernel ρ U A)) : ℝ) /
          rank (subspaceKernel ρ U A) := by
      simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast, fixedCodim]
    rcases ht with hi | hb | ⟨hi, hb, hs⟩
    · exact Or.inl ((ENNReal.toReal_lt_toReal
        (actionRatio_ne_top _ hI) (actionRatio_ne_top ρ hA)).mp (by rwa [hiR, haR]))
    · exact Or.inr (Or.inl ⟨hBel, (ENNReal.toReal_lt_toReal
        (actionRatio_ne_top ρ hBel) (actionRatio_ne_top ρ hA)).mp (by rwa [hbR, haR])⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hBel,
        (ENNReal.toReal_eq_toReal_iff' (actionRatio_ne_top _ hI)
          (actionRatio_ne_top ρ hA)).mp (by rwa [hiR, haR]),
        (ENNReal.toReal_eq_toReal_iff' (actionRatio_ne_top ρ hBel)
          (actionRatio_ne_top ρ hA)).mp (by rwa [hbR, haR]), hs⟩))

omit [Finite G] in
/-- If a subspace spans with the fixed space, restriction preserves the numerator. -/
theorem fixedCodim_restricted_eq_of_sup {A : Subgroup G}
    (hU : A ≤ subspaceStabilizer ρ U) (hs : U ⊔ fixedSpace ρ A = ⊤) :
    fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) =
      fixedCodim ρ A := by
  rw [fixedCodim_restrictedSubgroup ρ U A hU]
  have h := (Submodule.quotient_finrank_add_relative_eq_iff U (fixedSpace ρ A) ⊤ le_top).mpr hs
  simpa only [Module.finrank_zero_of_subsingleton, zero_add, fixedCodim] using h

omit [Finite G] in
/-- All subactors have the same numerator after a faithful spanning restriction. -/
theorem fixedCodim_restricted_subactor_eq {A D : Subgroup G}
    (hU : A ≤ subspaceStabilizer ρ U) (hs : U ⊔ fixedSpace ρ A = ⊤) (hDA : D ≤ A) :
    fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U D) =
      fixedCodim ρ D := by
  apply fixedCodim_restricted_eq_of_sup ρ U (hDA.trans hU)
  exact top_unique (hs ▸ sup_le_sup_left (fixedSpace_antitone ρ hDA) U)

/-- With trivial kernel, every subactor has the same action ratio after restriction. -/
theorem actionRatio_restricted_subactor_eq {A D : Subgroup G}
    (hA : IsElementaryTwo A) (hU : A ≤ subspaceStabilizer ρ U)
    (hk : subspaceKernel ρ U A = ⊥) (hs : U ⊔ fixedSpace ρ A = ⊤) (hDA : D ≤ A) :
    actionRatio (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U D) =
      actionRatio ρ D := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have hpD := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (Subgroup.inclusion hDA) (Subgroup.inclusion_injective hDA)
  have hKD : subspaceKernel ρ U D = ⊥ := by
    apply le_bot_iff.mp
    intro d hd
    exact hk.le ⟨hDA hd.1, hd.2⟩
  have hr := rank_subspaceKernel_add_image ρ U D (hDA.trans hU) hpD
  simp only [hKD, rank_bot, zero_add] at hr
  simp only [actionRatio, fixedCodim_restricted_subactor_eq ρ U hU hs hDA, hr]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Every subactor fixed space is invariant under an elementary abelian actor. -/
theorem fixedSpace_subactor_stabilized {A B : Subgroup G} (hA : IsElementaryTwo A)
    (hBA : B ≤ A) : A ≤ subspaceStabilizer ρ (fixedSpace ρ B) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply le_subspaceStabilizer
  intro a ha v hv b
  have hcomm : (b : G) * a = a * b := by
    exact congrArg (fun x : A => (x : G))
      ((IsMulCommutative.is_comm (M := A)).comm ⟨b, hBA b.property⟩ ⟨a, ha⟩)
  change ρ b (ρ a v) = ρ a v
  calc
    _ = ρ a (ρ b v) := by
      simpa only [map_mul, Module.End.mul_apply] using congrArg (fun g => ρ g v) hcomm
    _ = ρ a v := congrArg (ρ a) (hv b)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A subactor lies in the pointwise kernel on its own fixed space. -/
theorem subactor_le_fixedSpace_kernel {A B : Subgroup G} (hBA : B ≤ A) :
    B ≤ subspaceKernel ρ (fixedSpace ρ B) A := by
  intro b hb
  exact ⟨hBA hb, fun v hv => hv ⟨b, hb⟩⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The literal restricted action is faithful exactly when its pointwise kernel is trivial. -/
theorem subgroupActionHom_injective_iff (A : Subgroup G)
    (hU : A ≤ subspaceStabilizer ρ U) :
    Function.Injective (subgroupActionHom ρ U A hU) ↔ subspaceKernel ρ U A = ⊥ := by
  constructor
  · intro hi
    rw [← subgroupActionHom_ker ρ U A hU,
      (subgroupActionHom ρ U A hU).ker_eq_bot_iff.mpr hi, Subgroup.map_bot]
  · intro hk
    apply (subgroupActionHom ρ U A hU).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    have ham : (a : G) ∈ subspaceKernel ρ U A :=
      (subgroupActionHom_ker ρ U A hU).le ⟨a, ha, rfl⟩
    rw [hk, Subgroup.mem_bot] at ham
    exact Subtype.ext ham

end Representation.BinaryOffender
