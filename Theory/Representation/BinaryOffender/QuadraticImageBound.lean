module
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Lower quadratic-ratio bounds on actual action quotients

The image of an elementary actor has order exactly its index over its
pointwise kernel. A nontrivial quadratic image makes the global ratio finite;
a lower bound on that ratio gives the corresponding fixed-codimension bound.
This is the local estimate used on conjugate generators and noncentral chief
factors in Aschbacher--Smith, D.1.3(b), (c), and (n), printed pp.173--175.
-/

@[expose] public section
namespace Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- The linear action and its faithful image have exactly the same kernel. -/
theorem actionHom_ker_eq : (actionHom ρ).ker = ρ.ker := by
  ext g
  change actionHom ρ g = 1 ↔ ρ g = 1
  rw [actionHom_eq_one_iff]
  exact ⟨fun h => LinearMap.ext h, fun h v => LinearMap.congr_fun h v⟩

omit [Finite G] in
/-- The rank of the image is the rank of the literal quotient by the
relative action kernel, expressed as a relative index. -/
theorem rank_actionSubgroup_eq_log_relIndex (A : Subgroup G) :
    rank (actionSubgroup ρ A) = Nat.log 2 (ρ.ker.relIndex A) := by
  rw [rank, actionSubgroup, ← Subgroup.relIndex_ker, actionHom_ker_eq]

omit [Finite G] in
/-- Quadraticity passes to the faithful image of the same actor. -/
theorem quadratic_actionSubgroup {A : Subgroup G} (hA : IsQuadratic ρ A) :
    IsQuadratic (imageRepresentation ρ) (actionSubgroup ρ A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  exact hA a ha b hb v

omit [Finite G] in
/-- Nontriviality here is nontriviality of the action, not merely of the group. -/
theorem elementary_actionSubgroup {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : ¬ A ≤ ρ.ker) : IsElementaryTwo (actionSubgroup ρ A) := by
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro hbot
  apply hA
  rw [← actionHom_ker_eq]
  exact (Subgroup.map_eq_bot_iff A).mp hbot

/-- A genuine nontrivial quadratic action excludes the infinite global ratio. -/
theorem quadraticRatio_image_ne_top {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : ¬ A ≤ ρ.ker) (hquad : IsQuadratic ρ A) :
    quadraticRatio (imageRepresentation ρ) ≠ ⊤ := by
  have he := elementary_actionSubgroup ρ hA
  have hr : (rank (actionSubgroup ρ A) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt he.rank_pos)
  have hfinite : actionRatio (imageRepresentation ρ) (actionSubgroup ρ A) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) hr
  exact ne_top_of_le_ne_top hfinite
    (iInf_le_of_le _ (iInf_le_of_le ⟨he, quadratic_actionSubgroup ρ hquad⟩ le_rfl))

/-- The source local rank inequality, also valid for trivial action. -/
theorem quadratic_image_rank_bound {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hquad : IsQuadratic ρ A) {q : ℝ≥0∞}
    (hq : q ≤ quadraticRatio (imageRepresentation ρ)) :
    q * (Nat.log 2 (ρ.ker.relIndex A) : ℝ≥0∞) ≤ fixedCodim ρ A := by
  rw [← rank_actionSubgroup_eq_log_relIndex]
  by_cases hA : A ≤ ρ.ker
  · have hb : actionSubgroup ρ A = ⊥ := by
      apply (Subgroup.map_eq_bot_iff A).mpr
      rwa [actionHom_ker_eq]
    simp [hb, rank_bot]
  · have he := elementary_actionSubgroup ρ hA
    have hr : (rank (actionSubgroup ρ A) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt he.rank_pos)
    have hbound : q ≤ actionRatio (imageRepresentation ρ) (actionSubgroup ρ A) :=
      hq.trans (iInf_le_of_le _
        (iInf_le_of_le ⟨he, quadratic_actionSubgroup ρ hquad⟩ le_rfl))
    rw [actionRatio, fixedCodim_actionSubgroup] at hbound
    exact (ENNReal.le_div_iff_mul_le (Or.inl hr) (Or.inl (by simp))).mp hbound

/-- With lower ratio one the bound is an inequality of natural ranks. -/
theorem quadratic_image_rank_le {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hquad : IsQuadratic ρ A)
    (hq : 1 ≤ quadraticRatio (imageRepresentation ρ)) :
    Nat.log 2 (ρ.ker.relIndex A) ≤ fixedCodim ρ A := by
  have h := quadratic_image_rank_bound ρ hquad hq
  simpa using h

/-- Conversion to real ranks is made only after a finite ratio is established. -/
theorem quadratic_image_rank_bound_real {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hquad : IsQuadratic ρ A) {q : ℝ≥0∞} (hfinite : q ≠ ⊤)
    (hq : q ≤ quadraticRatio (imageRepresentation ρ)) :
    q.toReal * (Nat.log 2 (ρ.ker.relIndex A) : ℝ) ≤ fixedCodim ρ A := by
  have h := quadratic_image_rank_bound ρ hquad hq
  have hm : q * (Nat.log 2 (ρ.ker.relIndex A) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top hfinite (by simp)
  have hr := (ENNReal.toReal_le_toReal hm (by simp)).mpr h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hr

end Representation.BinaryOffender
