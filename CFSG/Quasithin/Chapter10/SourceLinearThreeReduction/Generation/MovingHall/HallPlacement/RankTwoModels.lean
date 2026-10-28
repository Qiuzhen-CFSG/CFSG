module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.TwoPerfectSylowAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSupplement
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSupplement
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer

/-!
# The marked local-component pairs in the three rank-two FF models

For SL₃, PSL₃, Sp₄ and G₂ over a nonbinary even field, the original full Sylow
has at most two proper local C-components. Perfectness places each in a
parabolic residual; the actual SL₂ core quotient forces equality with
that residual. Sylow-aligned model equivalences retain this same pair.
Central covers retain this pair by perfect-subgroup recovery from projective
images, including the order-three center of SL₃. The solvable Sylow control and the two-perfect pair argument
therefore fix each local component under the Borel actor.

This proves the three model calculations used in case (b) of the Borel
claim in Aschbacher–Smith 10.2.3, printed p.746. It does not assert that
every comparison belongs to this case; the source model sieve remains
with the moving-Hall assembly owner.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory ChapterA.Section03
open scoped Pointwise
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

/-- Transport a fixed-Sylow pair, retaining the literal local-component condition. -/
theorem local_pair_of_standard (e : X ≃* Y) (S : Sylow 2 X) (U : Sylow 2 Y)
    (P Q : Subgroup Y)
    (hpair : ∀ K : Subgroup Y, K ∈ localCComponents U → K ≠ ⊤ → K = P ∨ K = Q) :
    ∃ P Q : Subgroup X, ∀ K : Subgroup X,
      K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv e S U
  refine ⟨P.comap a.toMonoidHom,Q.comap a.toMonoidHom,?_⟩
  intro K hl hp
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl a.toMonoidHom
  rw [hS] at hl'
  have hp' : K.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  rcases hpair _ hl' hp' with he | he
  · left
    have hh := congrArg (comap a.toMonoidHom) he
    rwa [comap_map_eq_self_of_injective a.injective] at hh
  · right
    have hh := congrArg (comap a.toMonoidHom) he
    rwa [comap_map_eq_self_of_injective a.injective] at hh

/-- Two-perfect actors fixing the full Sylow fix each member of its local pair. -/
theorem twoPerfect_fixes_local_pair
    {A : Type*} [Group A] [Finite A] (a : A →* MulAut X) (hA : IsPPerfect 2 A)
    (S : Sylow 2 X) (hS : ∀ g : A, (S : Subgroup X).map (a g).toMonoidHom = S)
    (hpair : ∃ P Q : Subgroup X, ∀ K : Subgroup X,
      K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q)
    (K : Subgroup X) (hl : K ∈ localCComponents S) :
    ∀ g : A, K.map (a g).toMonoidHom = K := by
  by_cases hp : K = ⊤
  · subst K
    exact fun g => map_top_of_surjective _ (a g).surjective
  obtain ⟨P,Q,hpair⟩ := hpair
  have hi (g : A) : K.map (a g).toMonoidHom = P ∨ K.map (a g).toMonoidHom = Q := by
    let : Group.IsSolvable (a g).toMonoidHom.ker := by
      rw [(a g).toMonoidHom.ker_eq_bot_iff.mpr (a g).injective]
      infer_instance
    have hloc := Chapter1.Section02.localCComponents_map_of_solvable_ker hl (a g).toMonoidHom
    rw [hS g] at hloc
    apply hpair _ hloc
    intro he
    apply hp
    apply map_injective (f := (a g).toMonoidHom) (a g).injective
    rw [he,map_top_of_surjective _ (a g).surjective]
  let : MulAction A (Subgroup X) := MulAction.compHom (Subgroup X) a
  rcases hpair K hl hp with he | he
  · apply twoPerfect_fixes_pair hA K Q
    intro g
    change K.map (a g).toMonoidHom = K ∨ K.map (a g).toMonoidHom = Q
    simpa only [he] using hi g
  · apply twoPerfect_fixes_pair hA K P
    intro g
    change K.map (a g).toMonoidHom = K ∨ K.map (a g).toMonoidHom = P
    simpa only [he] using (hi g).symm
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

public noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual standard full-Sylow local components are precisely the two
parabolic residuals. The original Sylow is retained, not merely conjugate. -/
theorem linear_three_standard_local {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (K : Subgroup PSL(3,F)) (hl : K ∈ localCComponents (unipotent F))
    (hp : K ≠ ⊤) : K = pointLocal F ∨ K = lineLocal F := by
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let := hl.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ unipotent F from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hjoin : K ⊔ unipotent F ≠ ⊤ := by
    intro ht
    have hc : K.IsCComponent := by
      have hm := hl
      change (K.subgroupOf (K ⊔ unipotent F)).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hp
  rcases UnipotentOvergroups.overgroup_unipotent F _ (show unipotent F ≤ K ⊔ unipotent F from le_sup_right) hjoin with hP | hP
  · left
    let := pointLocal_isPerfect F hlarge
    apply local_eq_of_sl2_core_quotient (pointLocal F) (by omega)
      (pointLocalCoreQuotientEquiv F) (unipotentSylow F (by omega) hF) K hl
    · rw [←ParabolicResiduals.pointParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact unipotent_le_pointLocal F
  · right
    let := lineLocal_isPerfect F hlarge
    apply local_eq_of_sl2_core_quotient (lineLocal F) (by omega)
      (lineLocalCoreQuotientEquiv F) (unipotentSylow F (by omega) hF) K hl
    · rw [←ParabolicResiduals.lineParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact unipotent_le_lineLocal F
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF

private theorem sylow_le_determinant_kernel
    {F : Type*} [Field F] [CharP F 2]
    (W : Submodule F (Theory.SpecificGroups.SymplecticFour.Vector F))
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hS : (S : Subgroup _) ≤ Theory.SpecificGroups.SymplecticFour.stabilizer W) :
    (S : Subgroup _) ≤ Theory.SpecificGroups.SymplecticFour.determinantKernel W := by
  open Theory.SpecificGroups.SymplecticFour in
  intro t ht
  let x : stabilizer W := ⟨t,hS ht⟩
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨t,ht⟩
  have hx : x ^ (2^n) = 1 := Subtype.ext (congrArg (fun y : S => (y : Sp F)) hn)
  have hp : ((determinantCharacter W x : Fˣ) : F) ^ (2^n) = 1 := by
    have he := congrArg (fun u : Fˣ => (u:F)) (congrArg (determinantCharacter W) hx)
    simpa only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] using he
  have hc : determinantCharacter W x = 1 := by
    apply Units.ext
    exact (iterateFrobenius_inj F 2 n) (by simpa [iterateFrobenius_def] using hp)
  exact ⟨x,hc,rfl⟩

/-- The marked symplectic Sylow has precisely its point and plane local components. -/
theorem symplectic_standard_local
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (K : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hl : K ∈ localCComponents (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)))
    (hp : K ≠ ⊤) : K = Theory.SpecificGroups.SymplecticFour.pointLocal ∨
      K = Theory.SpecificGroups.SymplecticFour.planeLocal := by
  open Theory.SpecificGroups.SymplecticFour in
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  let := SimpleQuotients.isSimpleGroup_of_card_eq_two_pow (by omega : 2 ≤ n) hF
  let : IsSimpleGroup (Sp F) := EvenProjective.equiv.isSimpleGroup
  let := hl.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ unipotent from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hjoin : K ⊔ unipotent ≠ ⊤ := by
    intro ht
    have hc : K.IsCComponent := by
      have hh := hl
      change (K.subgroupOf (K ⊔ unipotent)).IsCComponent at hh
      rw [ht] at hh
      simpa only [map_subgroupOf_eq_of_le le_top] using hh.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hp
  rcases TwoConjugate.proper_unipotent_overgroup_le_parabolic hF hn.le
      (K ⊔ unipotent) le_sup_right hjoin with hP | hP
  · left
    let := pointLocal_perfect hF hn
    apply local_eq_of_sl2_core_quotient pointLocal hlarge
      (pointLocalCoreQuotientEquiv hF hn) (unipotentSylow hF hn.le) K hl
    · rw [←pointParabolic_solvableResidual_eq hF hn]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact sylow_le_determinant_kernel (point F) (unipotentSylow hF hn.le)
        (le_sup_right.trans hP)
  · right
    let := planeLocal_perfect hF hn
    apply local_eq_of_sl2_core_quotient planeLocal hlarge
      (planeLocalCoreQuotientEquiv hF hn) (unipotentSylow hF hn.le) K hl
    · rw [←planeParabolic_solvableResidual_eq hF hn]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact sylow_le_determinant_kernel (plane F) (unipotentSylow hF hn.le)
        (le_sup_right.trans hP)

/-- The marked G₂ Sylow has precisely its two root-parabolic residuals. -/
theorem g2_standard_local
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (K : Subgroup (Atlas.G2.Model F))
    (hl : K ∈ localCComponents (Atlas.G2.unipotent (K := F))) (hp : K ≠ ⊤) :
    K = Atlas.G2.LieParabolicSetup.local₁ ∨ K = Atlas.G2.LieParabolicSetup.local₂ := by
  open Atlas.G2 Atlas.G2.LieParabolicSetup in
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hq
  let := hl.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ unipotent from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hjoin : K ⊔ unipotent ≠ ⊤ := by
    intro ht
    have hc : K.IsCComponent := by
      have hh := hl
      change (K.subgroupOf (K ⊔ unipotent)).IsCComponent at hh
      rw [ht] at hh
      simpa only [map_subgroupOf_eq_of_le le_top] using hh.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hp
  rcases ProperSylowOvergroups.le_parabolic (K ⊔ unipotent) le_sup_right
      (lt_top_iff_ne_top.mpr hjoin) with hP | hP
  · left
    let := local₁_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₁ hq
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) (sylow (F := F)) K hl
    · rw [←HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact unipotent_le_local₁
  · right
    let := local₂_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₂ hq
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) (sylow (F := F)) K hl
    · rw [←HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hP)
    · exact unipotent_le_local₂
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory ChapterA.Section03 Matrix.PSL3.LinearThree
open scoped MatrixGroups
variable {X : Type*} [Group X] [Finite X]

/-- The actual PSL₃ marking retains the two local components of the supplied Sylow. -/
theorem linear_three_local_pair (S : Sylow 2 X) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL X 3 (2^n)) :
    ∃ P Q : Subgroup X, ∀ K : Subgroup X,
      K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact local_pair_of_standard e S (unipotentSylow F (by omega) hF) _ _
    (linear_three_standard_local hF hn)
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory ChapterA.Section03
open scoped MatrixGroups
variable {X Y : Type*} [Group X] [Finite X] [Group Y]

/-- The local pair lifts through a central cover by recovering each original
perfect subgroup from the full preimage of its image. -/
theorem local_pair_of_central_cover [Group.IsPerfect X]
    (f : X →* Y) (hf : Function.Surjective f) (hk : f.ker ≤ center X)
    (hpair : ∀ S : Sylow 2 Y, ∃ P Q : Subgroup Y, ∀ K : Subgroup Y,
      K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q)
    (S : Sylow 2 X) :
    ∃ P Q : Subgroup X, ∀ K : Subgroup X,
      K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  obtain ⟨P,Q,hpair⟩ := hpair (S.mapSurjective hf)
  let lift (P : Subgroup Y) := (solvableResidual (P.comap f)).map (P.comap f).subtype
  refine ⟨lift P,lift Q,?_⟩
  intro K hl hp
  let := hl.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (S : Subgroup X) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsSolvable (center X) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  have hp' : K.map f ≠ ⊤ := by
    intro ht
    apply hp
    apply top_unique
    exact perfect_le_of_map_le_of_central_kernel f hk ⊤ K (by rw [ht]; exact le_top)
  have he : K = lift (K.map f) := perfect_eq_residual_preimage f hk K
  rcases hpair _ hl' hp' with hP | hQ
  · exact Or.inl (he.trans (congrArg lift hP))
  · exact Or.inr (he.trans (congrArg lift hQ))

/-- Full SL₃ covers supply the same literal local-pair geometry as PSL₃,
including when the scalar center has order three. -/
theorem special_linear_three_geometry {m : ℕ} (hm : 1 < m)
    (hmodel : Chapter1.Section02.LocalModels.IsSL X 3 (2^m)) :
    SolvableSylowControl 2 X ∧ ∀ S : Sylow 2 X,
      ∃ P Q : Subgroup X, ∀ K : Subgroup X,
        K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
  have hf : Function.Surjective f := (Matrix.PSL3.projection_surjective F).comp e.surjective
  have hk : f.ker ≤ center X := by
    intro x hx
    have hz : e x ∈ center SL(3,F) := by
      rw [← Matrix.PSL3.projection_ker]
      exact hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hz (e y)
  have hs : ClassicalGroup.IsPSL PSL(3,F) 3 (2^m) := ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨SolvableSylowControl.of_surjective_central_kernel f hf hk ?_,
    local_pair_of_central_cover f hf hk (fun S => linear_three_local_pair S hm hs)⟩
  exact Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F (by omega) hF
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory ChapterA.Section03
open scoped MatrixGroups
variable {X : Type*} [Group X] [Finite X]

/-- The three FF rank-two rows, with actual quotient identifications. -/
def ComparisonRankTwo (X : Type*) [Group X] : Prop :=
  ∃ m : ℕ, 1 < m ∧ (ClassicalGroup.IsPSL X 3 (2^m) ∨
    Chapter1.Section02.LocalModels.IsSL X 3 (2^m) ∨
    ClassicalGroup.IsPSp X 2 (2^m) ∨ ClassificationModels.IsG2At X (2^m))

omit [Finite X] in
/-- Construct the rank-two case from an actual special-linear marking. -/
theorem ComparisonRankTwo.of_special_linear {m : ℕ} (hm : 1 < m)
    (h : Chapter1.Section02.LocalModels.IsSL X 3 (2^m)) : ComparisonRankTwo X :=
  ⟨m,hm,Or.inr (Or.inl h)⟩

omit [Finite X] in
/-- Construct the rank-two case from an actual projective symplectic marking. -/
theorem ComparisonRankTwo.of_symplectic {m : ℕ} (hm : 1 < m)
    (h : ClassicalGroup.IsPSp X 2 (2^m)) : ComparisonRankTwo X :=
  ⟨m,hm,Or.inr (Or.inr (Or.inl h))⟩

omit [Finite X] in
/-- Construct the rank-two case from an actual G₂ marking. -/
theorem ComparisonRankTwo.of_g2 {m : ℕ} (hm : 1 < m)
    (h : ClassificationModels.IsG2At X (2^m)) : ComparisonRankTwo X :=
  ⟨m,hm,Or.inr (Or.inr (Or.inr h))⟩

/-- All three actual rank-two models supply solvable Sylow control and
at most two proper local components for each marked Sylow. -/
theorem comparison_rank_two_geometry (h : ComparisonRankTwo X) :
    SolvableSylowControl 2 X ∧ ∀ S : Sylow 2 X,
      ∃ P Q : Subgroup X, ∀ K : Subgroup X,
        K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  obtain ⟨m,hm,hmodel⟩ := h
  rcases hmodel with hlinear | hspecial | hsymplectic | hg2
  · refine ⟨?_,fun S => linear_three_local_pair S hm hlinear⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hlinear
    exact SolvableSylowControl.of_equiv e
      (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
        F (by omega) hF)
  · exact special_linear_three_geometry hm hspecial
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hsymplectic
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2:ℕ)^1 < 2^m from Nat.pow_lt_pow_right (by decide) hm)
    refine ⟨SolvableSylowControl.of_equiv a ?_,?_⟩
    · exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits
        hF hm (fun J hs hu =>
          Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal
            hlarge J hs hu)
    · intro S
      exact local_pair_of_standard a S
        (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hm.le) _ _
        (symplectic_standard_local hF hm)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hg2
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2:ℕ)^1 < 2^m from Nat.pow_lt_pow_right (by decide) hm)
    refine ⟨SolvableSylowControl.of_equiv e ?_,?_⟩
    · exact fun S J hs hSJ => Atlas.G2.solvable_sylow_overgroup_normalizes hlarge S J hSJ hs
    · intro S
      exact local_pair_of_standard e S (Atlas.G2.LieParabolicSetup.sylow (F := F)) _ _
        (g2_standard_local hlarge)
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
