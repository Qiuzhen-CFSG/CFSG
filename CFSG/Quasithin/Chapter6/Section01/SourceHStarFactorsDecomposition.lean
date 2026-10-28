module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFactors
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The genuine product rows in the H-star Thompson image

Both product alternatives of B.5.6 have at most two literal factors, each
isomorphic to S3 or with quasisimple generalized Fitting subgroup. The
hyperplane alternative changes the module decomposition, but not this group
conclusion: its first factor is SL3(2), and its second is SL3(2) or SL2(2^m).
Their proper normal quotients are two-groups and their centers are trivial,
so the intrinsic product-coordinate argument permutes them under every
automorphism. This applies to conjugation on the actual normal Thompson
image of the 6.1.5 overgroup.

The outer A6--C3 alternative is deliberately retained. This file does not
derive its exclusion or infer a direct product from that outer shape.
Source: Aschbacher--Smith B.5.6(3),(5), p.105, and 6.1.5, pp.667--668.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource

private theorem simple_perfect_center {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : center A = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance).resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))

private theorem simple_perfect_fitting {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : IsQuasisimple (generalizedFitting A) := by
  let : IsQuasisimple A := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq simple_perfect_center).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  exact generalizedFitting_isQuasisimple_of_quasisimple

private theorem linear_three_simple_perfect {A : Type*} [Group A]
    (e : A ≃* SL(3, BinaryField.two.Carrier)) :
    IsSimpleGroup A ∧ Group.IsPerfect A := by
  let : IsSimpleGroup PSL(3, BinaryField.two.Carrier) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect SL(3, BinaryField.two.Carrier) := Atlas.sl_perfect 3 (by decide)
  exact ⟨(e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
    BinaryField.two.card_eq (by decide))).isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

private theorem linear_two_models (F : BinaryField) {A : Type*} [Group A]
    (e : A ≃* SL(2, F.Carrier)) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨ (IsSimpleGroup A ∧ Group.IsPerfect A) := by
  by_cases hd : F.degree = 1
  · exact Or.inl ⟨e.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))⟩
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup PSL(2, F.Carrier) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : Group.IsPerfect SL(2, F.Carrier) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
    exact Or.inr ⟨(e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

private theorem normal_quotient_two_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (hB : ∀ (N : Subgroup B) [N.Normal], N ≠ ⊥ → IsPGroup 2 (B ⧸ N))
    (N : Subgroup A) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (A ⧸ N) := by
  let M := N.map e.toMonoidHom
  let : M.Normal := (inferInstance : N.Normal).map _ e.surjective
  have hm : M ≠ ⊥ := by
    intro hb
    apply hn
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hb
  exact (hB M hm).of_equiv (QuotientGroup.congr N M e rfl).symm

private theorem center_eq_bot_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := hz.le (by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z))
  exact e.injective (he.trans e.map_one.symm)

variable {D V : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

/-- The hyperplane row retains exact group identifications for both factors. -/
theorem HyperplaneCase.factor_models (d : HyperplaneCase ρ) :
    (IsSimpleGroup d.first ∧ Group.IsPerfect d.first) ∧
      (Nonempty (d.second ≃* Equiv.Perm (Fin 3)) ∨
        (IsSimpleGroup d.second ∧ Group.IsPerfect d.second)) := by
  refine ⟨linear_three_simple_perfect d.firstEquiv, ?_⟩
  cases d.secondCase with
  | linearThree r hr hn =>
    obtain ⟨e⟩ := hn
    exact Or.inr (linear_three_simple_perfect e.groupEquiv)
  | linearTwo F hn =>
    obtain ⟨e⟩ := hn
    exact linear_two_models F e.groupEquiv

/-- B.5.6(5) gives precisely the factor types requested in 6.1.5. -/
theorem HyperplaneCase.factor_kinds (d : HyperplaneCase ρ) :
    IsQuasisimple (generalizedFitting d.first) ∧
      (Nonempty (d.second ≃* Equiv.Perm (Fin 3)) ∨
        IsQuasisimple (generalizedFitting d.second)) := by
  obtain ⟨⟨ha, hpa⟩, hb⟩ := d.factor_models
  let := ha
  let := hpa
  refine ⟨simple_perfect_fitting, ?_⟩
  rcases hb with he | ⟨hb, hpb⟩
  · exact Or.inl he
  · let := hb
    let := hpb
    exact Or.inr simple_perfect_fitting

/-- The original B.5.6(3) factors also have the exact 6.1.5 group types. -/
theorem SourceFactorCase.symmetricThree_or_quasisimple_fitting
    {A : Subgroup D} {U : Subrepresentation ρ} (d : SourceFactorCase ρ A U) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨ IsQuasisimple (generalizedFitting A) := by
  rcases d.group_models with he | he | ⟨hs, hp⟩
  · exact Or.inl he
  · right
    obtain ⟨e⟩ := he
    let := Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_generalizedFitting_isQuasisimple
    have hq := IsQuasisimple.of_mulEquiv
      (e.symm.subgroupMap (generalizedFitting (Equiv.Perm (Fin 5))))
    change IsQuasisimple ((generalizedFitting (Equiv.Perm (Fin 5))).map
      e.symm.toMonoidHom) at hq
    rwa [map_generalizedFitting_equiv e.symm] at hq
  · let := hs
    let := hp
    exact Or.inr simple_perfect_fitting

/-- The hyperplane factors are intrinsic up to interchange, just as in the
ordinary two-factor row; no whole-space splitting is needed. -/
theorem HyperplaneCase.automorphism_permutation [Finite D] (d : HyperplaneCase ρ)
    (hcore : pCore 2 D = ⊥) (e : MulAut D) :
    (d.first.map e.toMonoidHom = d.first ∧ d.second.map e.toMonoidHom = d.second) ∨
      (d.first.map e.toMonoidHom = d.second ∧ d.second.map e.toMonoidHom = d.first) := by
  obtain ⟨⟨ha, hpa⟩, hb⟩ := d.factor_models
  let := ha
  let := hpa
  have hquot : ∀ (N : Subgroup d.second) [N.Normal], N ≠ ⊥ →
      IsPGroup 2 (d.second ⧸ N) := by
    rcases hb with he | ⟨hs, _⟩
    · obtain ⟨eb⟩ := he
      exact normal_quotient_two_equiv eb symmetric_three_normal_quotient_two
    · let := hs
      exact simple_normal_quotient_two
  have hz : center d.second = ⊥ := by
    rcases hb with he | ⟨hs, hp⟩
    · obtain ⟨eb⟩ := he
      apply center_eq_bot_equiv eb
      apply (eq_bot_iff_forall _).mpr
      exact by decide
    · let := hs
      let := hp
      exact simple_perfect_center
  let : Nontrivial d.second := by
    rcases hb with he | ⟨hs, _⟩
    · obtain ⟨eb⟩ := he
      exact eb.symm.injective.nontrivial
    · let := hs
      infer_instance
  exact d.product.automorphism_permutation simple_normal_quotient_two hquot
    (d.product.swap.second_twoCore hcore) hz e

/-- The group types required of an individual source 6.1.5 factor. -/
@[expose] def SourceGroupFactorKind (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨ IsQuasisimple (generalizedFitting A)

/-- The two literal factors, independent of the two possible module geometries.
The permutation field is intrinsic, so original overgroup conjugation applies
without choosing new coordinates or an abstract product isomorphism. -/
structure SourceGroupFactorPair (D : Type*) [Group D] where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  factor_kinds : SourceGroupFactorKind first ∧ SourceGroupFactorKind second
  automorphism_permutation : ∀ e : MulAut D,
    (first.map e.toMonoidHom = first ∧ second.map e.toMonoidHom = second) ∨
      (first.map e.toMonoidHom = second ∧ second.map e.toMonoidHom = first)

/-- Retain the original factors and multiplication from B.5.6(3). -/
def SourceTwoFactorCase.groupFactorPair [Finite D] (d : SourceTwoFactorCase ρ)
    (hcore : pCore 2 D = ⊥) : SourceGroupFactorPair D where
  first := d.first
  second := d.second
  product := d.product
  factor_kinds := ⟨d.firstCase.symmetricThree_or_quasisimple_fitting,
    d.secondCase.symmetricThree_or_quasisimple_fitting⟩
  automorphism_permutation := d.automorphism_permutation hcore

/-- The hyperplane row uses exactly the same group-only selection interface. -/
def HyperplaneCase.groupFactorPair [Finite D] (d : HyperplaneCase ρ)
    (hcore : pCore 2 D = ⊥) : SourceGroupFactorPair D where
  first := d.first
  second := d.second
  product := d.product
  factor_kinds := ⟨Or.inr d.factor_kinds.1, d.factor_kinds.2⟩
  automorphism_permutation := d.automorphism_permutation hcore

/-- Complete B.5.6 reduces the source factor assertion to its one remaining
outer alternative. Both genuine product rows retain their literal factors. -/
theorem NontrivialAdequateAlternative.factor_decomposition [Finite D]
    (h : NontrivialAdequateAlternative ρ) (hcore : pCore 2 D = ⊥) :
    Nonempty (OuterSixThreeShape D) ∨ SourceGroupFactorKind D ∨
      Nonempty (SourceGroupFactorPair D) := by
  cases h with
  | quasisimple hq _ => exact Or.inr (Or.inl (Or.inr hq))
  | symmetricThree d => exact Or.inr (Or.inl (Or.inl ⟨d.equiv⟩))
  | twoFactors d => exact Or.inr (Or.inr ⟨d.groupFactorPair hcore⟩)
  | outerSixThree d => exact Or.inl ⟨d⟩
  | hyperplane d => exact Or.inr (Or.inr ⟨d.groupFactorPair hcore⟩)

end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
open Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Original quotient conjugation permutes the two literal hyperplane factors
on the Thompson image used by 6.1.5, including conjugation by the given H. -/
theorem hstar_overgroup_hyperplane_factor_permutation
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    letI : J.Normal := ThompsonImage.normal U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (d : ChapterB.SourceInduction.HyperplaneCase (ρ.comp J.subtype)) (x : X ⧸ C),
      (d.first.map (MulAut.conjNormal x).toMonoidHom = d.first ∧
        d.second.map (MulAut.conjNormal x).toMonoidHom = d.second) ∨
      (d.first.map (MulAut.conjNormal x).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal x).toMonoidHom = d.first) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let : J.Normal := ThompsonImage.normal U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  exact fun d x => d.automorphism_permutation (h.overgroup_thompson_hypothesis hX).twoCore
    (MulAut.conjNormal x)

/-- The complete classification on the original Thompson image gives one or
two source factors, with the outer A6--C3 case kept as the exact outstanding
alternative. No new classification or factorization hypothesis is assumed. -/
theorem hstar_overgroup_factor_decomposition
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    Nonempty (ChapterB.OuterSixThreeShape J) ∨
      ChapterB.SourceInduction.SourceGroupFactorKind J ∨
      Nonempty (ChapterB.SourceInduction.SourceGroupFactorPair J) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  exact (h.hstar_overgroup_thompson_classification hout hH hZH hHX hX).factor_decomposition
    (h.overgroup_thompson_hypothesis hX).twoCore

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
