module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNative
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Triality

/-!
# The original selected pair from a reduced triality marking

Native restoration supplies compatible maps of the original endpoints into
the same automorphism extension, with both reduced restrictions and the
entire original Borel retained. Perfectness identifies each selected local
factor with its endpoint's solvable residual. Transporting these factors
through the literal restrictions constructs the existing normalized-Borel
consumer's full marking, including its inner intersections and whole overlap.
That consumer then proves the original right-core equality, containment of
the same original S in R, and the concrete comparison. No parity restriction
on the nonbinary triality exponent is imposed.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226–228;
Aschbacher–Smith F.1.12, printed pp.263–264. The genuine marked reduced
comparison remains an explicit input; this is its original-restoration
application, not an exhaustive source recognition theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem reduced_factor_marking
    {G X : Type*} [Group G] [Group X]
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (j : Fin 2) (hp : Group.IsPerfect (L j))
    (Q K : Subgroup X)
    (f : Source.parabolic L (SuzukiContainment.reducedSylow L S) j ≃* Q)
    (hQ : (solvableResidual Q).map Q.subtype = K) :
    ((L j).subgroupOf (Source.parabolic L (SuzukiContainment.reducedSylow L S) j)).map
      (Q.subtype.comp f.toMonoidHom) = K := by
  let := hp
  let := h.finite_local j
  let := (SuzukiContainment.reduced_hypothesis h).finite_parabolic j
  have he : (L j).subgroupOf (Source.parabolic L (SuzukiContainment.reducedSylow L S) j) =
      solvableResidual (Source.parabolic L (SuzukiContainment.reducedSylow L S) j) := by
    apply Subgroup.map_injective
      (Source.parabolic L (SuzukiContainment.reducedSylow L S) j).subtype_injective
    rw [map_subgroupOf_eq_of_le (show L j ≤ Source.parabolic L
      (SuzukiContainment.reducedSylow L S) j from le_sup_left.trans le_sup_left)]
    rw [← (SuzukiContainment.reduced_hypothesis h).local_residual_eq_parabolic j,
      solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [he, ← map_map, map_solvableResidual_eq _ f.surjective]
  exact hQ

private theorem local_image_of_restriction
    {G X : Type*} [Group G] [Group X] {P P₀ K : Subgroup G}
    (h₀ : P₀ ≤ P) (hK : K ≤ P₀)
    (f : P →* MulAut X) (g : P₀ →* X)
    (hf : ∀ x : P₀, f (inclusion h₀ x) = MulAut.conj (g x)) :
    (K.subgroupOf P).map f = ((K.subgroupOf P₀).map g).map MulAut.conj := by
  rw [map_map]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hK hx⟩,hx,(hf ⟨x,hK hx⟩).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨inclusion h₀ x,hx,hf x⟩

private theorem endpoint_range
    {X Y : Type*} [Group X] [Group Y] (P : Subgroup X) (f : Y ≃* P) :
    (P.subtype.comp f.toMonoidHom).range = P := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective f.toMonoidHom f.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

private def markingFromIso
    {G X : Type*} [Group G] [Group X] {L R S : Subgroup G}
    {K₀ K₁ P₀ P₁ : Subgroup X} (h : HypothesisF11 ![L,R] S)
    (U : SourceCompletion.UnitaryNonbinary.SourceExtension P₀ P₁)
    (E : Iso (originalAmalgam ![L,R] S) U.amalgam)
    (h₀ : (solvableResidual (Source.parabolic ![L,R] S 0)).map
      (U.left.subtype.comp E.left.toMonoidHom) = K₀.map MulAut.conj)
    (h₁ : (solvableResidual (Source.parabolic ![L,R] S 1)).map
      (U.right.subtype.comp E.right.toMonoidHom) = K₁.map MulAut.conj) :
    Global.OriginalExtension.Marking L R S K₀ K₁ P₀ P₁ := by
  let J : Iso (Global.sourceParabolicAmalgam ![L,R] S) (originalAmalgam ![L,R] S) := {
    left := MulEquiv.refl _
    right := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 h)
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  let F := J.trans E
  let f₀ := U.left.subtype.comp F.left.toMonoidHom
  let f₁ := U.right.subtype.comp F.right.toMonoidHom
  have hf₀ : f₀.range = U.left := endpoint_range _ F.left
  have hf₁ : f₁.range = U.right := endpoint_range _ F.right
  refine { left := f₀, right := f₁
           left_injective := Subtype.val_injective.comp F.left.injective
           right_injective := Subtype.val_injective.comp F.right.injective
           agrees := ?_, left_residual := h₀, right_residual := h₁
           left_base := ?_, right_base := ?_, whole_overlap := ?_ }
  · intro x
    exact (congrArg Subtype.val (F.left_commutes x)).trans
      (congrArg Subtype.val (F.right_commutes x)).symm
  · rw [hf₀]
    exact U.left_inner
  · rw [hf₁]
    exact U.right_inner
  · have he : f₀.comp (Global.sourceParabolicAmalgam ![L,R] S).left =
        U.middle.subtype.comp F.middle.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact congrArg Subtype.val (F.left_commutes x)
    rw [he, endpoint_range, hf₀, hf₁]

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (m : ℕ) (hm : 0 < m) (hm2 : 1 < m) (i : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (TrialityNative.amalgam m hm i))

include d h hTH hm2 e
/-- Construct compatible markings of both original endpoints, their residuals,
inner intersections and full overlap from the same marked reduced row. -/
theorem exists_original_triality_marking_of_reduced_iso (hp : Group.IsPerfect R) :
    Nonempty (Global.OriginalTriality.Marking m hm (TrialityNative.side i)
      L R (Global.sourceS L H)) := by
  let hf := d.hypothesisF11 h hTH
  let U := TrialityNative.extension hf m hm i e hm2
  obtain ⟨E,_,hleft,hright⟩ := TrialityNative.exists_original_extension_iso hf m hm i e hm2
  have hq : 2 < (binaryParameters m hm).q := by
    rw [binaryParameters_q]
    exact (show 2^1 < 2^m from Nat.pow_lt_pow_right (by decide) hm2)
  have hK₀ : ((![L,R] 0).subgroupOf
      (Source.parabolic ![L,R] (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) 0)).map
      (TrialityNative.reducedCompletion m hm i e).left =
        localFactor (binaryParameters m hm) (TrialityNative.side i) :=
    reduced_factor_marking hf 0 (Chapter1.mem_L_isPerfect h.local_mem.1.1) _ _ e.left
      (parabolic_solvableResidual_map _ rfl hq _)
  have hK₁ : ((![L,R] 1).subgroupOf
      (Source.parabolic ![L,R] (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) 1)).map
      (TrialityNative.reducedCompletion m hm i e).right =
        localFactor (binaryParameters m hm) (TrialityNative.side (!i)) :=
    reduced_factor_marking hf 1 hp _ _ e.right
      (parabolic_solvableResidual_map _ rfl hq _)
  have hs : Global.OriginalTriality.other (TrialityNative.side i) = TrialityNative.side (!i) := by
    cases i <;> rfl
  dsimp only [Global.OriginalTriality.Marking]
  rw [hs]
  refine ⟨markingFromIso hf U E ?_ ?_⟩
  · rw [← d.original_local_eq_residual h hTH hp 0]
    exact (local_image_of_restriction (SuzukiContainment.reduced_parabolic_le hf 0)
      (show ![L,R] 0 ≤ Source.parabolic ![L,R]
        (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) 0 from
          le_sup_left.trans le_sup_left) (U.left.subtype.comp E.left.toMonoidHom)
        (TrialityNative.reducedCompletion m hm i e).left hleft).trans
        (congrArg (Subgroup.map MulAut.conj) hK₀)
  · rw [← d.original_local_eq_residual h hTH hp 1]
    exact (local_image_of_restriction (SuzukiContainment.reduced_parabolic_le hf 1)
      (show ![L,R] 1 ≤ Source.parabolic ![L,R]
        (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) 1 from
          le_sup_left.trans le_sup_left) (U.right.subtype.comp E.right.toMonoidHom)
        (TrialityNative.reducedCompletion m hm i e).right hright).trans
        (congrArg (Subgroup.map MulAut.conj) hK₁)

/-- The literal normalized-Borel consumer removes the extension at every
nonbinary degree, retaining the original selected R and original S. -/
theorem triality_original_core_and_containment_of_reduced_iso (hp : Group.IsPerfect R) :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R := by
  obtain ⟨f⟩ := exists_original_triality_marking_of_reduced_iso d h hTH m hm hm2 i e hp
  have hR := f.right_residual
  rw [← d.original_local_eq_residual h hTH hp 1] at hR
  exact ⟨d.triality_extension_right_core m hm (Global.OriginalTriality.other (TrialityNative.side i))
      f.right f.right_injective hR,
    d.sourceS_le_right_of_original_triality h hTH hp m hm (TrialityNative.side i) f⟩

/-- The same restored maps supply an actual concrete catalogue comparison,
with its field exponent and orientation forced by the original source pair. -/
theorem triality_original_comparison_of_reduced_iso (hp : Group.IsPerfect R) :
    Nonempty (Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (Global.OriginalTriality.orientedAmalgam m hm (TrialityNative.side i))) ∧
      m = n ∧ TrialityNative.side i = .central := by
  obtain ⟨f⟩ := exists_original_triality_marking_of_reduced_iso d h hTH m hm hm2 i e hp
  exact ⟨⟨d.originalTrialityComparison h hTH hp m hm (TrialityNative.side i) f⟩,
    (d.original_triality_field h hTH hp m hm (TrialityNative.side i) f).1,
    d.original_triality_orientation h hTH hp m hm (TrialityNative.side i) f⟩

/-- The triality row of the original concrete catalogue is obtained from a
reduced marking; no original marking or extension-collapse premise remains. -/
theorem triality_concreteComparison_of_reduced_iso (hp : Group.IsPerfect R) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨f⟩ := exists_original_triality_marking_of_reduced_iso d h hTH m hm hm2 i e hp
  exact d.concreteComparison_of_original_triality h hTH hp m hm (TrialityNative.side i) f

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
