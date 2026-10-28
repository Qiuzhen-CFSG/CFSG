module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedRadicals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryElementaryExclusion

/-!
# Regularity from the original Sylow quotient and linear actor

The full amalgam marking identifies the original S with the split U. The
image of each original parabolic two-core lies in U and is normalized by
the marked parabolic, so it lies in the complementary root section even
before (2B). Separation of that section from the simple root makes the
root's projection into the original S/O₂(Pᵢ) injective.

An elementary original Sylow quotient therefore gives an elementary root.
The same conclusion follows from an actual map of an original actor
containing S into binary SL₂ with kernel contained in O₂(Pᵢ): its root
image lies in an elementary Sylow. The proved solvable nine-point
obstruction excludes the only defective F.1.1 catalogue entry. Thus both
inputs establish (2B) and its literal original core preimage, without
perfectness or any Weyl-order assumption. EqualLinearRecognition and
QuadraticProfileRecognition apply these results to the original C₂/U₄
profiles and their full marked comparisons.

Source: DGS (10.5), (11.5)--(11.7), pp.156--157,173--175;
Fong--Seitz I (2B), (5C), pp.9,25--26; AS F.1.1--3. No new source
profile, marked quotient, or split datum is assumed to have been produced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

private theorem root_lift_core_trivial (i : Fin 2) (r : simpleRoot Q split i)
    (hr : (markedSylowEquiv Q e h split).symm ⟨r,simpleRoot_le Q split i r.property⟩ ∈
      ((parabolic L S i).pCoreIn 2).subgroupOf S) : r = 1 := by
  let a := markedSylowEquiv Q e h split
  have hcore : (r : X ⧸ Q.D) ∈ (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 := by
    rw [← marked_sylow_core_map Q e h i]
    refine ⟨a.symm ⟨r,simpleRoot_le Q split i r.property⟩,hr,?_⟩
    rw [← markedSylowEquiv_apply]
    exact congrArg Subtype.val (a.apply_symm_apply _)
  have hrem : (r : X ⧸ Q.D) ∈ simpleRemainder Q split i :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.parabolic_core_le_remainder
      Q split i (marked_core_le_unipotent Q e h split i) hcore
  exact Subtype.ext ((disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨r.property,hrem⟩)

include e h in
/-- The original Sylow quotient makes the actual root elementary, before regularity. -/
theorem simpleRoot_elementary_of_sylow_core (i : Fin 2)
    (hc : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S)) :
    IsElementaryAbelian 2 (simpleRoot Q split i) := by
  let := original_core_normal_in_sylow (L := L) (S := S) i
  let := hc
  let a := markedSylowEquiv Q e h split
  let f : simpleRoot Q split i →* S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S :=
    (QuotientGroup.mk' _).comp (a.symm.toMonoidHom.comp (inclusion (simpleRoot_le Q split i)))
  apply IsElementaryAbelian.of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply eq_bot_iff.mpr
  intro r hr
  exact root_lift_core_trivial Q e h split i r ((QuotientGroup.eq_one_iff _).mp hr)

include e h in
/-- An elementary actual root excludes the only defective original catalogue row. -/
theorem regularity_of_elementary_root (i : Fin 2)
    (hc : IsElementaryAbelian 2 (simpleRoot Q split i)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic L S i) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  rcases MarkedLocal.remainder_le_kernel_or_binary_unitary_exception Q e h split i T hT with hr | hx
  · exact hr
  · exact (simpleRoot_not_elementary_of_solvable_nine Q split i hx.1 hx.2.1 hc).elim

include e h in
/-- The source Sylow quotient discharges (2B) and the exact original core preimage. -/
theorem regularity_of_sylow_core (i : Fin 2)
    (hc : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic L S i) :=
  regularity_of_elementary_root Q e h split i
    (simpleRoot_elementary_of_sylow_core Q e h split i hc)

include e h in
/-- A literal linear quotient of an original actor containing S supplies regularity without any perfectness premise. -/
theorem regularity_of_linear_actor {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (A : Subgroup (parabolic L S i))
    (hSA : S.subgroupOf (parabolic L S i) ≤ A)
    (f : A →* SL(2,F))
    (hk : f.ker ≤ (pCore 2 (parabolic L S i)).subgroupOf A) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic L S i) := by
  let g : S →* A :=
    ((inclusion (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left)).codRestrict A
      (fun s => hSA s.property))
  let l : simpleRoot Q split i →* S :=
    (markedSylowEquiv Q e h split).symm.toMonoidHom.comp (inclusion (simpleRoot_le Q split i))
  let z : simpleRoot Q split i →* SL(2,F) := f.comp (g.comp l)
  have hz : Function.Injective z := by
    apply z.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro r hr
    apply root_lift_core_trivial Q e h split i r
    have hh := hk (show g (l r) ∈ f.ker from hr)
    change ((l r : S) : G) ∈ (pCore 2 (parabolic L S i)).map (parabolic L S i).subtype
    exact ⟨(g (l r)).val,hh,rfl⟩
  have htwo : IsPGroup 2 z.range :=
    (split.isTwo.to_le (simpleRoot_le Q split i)).of_surjective z.rangeRestrict z.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := htwo.exists_le_sylow
  let a := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T
  let z' : simpleRoot Q split i →* T := z.codRestrict _ (fun r => hT ⟨r,rfl⟩)
  have hz' : Function.Injective z' := fun r t he => hz (congrArg Subtype.val he)
  let : IsElementaryAbelian 2 (Multiplicative F) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Multiplicative.toAdd.injective
        change (x^2).toAdd = 0
        rw [pow_two]
        exact CharTwo.add_self_eq_zero x.toAdd) }
  have he : IsElementaryAbelian 2 T := IsElementaryAbelian.of_injective a.symm.toMonoidHom a.symm.injective
  let := he
  exact regularity_of_elementary_root Q e h split i (IsElementaryAbelian.of_injective z' hz')
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
