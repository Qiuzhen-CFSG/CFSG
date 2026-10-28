module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.FactorClosureAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralApplications
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The actual binary unitary local action before regularity

A solvable original factor quotient makes its whole root closure solvable:
the two-core extension is solvable, and the normal factor together with the
unipotent two-group generates the closure. This proves solvability of the
same local permutation image without (2B).

For SU₃(2) and PSU₃(2), the earlier scalar descent gives an actual normal
PSU₃(2) subgroup of order 72, and the original Borel index gives panel degree
nine. The catalogue therefore retains a genuine local action and subgroup
in its unresolved branch. It does not identify the possible larger local
group or claim the type-VI exception satisfies (2B).
Source: Fong--Seitz I (2A)--(2B), (5B)--(5C); DGS (6.1), pp.118--119;
AS F.1.1--3. The final type-VI analysis remains with source recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
open HermitianForm
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

include e h in
/-- A solvable original quotient makes the whole local group solvable, before (2B). -/
theorem localGroup_isSolvable_of_factor_quotient
    (hs : Group.IsSolvable ((L i) ⧸ pCore 2 (L i))) :
    Group.IsSolvable (localGroup Q split i) := by
  let := h.finite_local i
  let := hs
  let : Group.IsNilpotent (pCore 2 (L i)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (L i) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (L i))).mpr ⟨inferInstance,inferInstance⟩
  let A := (factorMap Q e i).range
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (factorMap Q e i).rangeRestrict_surjective
  let : Group.IsNilpotent split.U := split.isTwo.isNilpotent
  have hj : Group.IsSolvable (A ⊔ split.U : Subgroup (X ⧸ Q.D)) :=
    Group.isSolvable_sup_of_normalizes _ _
      ((split.U_le.trans (Q.tits.B_le_standardParabolic _)).trans (factor_parabolic_normalizes Q e h i))
  have he : A ⊔ split.U = localClosure Q split i := factor_sup_unipotent Q e h split i
  let : Group.IsSolvable (localClosure Q split i) := he ▸ hj
  exact Group.isSolvable_of_surjective (localAction Q split i).rangeRestrict_surjective

variable [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hc : Nat.card E = 2^2) (hconj : ∀ x, J.conj x = x^2)

include e h hT hc hconj in
/-- The binary projective factor gives a solvable degree-nine local action and a normal order-72 subgroup. -/
theorem binary_projectiveUnitary_local
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Group.IsSolvable (localGroup Q split i) ∧ Nat.card (Panel Q i) = 9 ∧
      Function.Injective (projectiveUnitaryFactorLocalMap Q e h split i J μ) ∧
      (projectiveUnitaryFactorLocalMap Q e h split i J μ).range.Normal ∧
      Nat.card (projectiveUnitaryFactorLocalMap Q e h split i J μ).range = 72 := by
  have hcm : Nat.card E = (2^1)^2 := hc
  have hconjm : ∀ x, J.conj x = x^(2^1) := hconj
  have hinj := projectiveUnitaryFactorLocalMap_injective Q e h split i T hT J
    (by decide : 0 < 1) hcm hconjm μ
  refine ⟨?_,?_,hinj,projectiveUnitaryFactorLocalMap_range_normal Q e h split i J μ,?_⟩
  · let := FixedFieldTwo.projective_isSolvable J hc hconj
    exact localGroup_isSolvable_of_factor_quotient Q e h split i
      (Group.isSolvable_of_surjective (f := μ.symm.toMonoidHom) μ.symm.surjective)
  · have hi := singleton_parabolic_root_index Q split i
    change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hi
    rw [projectiveUnitary_simpleRoot_card Q e h split i T hT J
      (by decide : 0 < 1) hcm hconjm μ] at hi
    exact hi
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact FixedFieldTwo.card_projective J hc hconj

include e h hT hc hconj in
/-- The binary scalar cover gives the same genuine normal PSU3(2) local image. -/
theorem binary_specialUnitary_local
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    Group.IsSolvable (localGroup Q split i) ∧ Nat.card (Panel Q i) = 9 ∧
      Function.Injective (specialUnitaryFactorLocalMap Q e h split i T hT J
        (by decide : 0 < 1) hc hconj ν) ∧
      (specialUnitaryFactorLocalMap Q e h split i T hT J (by decide : 0 < 1) hc hconj ν).range.Normal ∧
      Nat.card (specialUnitaryFactorLocalMap Q e h split i T hT J
        (by decide : 0 < 1) hc hconj ν).range = 72 := by
  have hcm : Nat.card E = (2^1)^2 := hc
  have hconjm : ∀ x, J.conj x = x^(2^1) := hconj
  have hinj := specialUnitaryFactorLocalMap_injective Q e h split i T hT J
    (by decide : 0 < 1) hcm hconjm ν
  refine ⟨?_,?_,hinj,specialUnitaryFactorLocalMap_range_normal Q e h split i T hT J
    (by decide : 0 < 1) hcm hconjm ν,?_⟩
  · let := FixedFieldTwo.projective_isSolvable J hc hconj
    let : Group.IsSolvable (center J.specialSubgroup) := Group.isSolvable_of_comm
      (fun x y => Subtype.ext (mem_center_iff.mp x.property y.val).symm)
    let : Group.IsSolvable J.specialToProjective.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion J.specialToProjective_ker_le_center) (inclusion_injective _)
    let : Group.IsSolvable J.specialSubgroup := Group.isSolvable_of_ker_le_range
      J.specialToProjective.ker.subtype J.specialToProjective (by rw [range_subtype])
    exact localGroup_isSolvable_of_factor_quotient Q e h split i
      (Group.isSolvable_of_surjective (f := ν.symm.toMonoidHom) ν.symm.surjective)
  · have hi := singleton_parabolic_root_index Q split i
    change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hi
    rw [specialUnitary_simpleRoot_card Q e h split i T hT J
      (by decide : 0 < 1) hcm hconjm ν] at hi
    exact hi
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact FixedFieldTwo.card_projective J hc hconj

include e h hT in
/-- The local sieve retains the genuine solvable degree-nine action and its normal PSU3(2). -/
theorem remainder_le_kernel_or_binary_unitary_action :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i)) ∨
    (Group.IsSolvable (localGroup Q split i) ∧ Nat.card (Panel Q i) = 9 ∧
      ∃ A : Subgroup (localGroup Q split i), A.Normal ∧ Nat.card A = 72 ∧
        ClassicalGroup.IsPSU A 3 2) := by
  rcases remainder_le_kernel_or_small_unitary Q e h split i T hT with hreg | hpsu | hsu
  · exact Or.inl hreg
  · obtain ⟨F,hF,hfin,K,hcard,hconjugate,⟨μ⟩⟩ := hpsu
    obtain ⟨hsol,hpanel,hinj,hnorm,horder⟩ :=
      binary_projectiveUnitary_local Q e h split i T hT K hcard hconjugate μ
    exact Or.inr ⟨hsol,hpanel,_,hnorm,horder,F,hF,hfin,K,hcard,hconjugate,
      ⟨(MonoidHom.ofInjective hinj).symm⟩⟩
  · obtain ⟨F,hF,hfin,K,hcard,hconjugate,⟨ν⟩⟩ := hsu
    obtain ⟨hsol,hpanel,hinj,hnorm,horder⟩ :=
      binary_specialUnitary_local Q e h split i T hT K hcard hconjugate ν
    exact Or.inr ⟨hsol,hpanel,_,hnorm,horder,F,hF,hfin,K,hcard,hconjugate,
      ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
