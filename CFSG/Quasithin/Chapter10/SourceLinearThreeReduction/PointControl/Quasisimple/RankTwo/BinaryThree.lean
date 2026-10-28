module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.SpecificGroups.Triality.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.BinaryThreeSection

/-!
# Exceptional rank-two exclusions for the original binary-three quotient

The faithful-signalizer center lies in O₂(L), so the actual image of L
in the containing central quotient still has its SL₃(2) quotient. In
binary triality its full restricted Sylow places it in the arms factor,
whose SL₂(8) quotient contradicts the order-four section. In a Ree carrier
the nonzero core places it in a parabolic; the linear side has the same
order-four obstruction and the Suzuki side is three-free.

These comparisons apply to every original L₃(2) module row, including
four-natural and modules with fixed vectors. They use no generation bound
or irreducibility assertion for the fixed setup. RankTwo.Source applies
them to complete the rank-two carrier exclusion in this source branch.
Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The binary triality endpoint is impossible for every original L₃(2)
module row, including the four-natural row. -/
theorem not_binary_triality_of_binary_three [Group.IsPerfect I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (eI : (I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  obtain ⟨S,_,hB,hSN,_,hproper,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := (L.subgroupOf I).map (eI.toMonoidHom.comp q)
  let Q := R.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hQ : (Q : Subgroup (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)) =
      (R : Subgroup (I ⧸ center I)).map eI.toMonoidHom := rfl
  let : Group.IsSolvable eI.toMonoidHom.ker := by
    rw [eI.toMonoidHom.ker_eq_bot_iff.mpr eI.injective]
    infer_instance
  have hA : A ∈ localCComponents Q := by
    rw [hQ]
    simpa only [A,B,q,map_map] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hB eI.toMonoidHom
  have hAn : (Q : Subgroup (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)) ≤
      normalizer (A : Set (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)) := by
    rw [hQ]
    have hh := (map_mono (f := eI.toMonoidHom) hSN).trans (le_normalizer_map eI.toMonoidHom)
    simpa only [A,B,q,map_map] using hh
  have hAp : A ≠ ⊤ := by
    intro he
    apply hproper
    apply map_injective (f := eI.toMonoidHom) eI.injective
    rw [map_top_of_surjective eI.toMonoidHom eI.surjective]
    simpa only [A,B,q,map_map] using he
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (markedLocalHom_surjective c.strict.le eI)
  have hAns : ¬ Group.IsSolvable A := by
    intro hs
    let := hs
    exact hA.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ (Q : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  let dA := (markedCoreQuotientEquiv D c.strict.le eI).symm.trans dL
  exact Triality.Standard.BinaryLocalSections.no_binary_three_quotient_of_normalized
    Q A hAp hAns hAn (dA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))
    (dA.surjective.comp (QuotientGroup.mk'_surjective _))

/-- The literal noncentral core center and binary-three core quotient
exclude every Ree containing component. No module irreducibility is assumed. -/
theorem not_ree_of_binary_three
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False := by
  let A := (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (markedLocalHom_surjective c.strict.le eI)
  have hcore : pCore 2 A ≠ ⊥ := by
    intro hz
    apply marked_core_center_not_central D c.strict.le eI
    rintro _ ⟨z,_,rfl⟩
    have he : (z : A) = 1 := mem_bot.mp (hz ▸ z.property)
    change (z : A) ∈ center A
    rw [he]
    exact one_mem _
  exact ReeF4.ConverseParabolics.not_binary_three_core_quotient hm A hcore
    ((markedCoreQuotientEquiv D c.strict.le eI).symm.trans dL)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
