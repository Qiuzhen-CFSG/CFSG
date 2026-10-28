module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTriality
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour
public import Theory.SpecificGroups.ReeF4.ParabolicResiduals
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# The Ree amalgam comparison in 5.2.6

The actual binary Ree parabolics are solvable. At larger fields, restricting
an original parabolic isomorphism to its solvable residual identifies the
selected factor with the corresponding fixed root factor. Its intrinsic
Suzuki quotient cannot be binary PSL₂. This fixes the orientation and
excludes both orientations for a diagram-selected right factor.

In the surviving whole-residual branch the original left quotient fixes
n = 2m+1 > 1. Both factor isomorphisms and the core orders q^11 and q^10
are retained. All amalgams use the whole overlap, including odd Cartans.
This is local comparison, not exhaustive classification or ambient completion
recognition. Those obligations and the F.1.12 core bound remain with
qt-d-1222-rankone-generic-global; original uniqueness retains its producer.

Source: Aschbacher–Smith 5.2.6(5), printed pp.650–651, and F.1.12(I)(5),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ChapterF.GreenBook.LieModels

namespace ReeComparison

/-- Both full parabolics of the binary Ree group are solvable. -/
theorem binary_parabolic_solvable (s : Side) : Group.IsSolvable (parabolic 0 s) := by
  rw [← ReeFour.binary_localFactor]
  let : Group.IsNilpotent (pCore 2 (localFactor 0 s)) := pCore_isNilpotent
  apply (Group.isSolvable_iff_subgroup_quotient (pCore 2 (localFactor 0 s))).mpr
  refine ⟨inferInstance, ?_⟩
  cases s with
  | linear =>
    let : Group.IsSolvable (LinearQuotient 0) :=
      Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using field_card 0)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (linearLocalQuotientEquiv 0).toMonoidHom) (linearLocalQuotientEquiv 0).injective
  | suzuki =>
    let : Group.IsSolvable (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :=
      BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (suzukiLocalQuotientEquiv 0).toMonoidHom) (suzukiLocalQuotientEquiv 0).injective

end ReeComparison

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

include d h hp in
/-- An original nonsolvable parabolic excludes the binary Ree field. -/
theorem Preparation.ree_parameter_positive (m : ℕ) (i : Fin 2) (s : Side)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* parabolic m s) :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst m
  let := ReeComparison.binary_parabolic_solvable s
  exact d.parabolics_not_solvable h hp i
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

include d h hTH hp in
/-- Restriction to the solvable residual identifies the same selected factor. -/
theorem Preparation.ree_parabolic_factor (m : ℕ) (i : Fin 2) (s : Side)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* parabolic m s) :
    Nonempty (![L,R] i ≃* localFactor m s) := by
  have hm := d.ree_parameter_positive h hp m i s e
  let X := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let a : solvableResidual X ≃* ![L,R] i :=
    ((solvableResidual X).equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp i))
  let b : solvableResidual (parabolic m s) ≃* localFactor m s :=
    ((solvableResidual (parabolic m s)).equivMapOfInjective
      (parabolic m s).subtype (parabolic m s).subtype_injective).trans
        (MulEquiv.subgroupCongr (parabolic_solvableResidual_map hm s))
  exact ⟨a.symm.trans (e.solvableResidualEquiv.trans b)⟩

include d h hTH hp in
/-- The actual Suzuki quotient excludes a binary PSL₂ source endpoint. -/
theorem Preparation.not_ree_suzuki_parabolic (m : ℕ) (i : Fin 2) {f : ℕ}
    (hlin : ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 (2^f)) :
    ¬ Nonempty (ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃*
      parabolic m .suzuki) := by
  rintro ⟨e⟩
  have hm := d.ree_parameter_positive h hp m i .suzuki e
  obtain ⟨a⟩ := d.ree_parabolic_factor h hTH hp m i .suzuki e
  exact binary_quotient_not_suzuki hlin hm
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (suzukiLocalQuotientEquiv m)⟩

include d h hTH hp in
/-- The original left factor cannot occupy the Suzuki endpoint. -/
theorem Preparation.not_ree_unreversed (m : ℕ) :
    ¬ Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (ReeFour.amalgam m)) := by
  rintro ⟨e⟩
  exact d.not_ree_suzuki_parabolic h hTH hp m 0 h.linear ⟨e.left⟩

include d h hTH hp in
/-- Both compatible orientations are excluded when the selected right quotient is binary PSL₂. -/
theorem Preparation.not_ree_amalgams {f : ℕ}
    (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f)) (m : ℕ) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ Nonempty (RankTwoAmalgam.Iso α (ReeFour.amalgam m)) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (ReeFour.amalgam m).reverse) := by
  refine ⟨d.not_ree_unreversed h hTH hp m, ?_⟩
  rintro ⟨e⟩
  exact d.not_ree_suzuki_parabolic h hTH hp m 1 hlin ⟨e.right⟩

include d h hTH hp in
/-- The surviving orientation identifies both factors, the original exponent and both intrinsic core orders. -/
theorem Preparation.ree_local_structure (m : ℕ)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ReeFour.amalgam m).reverse) :
    2*m+1 = n ∧ 0 < m ∧
      Nonempty (L ≃* localFactor m .linear) ∧
      Nonempty (R ≃* localFactor m .suzuki) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      Nat.card (pCore 2 L) = (2^n)^11 ∧ Nat.card (pCore 2 R) = (2^n)^10 := by
  have hm := d.ree_parameter_positive h hp m 0 .linear e.left
  obtain ⟨a⟩ := d.ree_parabolic_factor h hTH hp m 0 .linear e.left
  obtain ⟨b⟩ := d.ree_parabolic_factor h hTH hp m 1 .suzuki e.right
  let c := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (linearLocalQuotientEquiv m)
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := binary_psl_field_card_eq (f.symm.trans c)
  rw [hF,field_card] at hc
  have he : 2*m+1 = n := (Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm
  refine ⟨he,hm,⟨a⟩,⟨b⟩,?_,?_,?_⟩
  · exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (suzukiLocalQuotientEquiv m)⟩
  · exact (LocalCoreTransport.core_card 2 a).trans
      (by simpa only [he] using card_local_pCore_linear m)
  · exact (LocalCoreTransport.core_card 2 b).trans
      (by simpa only [he] using card_local_pCore_suzuki m)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
