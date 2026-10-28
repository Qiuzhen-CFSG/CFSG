module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionBlocks
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.SourceAmalgam

/-!
# The special U₅(4) comparison in 5.2.6

The line parabolic's solvable residual has the actual SU₃(4) quotient.
Binary PSL₂ has no such quotient, so the original L cannot occupy this
endpoint. The same obstruction excludes the opposite orientation whenever
the selected right factor has binary PSL₂ quotient, as in the diagram branch.

The whole-residual branch retains its possible U₅(4) comparison. Restricting
the surviving parabolic isomorphisms identifies the original L with the
plane residual and R with the line residual. The actual PSL₂(16) quotient
forces n = 4. Transport gives the full core orders and the line core's
special-group identities: its center has order four and equals both the
commutator and Frattini subgroups. The maps retain the whole overlap.

These results supply the literal local clauses of 5.2.6(7). Exhaustive
amalgam recognition and ambient completion remain with
qt-d-1222-rankone-generic-global; no global U₅(4) isomorphism is assumed.
Source: Aschbacher–Smith 5.2.6, pp.650–651, and F.1.12(I)(7), p.263
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

private def unitaryFiveLeftFactorEquiv (M : Model 4) (i : Fin 2)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* M.leftParabolic) :
    ![L,R] i ≃* M.leftLocalImage :=
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let a : solvableResidual P ≃* ![L,R] i :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp i))
  a.symm.trans (e.solvableResidualEquiv.trans M.leftLocalImageEquiv)

private def unitaryFiveRightFactorEquiv (M : Model 4) (i : Fin 2)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* M.rightParabolic) :
    ![L,R] i ≃* M.rightLocalImage :=
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let a : solvableResidual P ≃* ![L,R] i :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp i))
  a.symm.trans (e.solvableResidualEquiv.trans M.rightLocalImageEquiv)

include d h hTH hp
/-- A source factor with binary PSL₂ quotient cannot be the U₅(4) line
parabolic residual: the latter has the genuine special SU₃(4) quotient. -/
theorem Preparation.not_unitaryFive_line_parabolic
    (M : Model 4) (i : Fin 2) {f : ℕ}
    (hlin : ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 (2^f)) :
    ¬ Nonempty (ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* M.leftParabolic) := by
  rintro ⟨e⟩
  let a := unitaryFiveLeftFactorEquiv d h hTH hp M i e
  let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply binary_quotient_not_special_unitary hlin (m := 2) (by decide)
  obtain ⟨F,iF,iFin,J,hF,hJ,⟨b⟩⟩ := M.source_quotient_models.1
  exact ⟨F,iF,iFin,J,hF,hJ,⟨q.trans b⟩⟩

/-- The original faithful left factor fixes the U₅(4) orientation: its
PSL₂ quotient cannot lie at the line endpoint. -/
theorem Preparation.not_unitaryFive_unreversed (M : Model 4) :
    ¬ Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) M.amalgam) := by
  rintro ⟨e⟩
  exact d.not_unitaryFive_line_parabolic h hTH hp M 0 h.linear ⟨e.left⟩

/-- A diagram-selected right factor also has binary PSL₂ quotient, excluding
both compatible U₅(4) orientations. No such premise is imposed in the
whole-residual branch. -/
theorem Preparation.not_unitaryFive_amalgams {f : ℕ}
    (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f)) (M : Model 4) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ Nonempty (RankTwoAmalgam.Iso α M.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α M.amalgam.reverse) := by
  refine ⟨d.not_unitaryFive_unreversed h hTH hp M,?_⟩
  rintro ⟨e⟩
  exact d.not_unitaryFive_line_parabolic h hTH hp M 1 hlin ⟨e.right⟩

/-- The surviving U₅(4) orientation has exactly the source's n = 4,
PSL₂(16)/SU₃(4) local factors, and canonical core orders. The right core
has center equal to both its commutator and Frattini subgroup, as required
by the notation 4^(1+6). -/
theorem Preparation.unitaryFive_local_structure (M : Model 4)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) M.amalgam.reverse) :
    n = 4 ∧ Nonempty (L ≃* M.rightLocalImage) ∧ Nonempty (R ≃* M.leftLocalImage) ∧
      ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 ∧
      Nat.card (pCore 2 L) = 2^16 ∧ Nat.card (pCore 2 R) = 4^7 ∧
      Nat.card (center (pCore 2 R)) = 4 ∧
      center (pCore 2 R) = commutator (pCore 2 R) ∧
      center (pCore 2 R) = frattini (pCore 2 R) := by
  let a : L ≃* M.rightLocalImage := unitaryFiveRightFactorEquiv d h hTH hp M 0 e.left
  let b : R ≃* M.leftLocalImage := unitaryFiveLeftFactorEquiv d h hTH hp M 1 e.right
  let aQ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hn : n = 4 := by
    obtain ⟨F,_,_,hF,⟨c⟩⟩ := h.linear
    obtain ⟨E,_,_,hE,⟨g⟩⟩ := M.source_quotient_models.2
    let := Fintype.ofFinite F
    let := Fintype.ofFinite E
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4)
      (by simpa only [Nat.card_eq_fintype_card, Nat.reducePow] using hE)
    have hc := binary_psl_field_card_eq (c.symm.trans (aQ.trans g))
    rw [hF,hE] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  let ac : pCore 2 L ≃* pCore 2 M.rightLocalImage :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let bc : pCore 2 R ≃* pCore 2 M.leftLocalImage :=
    (b.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
  obtain ⟨_,hc,hz,hcomm,hfrat⟩ := M.leftLocalImage_core_structure
  refine ⟨hn,⟨a⟩,⟨b⟩,?_,(Nat.card_congr ac.toEquiv).trans M.rightLocalImage_core_card,
    (Nat.card_congr bc.toEquiv).trans hc,
    (Nat.card_congr (centerCongr bc).toEquiv).trans hz,?_,?_⟩
  · obtain ⟨F,iF,iFin,J,hF,hJ,⟨c⟩⟩ := M.source_quotient_models.1
    exact ⟨F,iF,iFin,J,hF,hJ,⟨bQ.trans c⟩⟩
  · apply map_injective (f := bc.toMonoidHom) bc.injective
    rw [center_map_equiv bc,map_commutator_eq,
      MonoidHom.range_eq_top.mpr bc.surjective,←_root_.commutator_def]
    exact hcomm
  · apply map_injective (f := bc.toMonoidHom) bc.injective
    rw [center_map_equiv bc,frattini_map_equiv bc]
    exact hfrat

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
