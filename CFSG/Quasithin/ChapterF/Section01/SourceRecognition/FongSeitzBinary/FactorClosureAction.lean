module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuotientActionBound

/-!
# Original factors and the whole local closure's quotient action

Every original factor lies in the whole root closure. Its product with U
is normalized by the full marked endpoint, so it also contains U's
reflection and equals that closure. For a centerfree original two-core
quotient, conjugation identifies the closure modulo its two-core with a
subgroup of the original quotient's automorphism group. This supplies a
cardinality bound on the actual local cover, not a model tag.

The companion adapter transfers a bound on automorphism two-subgroups to
the panel-kernel criterion through the same injective factor map. No
original perfectness or equality of root and quotient-Sylow orders is
assumed. DihedralLocal consumes both results on the truncated Suzuki row.
Source: Fong--Seitz I (2B), (5B)--(5C), pp.7--9,25--26;
DGS (6.1), pp.118--119; AS F.1.1--3, pp.259--260.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

include e h in
/-- Transport the automorphism bound through the SAME original factor marking. -/
theorem remainder_le_kernel_of_factor_action_bound
    (hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥)
    (hb : ∀ V : Subgroup (MulAut ((L i) ⧸ pCore 2 (L i))), IsPGroup 2 V →
      Nat.card V ≤ Nat.card (simpleRoot Q split i)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let f := factorMap Q e i
  let A := f.range
  let a : L i ≃* A := MonoidHom.ofInjective (factorMap_injective Q e i)
  let c := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i} := by
    have he := congrArg (Subgroup.map (Q.tits.standardParabolic {Q.simple i}).subtype)
      (factorInEndpoint_generates_panel Q e h i)
    rw [Subgroup.map_sup, ← MonoidHom.range_comp,
      map_subgroupOf_eq_of_le (Q.tits.B_le_standardParabolic _),
      ← MonoidHom.range_eq_map, range_subtype] at he
    exact he
  apply PanelKernel.remainder_le_kernel_of_quotient_action_bound Q split i A
    (factor_parabolic_normalizes Q e h i) hgen
  · apply eq_bot_iff.mpr
    intro z hz'
    have he := MulEquivClass.apply_mem_center c.symm hz'
    change c.symm z ∈ center ((L i) ⧸ pCore 2 (L i)) at he
    rw [hz,mem_bot] at he
    exact c.symm.injective (he.trans c.symm.map_one.symm)
  · intro V hV
    let f := (MulAut.congr c.symm).toMonoidHom
    have hc := card_map_of_injective (K := V) (f := f) (MulAut.congr c.symm).injective
    exact hc ▸ hb (V.map f) (hV.map f)

include h in
/-- The original factor and U generate the whole local closure, without perfectness. -/
theorem factor_sup_unipotent :
    (factorMap Q e i).range ⊔ split.U = localClosure Q split i := by
  let A := (factorMap Q e i).range
  let J := A ⊔ split.U
  have hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i} := by
    have he := congrArg (Subgroup.map (Q.tits.standardParabolic {Q.simple i}).subtype)
      (factorInEndpoint_generates_panel Q e h i)
    rw [Subgroup.map_sup, ← MonoidHom.range_comp,
      map_subgroupOf_eq_of_le (Q.tits.B_le_standardParabolic _),
      ← MonoidHom.range_eq_map, range_subtype] at he
    exact he
  have hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (J : Set (X ⧸ Q.D)) := by
    rw [← hgen]
    apply sup_le ((show A ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf ((Q.tits.B_le_standardParabolic _).trans (factor_parabolic_normalizes Q e h i))
      split.normalizes).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm (sup_le (factor_le_localClosure Q e h split i) le_sup_left)
  apply sup_le le_sup_right
  have hh := comap_mono (f := (MulAut.conj
    (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) (show split.U ≤ J from le_sup_right)
  change unipotentConjugate split (Q.simple i) ≤ rightConjugate J _ at hh
  rwa [rightConjugate_eq_self _ (hn (Q.tits.bruhatCell_subset_standardParabolic_of_mem
    (Set.mem_singleton _) (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _))))] at hh

/-- The factor-unipotent join gives the literal whole local cover. -/
noncomputable def factorClosureQuotientEquiv :
    ((factorMap Q e i).range ⊔ split.U : Subgroup (X ⧸ Q.D)) ⧸
        pCore 2 ((factorMap Q e i).range ⊔ split.U : Subgroup (X ⧸ Q.D)) ≃*
      LocalCover.CoverGroup Q split i :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (factor_sup_unipotent Q e h split i))
    (pCore_map_iso 2 (MulEquiv.subgroupCongr (factor_sup_unipotent Q e h split i)))).trans
      (LocalCover.coreQuotientEquiv Q split i).symm

include e h in
/-- A centerfree original quotient bounds the whole local cover by its automorphisms. -/
theorem localCover_card_le_factor_aut
    (hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥) :
    Nat.card (LocalCover.CoverGroup Q split i) ≤ Nat.card (MulAut ((L i) ⧸ pCore 2 (L i))) := by
  let := h.finite_local i
  let A := (factorMap Q e i).range
  let a : L i ≃* A := MonoidHom.ofInjective (factorMap_injective Q e i)
  let c := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hzA : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz'
    have he := MulEquivClass.apply_mem_center c.symm hz'
    change c.symm z ∈ center ((L i) ⧸ pCore 2 (L i)) at he
    rw [hz,mem_bot] at he
    exact c.symm.injective (he.trans c.symm.map_one.symm)
  have hn : split.U ≤ normalizer (A : Set (X ⧸ Q.D)) :=
    (split.U_le.trans (Q.tits.B_le_standardParabolic _)).trans (factor_parabolic_normalizes Q e h i)
  let b := pCoreJoinQuotientEquivRange 2 hn split.isTwo hzA
  rw [← Nat.card_congr (factorClosureQuotientEquiv Q e h split i).toEquiv,
    Nat.card_congr b.toEquiv]
  exact (Nat.card_le_card_of_injective
    (fun x : (pCoreJoinAction 2 hn).range => MulAut.congr c.symm x.val)
    ((MulAut.congr c.symm).injective.comp Subtype.val_injective))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
