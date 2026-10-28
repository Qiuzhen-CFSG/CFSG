module
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.RankOneCovers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Actual local A₅ sections in binary triality

A full-Sylow local C-component with nontrivial two-core is a conjugate of a
literal root local factor. The intrinsic core of its Sylow supplement is
nontrivial. Its normalizer lies in a genuine parabolic by the proved triality
hexagon theorem. Perfectness and the cyclic parabolic quotient put the
component in the local factor, while every two-element belongs to that
prime-to-two residual. The rank-one cover theorem then gives equality.

An A₅ quotient forces the central node and field order four: the arms quotient
is SL₂(q³), whose order cannot be sixty. At q = 2 the actual carrier order is
five-free, so the small parameter is excluded before applying perfectness.
All subgroups, conjugations and quotient maps are the actual root carriers.

Source: Aschbacher–Smith A.3.12(2), F.1.12(I)(4), and 10.2.9, printed
pp.47–48, 263–264, and 750–751.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem local_perfect {G : Type*} [Group G] (S : Subgroup G)
    {B : Subgroup G} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem perfect_le_local (P : Parameters) (hp : P.prime = 2) (a : Node)
    (B : Subgroup (Carrier P)) [Group.IsPerfect B] (hB : B ≤ parabolic P a) :
    B ≤ localFactor P a := by
  let X := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient X
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact h (show (⟨x,hB hx⟩ : parabolic P a) ∈ X from hx)

/-- A local component with nontrivial two-core is a conjugate of a literal
triality local factor. -/
theorem local_placement (n : ℕ) (hn : 0 < n) (hq : 2 < 2 ^ n)
    (S : Sylow 2 (BinaryCarrier n hn)) (B : Subgroup (BinaryCarrier n hn))
    (hB : B ∈ localCComponents S) (hcore : pCore 2 B ≠ ⊥) :
    ∃ (g : BinaryCarrier n hn) (a : Node),
      B.map (MulAut.conj g).toMonoidHom = localFactor (binaryParameters n hn) a := by
  let P := binaryParameters n hn
  let H := B ⊔ (S : Subgroup (BinaryCarrier n hn))
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro hzero
    have hle := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hB.subnormal)
    rw [pCoreIn_subgroupOf 2 B H le_sup_left,map_subgroupOf_eq_of_le
      ((B.pCoreIn_le 2).trans le_sup_left)] at hle
    change B.pCoreIn 2 ≤ H.pCoreIn 2 at hle
    rw [hzero] at hle
    apply hcore
    apply map_injective B.subtype_injective
    exact (le_bot_iff.mp hle).trans (Subgroup.map_bot _).symm
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set (BinaryCarrier n hn)) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  obtain ⟨g,a,hg⟩ := TwoLocalCover.normalizer_cover n hn (H.pCoreIn 2) hQ (isPGroup_pCoreIn 2 H)
  let c := MulAut.conj g
  let S' := S.mapSurjective (f := c.toMonoidHom) c.surjective
  let B' := B.map c.toMonoidHom
  let : Group.IsSolvable c.toMonoidHom.ker := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr c.injective]
    infer_instance
  have hb : B' ∈ localCComponents (S' : Subgroup (BinaryCarrier n hn)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB c.toMonoidHom
  have hBP : B' ≤ parabolic P a := (map_mono (le_sup_left.trans hHN)).trans hg
  have hSP : (S' : Subgroup (BinaryCarrier n hn)) ≤ parabolic P a :=
    (map_mono (le_sup_right.trans hHN)).trans hg
  let := local_perfect (S' : Subgroup (BinaryCarrier n hn)) hb
  have hBK : B' ≤ localFactor P a := perfect_le_local P rfl a B' hBP
  have hSK : (S' : Subgroup (BinaryCarrier n hn)) ≤ localFactor P a :=
    sylow_le_localFactor P a S' hSP
  let := localFactor_isPerfect P rfl hq a
  refine ⟨g,a,?_⟩
  cases a with
  | arms =>
    apply local_eq_of_sl2_core_quotient (localFactor P .arms) ?_
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm) S' B' hb hBK hSK
    rw [card_extensionField]
    have hh : 2 < P.q := hq
    have hpow : 27 ≤ P.q ^ 3 := Nat.pow_le_pow_left (show 3 ≤ P.q by omega) 3
    omega
  | central =>
    apply local_eq_of_sl2_core_quotient (localFactor P .central) ?_
      ((localFactorCentralQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField P.prime P.exponent)).symm) S' B' hb hBK hSK
    rw [card_baseField]
    exact hq

/-- The A₅ quotient forces q = 4 and the central parabolic, not the arms node. -/
theorem five_section_placement (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (BinaryCarrier n hn)) (B : Subgroup (BinaryCarrier n hn))
    (hB : B ∈ localCComponents S) (hcore : pCore 2 B ≠ ⊥)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    2 ^ n = 4 ∧ ∃ g : BinaryCarrier n hn,
      B.map (MulAut.conj g).toMonoidHom = localFactor (binaryParameters n hn) .central := by
  have hq : 2 < 2 ^ n := by
    have hge := (binaryParameters n hn).q_ge_two
    change 2 ≤ 2 ^ n at hge
    by_contra! hh
    have htwo : (binaryParameters n hn).q = 2 := le_antisymm hh hge
    have hd := card_quotient_dvd_card (pCore 2 B)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
    norm_num at hd
    have hfive := (by decide : 5 ∣ 60).trans (hd.trans B.card_subgroup_dvd_card)
    change 5 ∣ Nat.card (Carrier (binaryParameters n hn)) at hfive
    rw [ConcreteBruhat.FixedCellCount.card_carrier,ConcreteBruhat.FixedCellCount.card_borel,htwo] at hfive
    norm_num at hfive
  obtain ⟨g,a,hg⟩ := local_placement n hn hq S B hB hcore
  let c := (MulAut.conj g).subgroupMap B
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  cases a with
  | arms =>
    have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃*
        SL(2, ExtensionField (binaryParameters n hn)) := by
      rw [hg]
      exact (localFactorArmsQuotientEquivPSL2 _ rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm
    have hh := field_four_of_sl2_five_section e (cq.trans ep)
    rw [card_extensionField] at hh
    have hge := (binaryParameters n hn).q_ge_two
    have hpow : 8 ≤ (binaryParameters n hn).q ^ 3 := Nat.pow_le_pow_left hge 3
    omega
  | central =>
    have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2, GaloisField 2 n) := by
      rw [hg]
      exact (localFactorCentralQuotientEquivPSL2 _ rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm
    have hh := field_four_of_sl2_five_section e (cq.trans ep)
    have he : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (Nat.ne_of_gt hn)
    exact ⟨he ▸ hh,g,hg⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
