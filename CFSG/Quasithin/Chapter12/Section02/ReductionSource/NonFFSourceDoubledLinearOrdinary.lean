module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearResidualPair
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpReeCentered
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SquareFieldSections

/-!
# Excluding every original ordinary component in the nonbinary doubled row

The whole original linear-three pair has rank six times the field degree.
Its literal reciprocal residual moves it and has no fixed points, so the
complete module survives projection by the ordinary component's center.
For a nonbinary field its rank is at least twelve. The actual Theorem-C
catalogue and centered Ree exclusion therefore eliminate every ordinary
component. The original residual's simple quotient is projective SL₃;
the scalar center is retained until that explicit quotient is taken.

Source: Aschbacher--Smith C.3.2--5, 4.4.6 and 7.5.2, printed pp.149--150,
620,700, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both original summands contribute their complete binary dimension. -/
theorem sourceOrbit_linear_dimension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 6 * F.degree := by
  obtain ⟨_,_,_,_,_,e,_,_,_⟩ := D.sourceOrbit_linear_pair_coordinates h hd F hmodel
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  rw [e.finrank_eq,Module.finrank_prod,Subspace.dual_finrank_eq]
  simp [Module.finrank_pi_fintype,hF]
  omega

private theorem linear_central_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* PSL(3,F.Carrier)) := by
  obtain ⟨m⟩ := hmodel
  exact ⟨(D.componentCentralQuotientEquiv h.quasisimple).trans
    (centerQuotientCongr m.groupEquiv)⟩

/-- The literal whole-orbit C.2.8 places the actual moved pair in the
original residual two-core, with no residual-fixed subgroup. -/
theorem sourceOrbit_linear_witness_residual_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Group.IsPerfect LH ∧ D.sourceOrbit ≤ LH.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,LH⁆ ∧
      D.sourceOrbit ⊓ centralizer (LH : Set G) = ⊥ := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hs : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH := hc.normalized_span_eq hn
  have hULH : D.sourceOrbit ≤ LH := hs ▸ hc.module_le
  have hLHN : LH ≤ normalizer (D.sourceOrbit : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes
  have hperfect : Group.IsPerfect LH := hs ▸ hc.span_perfect
  have hm : D.sourceOrbit = ⁅D.sourceOrbit,LH⁆ := hs ▸ hc.module_commutator
  exact ⟨hperfect,
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) hULH hLHN,
    hm,D.sourceOrbit_linear_witness_fixed_eq_bot h hd F hmodel hw⟩

/-- Every ordinary component of the actual reciprocal overgroup is
incompatible with the complete nonbinary linear-three source orbit. -/
theorem sourceOrbit_linear_witness_not_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,hcore,hcomm,hfix⟩ :=
    D.sourceOrbit_linear_witness_residual_data h hd F hmodel hw hWJ hJC
  obtain ⟨e⟩ := D.linear_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (PSL(3,F.Carrier)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (PSL(3,F.Carrier)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨c,_⟩,_⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : LH →* PSL(3,F.Carrier) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hr : 12 ≤ primeRank 2 D.sourceOrbit := by
    have hcard : Nat.card D.sourceOrbit = 2 ^ (6 * F.degree) := by
      rw [Nat.card_congr Additive.ofMul]
      simpa only [Nat.card_zmod,D.sourceOrbit_linear_dimension h hd F hmodel] using
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    let : IsElementaryAbelian 2 (⊤ : Subgroup D.sourceOrbit) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup D.sourceOrbit).subtype Subtype.val_injective
    have hb := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup D.sourceOrbit)
      (by simpa only [card_top] using hcard)
    omega
  exact no_ordinary_normalized_rankOne hc hn hcore D.sourceOrbit_weakClosure_setup.nontrivial
    hcomm hfix hr (Group.IsPerfect.not_isSolvable _)
    (Matrix.PSL3.LinearThree.not_two_exponent (MulEquiv.refl _) F.card_eq) π hπ K hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
