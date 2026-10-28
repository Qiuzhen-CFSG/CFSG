module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticReciprocal
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticPushingUp
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrained
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpReeCentered
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization

/-!
# Residual uniqueness on the original nonbinary doubled orbit

The reciprocal argument supplies the actual C.2.8 witness and its escape.
The unchanged whole orbit has dimension 8n, lies in the residual's two-core,
and has no residual-fixed vectors. Its rank therefore excludes every ordinary
component through the source C.3 catalogue and the centered Ree calculation.
The inclusion-induced residual quotient, the concrete symplectic order and
its non-elementary Sylow exclude every constrained C.2.7 component.

Both branches being impossible, C_L(A)^infinity has N_G(L) as its unique
maximal two-local overgroup. This discharges the pushing-up branch of 4.4.6
for the nonbinary row. The later escaping odd-normalizer component still
requires exclusion for Hall faithfulness; the A₆ row remains separate.

Source: Aschbacher--Smith 4.2.12--13 and 4.4.6, printed pp.610--612,620,
applied to 7.3.4, p.699, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem whole_rank_ge_of_finrank {d : ℕ}
    (hd : Module.finrank (ZMod 2) (Additive D.sourceOrbit) = d) :
    d ≤ primeRank 2 D.sourceOrbit := by
  have hc : Nat.card D.sourceOrbit = 2 ^ d := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod,hd] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  let : IsElementaryAbelian 2 (⊤ : Subgroup D.sourceOrbit) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup D.sourceOrbit).subtype Subtype.val_injective
  exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup D.sourceOrbit)
    (by simpa only [card_top] using hc)

private theorem symplectic_central_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))) :
    Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* Sp F.Carrier) := by
  obtain ⟨m⟩ := hmodel
  exact ⟨(D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (EvenProjective.center_eq_bot (F := F.Carrier))).trans
        QuotientGroup.quotientBot))⟩

/-- Every ordinary component in the original nonbinary pushing-up configuration
is excluded using the whole orbit of dimension 8n. -/
theorem sourceOrbit_symplectic_pushingUp_no_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    {A J H W : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨hnorm,_,hcore,hcomm,hfix⟩ := D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA ho hw
  obtain ⟨e⟩ := D.symplectic_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (Sp F.Carrier) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Sp F.Carrier) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,hc,_,_,_,_,⟨c,_⟩,_⟩
  let R := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : R →* Sp F.Carrier := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hr : 12 ≤ primeRank 2 D.sourceOrbit :=
    (by omega : 12 ≤ 8 * F.degree).trans
      (D.whole_rank_ge_of_finrank (D.sourceOrbit_symplectic_dimension h hd F hmodel))
  exact no_ordinary_normalized_rankOne hc hnorm hcore D.sourceOrbit_weakClosure_setup.nontrivial
    hcomm hfix hr (Group.IsPerfect.not_isSolvable _) (doubledSymplectic_not_two_exponent F.card_eq)
    π hπ K hK

/-- Every constrained component in the original nonbinary pushing-up pair
is excluded on its actual residual quotient map. -/
theorem sourceOrbit_symplectic_pushingUp_no_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨e⟩ := D.symplectic_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (Sp F.Carrier) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Sp F.Carrier) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,hc,_,hnorm,_,_,⟨c,_⟩,_⟩
  have hnorm' := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hnorm
  let R := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : R →* Sp F.Carrier := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  exact no_constrained_normalized_rankOne hc hnorm' (Group.IsPerfect.not_isSolvable _)
    (doubledSymplectic_not_two_exponent F.card_eq) π hπ
    (doubledSymplectic_card_gt_20160 F.card_eq hn)
    (doubledSymplectic_card_not_dvd_linear_five_two F.card_eq hn) K hK hq hout hfK

/-- Source 4.4.6(2) for the nonbinary paired symplectic row, on the original
fixed residual. Both the ordinary and constrained C.2.8 branches are discharged. -/
theorem sourceOrbit_symplectic_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,W,hw,hescape⟩ := D.sourceOrbit_symplectic_reciprocal_escape h F hmodel A hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have he : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hf => hescape (hf.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape he
  rcases hcases with hordinary | hconstrained
  · exact D.sourceOrbit_symplectic_pushingUp_no_ordinary h hd hmany hnon F hn hmodel hA ho hw K hordinary
  · exact D.sourceOrbit_symplectic_pushingUp_no_constrained h F hn hmodel hw K hK hq hout hconstrained
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
