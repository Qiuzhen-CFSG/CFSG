module

public import CFSG.Quasithin.Chapter12.Section06.Setup
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Source
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality
public import Theory.Mathieu.M24.Properties.Order

/-!
# Original ambient escape in the orthogonal A₈ case

The original elementary module has a quotient of order 64. Its full
normalizer action has kernel containing that same module and image
containing the marked A₈. Hence 64·20160 divides the ambient group order.
This excludes every global recognition alternative of 12.2.13, whose
two-part is at most 1024. Recognition therefore gives centralizer escape
uniformly for the original chosen modules in this same G,T, and the earlier
A₇ source exclusion applies without any additional Chapter 13 hypotheses.

The structural and module statements of 12.2.2 and the standing
multiple-overgroup guard remain explicit. No nonsingular-centralizer
control or vanishing of the original fixed space is assumed.

Source: Aschbacher–Smith, 12.2.13, 12.3.1 and the original setup for 12.6,
printed pp.799,807,822–823.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Both the unchanged module and its faithful marked A₈ action contribute
to the ambient order, even when the original fixed space is nonzero. -/
theorem OrthogonalMarking.full_order_dvd
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) :
    64 * 20160 ∣ Nat.card G := by
  let q := (fixedSeed L V hn).toSubmodule.mkQ
  have hquot : Nat.card (Vhat L V hn) = 64 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_Vhat D]
    decide
  have hV : 64 ∣ Nat.card V := by
    have hh := AddSubgroup.card_dvd_of_surjective q.toAddMonoidHom
      (Submodule.mkQ_surjective (fixedSeed L V hn).toSubmodule)
    change Nat.card (Vhat L V hn) ∣ Nat.card V at hh
    rwa [hquot] at hh
  let f := V.normalizerMonoidHom
  have hkernel : V.subgroupOf (normalizer (V : Set G)) ≤ f.ker := by
    rw [show f.ker = (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) from
      V.normalizerMonoidHom_ker]
    exact comap_mono (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hVker : 64 ∣ Nat.card f.ker := by
    have he : Nat.card (V.subgroupOf (normalizer (V : Set G))) = Nat.card V :=
      Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv
    exact hV.trans (he ▸ card_dvd_of_le hkernel)
  have hsmall : Nat.card (conjugation L V hn).range = 20160 := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (conjugation L V hn)).toEquiv,Nat.card_congr D.groupEquiv.toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hsub : (conjugation L V hn).range ≤ f.range := by
    rintro x ⟨l,rfl⟩
    exact ⟨inclusion hn l,rfl⟩
  have himage : 20160 ∣ Nat.card f.range := hsmall ▸ card_dvd_of_le hsub
  have hnormalizer : 64 * 20160 ∣ Nat.card (normalizer (V : Set G)) := by
    have hh := Nat.mul_dvd_mul hVker himage
    rwa [←index_ker,f.ker.card_mul_index] at hh
  exact hnormalizer.trans (normalizer (V : Set G)).card_subgroup_dvd_card

private theorem not_binary_linear_of_order {X : Type*} [Group X] [Finite X]
    (hdiv : 64 * 20160 ∣ Nat.card X) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL X n 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
  let a := e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hc))
  rw [Nat.card_congr a.toEquiv] at hdiv
  rcases hn with rfl | rfl
  · rw [Atlas.Order20160A8.psl4Two_card] at hdiv
    norm_num at hdiv
  · rw [Nat.card_congr (BinaryLinear.OuterCyclic.projectiveEquivSL
      (by decide : 0 < 5)).toEquiv,
      Representation.SL5ExteriorSquare.card_specialLinearFive] at hdiv
    norm_num at hdiv

/-- Original same-ambient escape for every chosen module, forced by the
given orthogonal source configuration and the completed earlier recognition. -/
theorem SourceHypothesis.original_centralizer_escape
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Section03.SourceAlternatingSeven.CentralizerEscape T := by
  have hd := D.full_order_dvd
  intro Y W hY hW
  rcases RecognitionSource.alternatives_of_modules_of_many_at hY hW structural modules hmany with
    he | ⟨d,hdim,_,hm⟩ | ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩
  · exact he
  · exact (not_binary_linear_of_order hd (by omega) hm).elim
  · rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
    norm_num [Nat.factorial] at hd
  · rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order] at hd
    norm_num at hd

/-- Earlier 12.3.1 at every original member, with its literal central
quotient and no additional ambient-exclusion or escape premise. -/
theorem SourceHypothesis.original_not_alternating_seven
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (Y : Subgroup G) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) :=
  Section03.SourceAlternatingSeven.centralQuotient_not_alternatingSeven_at
    hY structural modules (S.original_centralizer_escape D structural modules hmany)

end CFSG.Quasithin.Chapter12.Section06
