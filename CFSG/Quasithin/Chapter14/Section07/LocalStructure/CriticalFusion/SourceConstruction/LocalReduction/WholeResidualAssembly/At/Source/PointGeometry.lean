module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CyclicResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NaturalRecognition
public import Theory.GroupTheory.PResidual.CyclicThree
public import Theory.GroupTheory.PResidual.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LocalOvergroups
public import Theory.GroupTheory.PResidual.NormalPrimeLift
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPoint
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreOddJoin
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.CyclicFixedRank
public import Theory.GroupTheory.PResidual.AbelianQuotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Baumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPointReduction
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.LinearThreeCore
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import Theory.GroupTheory.Commutator.SmallNormalizedImage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPointRankOne
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.Commutator.BoundedImageKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialBranch
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialDegree
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointNormality
public import Theory.GroupAction.Extraspecial27CubicFixer
public import Theory.Representation.ExtraspecialCubicSmallActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralizerFactors
public import Theory.Representation.BinaryConjugationSection.DisplacementBound

/-!
# Guarded point geometry

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding cyclic three-group residuals at the original point normalizer

A critical path gives a reciprocal conjugate of U in R₁. If R₁ were
contained in O₂(H), transporting back would put U inside the reciprocal
core, contrary to criticality. Thus R₁ has nontrivial image under the
literal star map. The point-parabolic image has order six times its
two-core order, so every Sylow two-subgroup of H/O₂(H) has order divisible
by four. A cyclic three-group two-residual would instead give Sylow
order at most two.

The canonical equivalence K/O₂(K) ≃ O²(H/O₂(H)) retains the original
quotient map on representatives. It transfers the exclusion to the exact
residual used by the source construction. The final conditional application
removes this cyclic alternative from a prospective residual classification.
It does not prove the remaining residual alternatives.

Here H is the original point normalizer F.H. The full source 14.7.8 also
quantifies over smaller members of H_z. The only explicit earlier source
inputs in the original-group application are Structural1222 and the full
12.2.13 escape theorem; neither a critical path nor a recognized model is
assumed there.

Source: Aschbacher–Smith, 14.7.8, printed p.1045; the critical geometry
of F.8.7 and the residual alternatives of 14.7.52, printed p.1065.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Reciprocal criticality prevents the original point core from lying in O₂(H). -/
theorem point_core_not_le_H_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : ¬ F.Ri L 1 ≤ F.H.pCoreIn 2 := by
  intro hle
  obtain ⟨g, _, hHg, hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective, hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      ((hAR.trans hle).trans_eq hQmap.symm))

/-- The original R₁ has nontrivial image in the literal star quotient. -/
theorem point_core_star_nontrivial
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : star F (F.Ri L 1) ≠ ⊥ := by
  intro hz
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hk : (F.Ri L 1).subgroupOf F.H ≤ pCore 2 F.H := by
    simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk'] using hz
  apply point_core_not_le_H_core h structural c
  intro x hx
  exact mem_map_of_mem F.H.subtype (hk (show (⟨x,hRH hx⟩ : F.H) ∈
    (F.Ri L 1).subgroupOf F.H from hx))

/-- The point-parabolic image forces four to divide every star Sylow order. -/
theorem four_dvd_star_sylow_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (S : Sylow 2 (HStar F.H)) :
    4 ∣ Nat.card S := by
  have hBH : B ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  let f : B →* HStar F.H := (starMap F).comp (inclusion hBH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hBH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)
  have hr := point_image_ratio_at h structural f hk
  have him : (pCore 2 B).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 B).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hne : pCore 2 f.range ≠ ⊥ := by
    intro he
    apply point_core_not_le_H_core h structural c
    rintro x ⟨x,hx,rfl⟩
    have hzero : f.rangeRestrict x = 1 :=
      mem_bot.mp (he ▸ him (mem_map_of_mem _ hx))
    have hxcore : inclusion hBH x ∈ pCore 2 F.H :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hzero)
    exact mem_map_of_mem F.H.subtype hxcore
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hz
    exact hne (eq_bot_of_card_eq _ (by simpa only [hz, pow_zero] using hn))
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hd : 4 ∣ Nat.card f.range := by
    rw [hr, hn, pow_succ]
    exact ⟨3 * 2 ^ k, by ring⟩
  exact S.pow_dvd_card_of_pow_dvd_card (n := 2)
    (hd.trans f.range.card_subgroup_dvd_card)

/-- The original star quotient cannot have cyclic three-group two-residual. -/
theorem no_cyclic_three_star_residual_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G)) :
    ¬ (IsCyclic (pResidual 2 (HStar F.H)) ∧ IsPGroup 3 (pResidual 2 (HStar F.H))) := by
  rintro ⟨hcyc,hthree⟩
  let := hcyc
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath_at h hab hescape structural
  let S : Sylow 2 (HStar F.H) := Classical.choice inferInstance
  have hb := Sylow.card_le_two_of_cyclic_three_residual S (pCore_quotient_pCore_eq_bot 2) hthree
  have hd := four_dvd_star_sylow_card h structural c S
  have hp := Nat.card_pos (α := S)
  have := Nat.le_of_dvd hp hd
  omega

/-- The canonical residual comparison through the original map H → H/O₂(H). -/
noncomputable def residualStarEquiv (F : InvariantFlag T V 3) :
    ((K F) ⧸ pCore 2 (K F)) ≃* pResidual 2 (HStar F.H) := by
  let E : K F ≃* pResidual 2 F.H :=
    (subgroupOfEquivOfLe (show K F ≤ F.H from map_subtype_le _)).symm.trans
      (MulEquiv.subgroupCongr (residual_subgroupOf F))
  let Q := QuotientGroup.congr (pCore 2 (K F)) (pCore 2 (pResidual 2 F.H))
    E (pCore_map_iso 2 E)
  have hc : pCore 2 (pResidual 2 F.H) =
      (pCore 2 F.H).subgroupOf (pResidual 2 F.H) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 F.H).Normal).isSubnormal
  exact Q.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans
    (pResidualQuotientEquiv 2 (pCore 2 F.H)))

set_option backward.isDefEq.respectTransparency false in
/-- The residual comparison sends an original representative to its star image. -/
theorem residualStarEquiv_mk (F : InvariantFlag T V 3) (k : K F) :
    (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) =
      starMap F ⟨k, (map_subtype_le _ : K F ≤ F.H) k.property⟩ := by
  dsimp only [residualStarEquiv, MulEquiv.trans_apply]
  rw [QuotientGroup.congr_mk']
  change (pResidualQuotientEquiv 2 (pCore 2 F.H)
    (QuotientGroup.mk' ((pCore 2 F.H).subgroupOf (pResidual 2 F.H))
      (((subgroupOfEquivOfLe (show K F ≤ F.H from map_subtype_le _)).symm.trans
        (MulEquiv.subgroupCongr (residual_subgroupOf F))) k)) : HStar F.H) = _
  rw [pResidualQuotientEquiv_mk]
  rfl

/-- The cyclic three-group exclusion on the literal K/O₂(K). -/
theorem no_cyclic_three_residual_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G)) :
    ¬ (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) := by
  rintro ⟨hcyc,hthree⟩
  let := hcyc
  let e := residualStarEquiv F
  exact no_cyclic_three_star_residual_of_escape h hab structural hescape
    ⟨isCyclic_of_surjective e e.surjective, hthree.of_equiv e⟩

/-- Apply the cyclic exclusion with escape supplied by the full earlier 12.2.13 theorem. -/
theorem no_cyclic_three_residual_of_earlier_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    ¬ (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) :=
  no_cyclic_three_residual_of_escape h hab structural (h.flag_escape_at F previous)

/-- The original source-data consumer discharges the cyclic three-group branch.
The other residual alternatives and the independent G₂ exclusion remain explicit. -/
theorem exists_data_of_cyclic_or_residual_alternatives
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hcandidates :
      (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) ∨
      AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  have h52 : AlternatingResidual F ∨ G2Residual F := hcandidates.resolve_left
    (no_cyclic_three_residual_of_earlier_source h hab structural previous)
  exact exists_data_of_residual_alternatives_at d h hab structural h52 h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The minimal large-prime obstruction in the original local family

For any J in H_z, a normal subgroup with p-group star image, p > 3,
cannot lie in M unless that image is trivial. Inside the point normalizer,
TI makes M preserve V. The action on V/V₁ has order dividing six; the
prime image therefore acts trivially. Normality extends this to the whole
J-span, whose literal action kernel is O₂(J).

Choose a minimal normal elementary subgroup in a nonzero p-core and take
the two-residual of its full preimage. The preceding argument makes this
lift escape M. A minimal local p-core obstruction is generated by this
lift and L₁T: the lift keeps its intrinsic two-core quotient in every
intermediate overgroup. Hence that minimal subgroup is solvable. Its
prime core is elementary of order p or p², complemented by the original
point-parabolic image, which acts irreducibly on it.

These are the first reductions of 14.7.6, with the original ambient group,
flag and quotient maps. The offender/dihedral reduction and ambient
exclusion of the surviving prime cases remain; no vanishing of large-prime
cores, solvable-local exclusion or final residual classification is claimed.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045; its use in
14.7.28–29, printed p.1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem LargePrimeReduction_local_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    (F.localTildeAction J hJ.2.1).ker = pCore 2 J := by
  let := h.chosen.elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  exact F.localKernel_eq_pCore h.source.simpleQTKE L _ J (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    (((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural))) h.centralizer_L hJ

private theorem LargePrimeReduction_seed_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (F.tilde V)) = 6 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let f := F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  have hk : f.ker = (F.Vi 1).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, ← Subtype.val_inj]
    change (F.tildeProjection ⟨v, _⟩ = 1) ↔ (v : G) ∈ F.Vi 1
    exact QuotientGroup.eq_one_iff _
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  have he := QuotientGroup.quotientKerEquivOfSurjective f (F.tildeMap_surjective V _)
  have hker : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
  have hfour : Nat.card (F.tilde V) = 4 := by
    rw [Nat.card_congr he.toEquiv, hker, hV] at hc
    omega
  let : Nontrivial (F.tilde V) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (F.tilde V) := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  exact IsKleinFour.card_mulAut _

/-- A normal subgroup whose star image is a large-prime group cannot lie
in the source normalizer unless that star image is trivial. -/
theorem local_normal_largePrime_image_eq_bot_of_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (N : Subgroup G) (hNJ : N ≤ J) (hn : (N.subgroupOf J).Normal)
    (hNp : IsPGroup p ((N.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))))
    (hNM : N ≤ normalizer (L : Set G)) :
    (N.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) = ⊥ := by
  let := h.chosen.elementary
  let := hn
  have hNH := hNJ.trans hJ.2.1
  have hNV : N ≤ normalizer (V : Set G) :=
    (le_inf hNM hNH).trans (inf_normalizer_le_of_trivial_intersections
      ((structural L h.source).2.2 V h.chosen).2.2.1
      (by intro he; have hc := F.card 1 (by decide); rw [he,card_bot] at hc; norm_num at hc)
      (F.le_seed 1))
  let f := F.tildeAction N V hNH hNV
  let q : N →* HStar J := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hNJ)
  have hqr : q.range = (N.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hqf : q.ker ≤ f.ker := by
    intro a ha
    have hacore : inclusion hNJ a ∈ pCore 2 J := (QuotientGroup.eq_one_iff _).mp ha
    have hak : inclusion hNJ a ∈ (F.localTildeAction J hJ.2.1).ker :=
      (LargePrimeReduction_local_action_kernel h structural J hJ).symm ▸ hacore
    exact (F.mem_tildeAction_ker_iff N V hNH
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) hNV a).mpr
      (fun v hv => (F.mem_localTildeAction_ker_iff J hJ.2.1 _).mp hak v
        (le_conjugateSpanBy V J hv))
  let f₀ := QuotientGroup.lift q.ker f hqf
  have hqp : IsPGroup p (N ⧸ q.ker) :=
    (hqr.symm ▸ hNp).of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  have hf₀p : IsPGroup p f₀.range := hqp.of_surjective f₀.rangeRestrict f₀.rangeRestrict_surjective
  have hpc : Nat.Coprime p 6 := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd
    have hd' : p ∣ 2 ∨ p ∣ 3 := (Fact.out : p.Prime).dvd_mul.mp hd
    rcases hd' with hd' | hd' <;> have := Nat.le_of_dvd (by decide) hd' <;> omega
  obtain ⟨k,hk⟩ := hf₀p.exists_card_eq
  have hd := f₀.range.card_subgroup_dvd_card
  rw [LargePrimeReduction_seed_aut_card h] at hd
  have hcard : Nat.card f₀.range = 1 :=
    Nat.eq_one_of_dvd_coprimes (hk ▸ hpc.pow_left k) dvd_rfl hd
  have hf0 : f₀.range = ⊥ := Subgroup.card_eq_one.mp hcard
  have hf (a : N) : f a = 1 := by
    exact mem_bot.mp (hf0 ▸ (show f₀ (QuotientGroup.mk' q.ker a) ∈ f₀.range from ⟨_,rfl⟩))
  have hNseed : N.subgroupOf J ≤
      ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L J) hJ.2.1 V := by
    intro a ha
    apply (ChapterF.Section08.Setup.mem_quotientCentralizer_iff (F.f8SourceSetup L J) hJ.2.1 V
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) a).mpr
    intro v hv
    have hh := (F.mem_tildeAction_ker_iff N V hNH
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) hNV ⟨a,ha⟩).mp (hf ⟨a,ha⟩) v hv
    simpa only [commutatorElement_inv] using (F.Vi 1).inv_mem hh
  have hNcore : N.subgroupOf J ≤ pCore 2 J := by
    rw [←LargePrimeReduction_local_action_kernel h structural J hJ,←F.f8Source_core_eq_kernel L J hJ.2.1
      (h.chosen.le_sylow.trans (show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx)))]
    exact normal_le_normalCore.mpr hNseed
  rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  exact hNcore
/-- Every nontrivial large-prime core supplies a normal two-perfect lift
which escapes M, with its exact original quotient and elementary marking. -/
theorem local_largePrime_core_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hne : pCore p (HStar J) ≠ ⊥) :
    ∃ (X : Subgroup (HStar J)) (Y : Subgroup J),
      X.Normal ∧ X ≠ ⊥ ∧ X ≤ pCore p (HStar J) ∧ IsElementaryAbelian p X ∧
      (∀ W : Subgroup (HStar J), W.Normal → W ≤ X → W = ⊥ ∨ W = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map J.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨X,hXn,hXne,hXle,hXp,hXmin⟩ := exists_minimal_normal_le_pCore hne
  let := hXn
  let := hXp
  obtain ⟨Y,hYn,hYp,hYle,hYm,hYk,he⟩ := exists_normal_prime_residual_lift (by omega : p ≠ 2)
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) X (IsElementaryAbelian.isPGroup p X)
  refine ⟨X,Y,hXn,hXne,hXle,hXp,hXmin,hYn,hYp,hYle,hYm,hYk,he,?_⟩
  intro hM
  have hsub : (Y.map J.subtype).subgroupOf J = Y :=
    comap_map_eq_self_of_injective J.subtype_injective Y
  have hz := local_normal_largePrime_image_eq_bot_of_le_normalizer h structural J hJ hp
    (Y.map J.subtype) (map_subtype_le Y) (hsub.symm ▸ hYn)
    (by rw [hsub,hYm]; exact IsElementaryAbelian.isPGroup p X) hM
  rw [hsub,hYm] at hz
  exact hXne hz

private def LargePrimeReduction_normalLocalCoreImageEquiv (N I : Subgroup G) (hNI : N ≤ I)
    (hn : (N.subgroupOf I).Normal) :
    (N ⧸ pCore 2 N) ≃* (N.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let := hn
  let e := (subgroupOfEquivOfLe hNI).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (coreQuotientEquivImage 2 (N.subgroupOf I))

private theorem LargePrimeReduction_local_family_of_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hIH : I ≤ F.H) (hIM : ¬ I ≤ normalizer (L : Set G)) :
    I ∈ F.Hz L (normalizer (L : Set G)) := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 1) (by simpa using hcard))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBI))) hIH
  have hcore : I.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hp := le_bot_iff.mp (he ▸ hpoint)
    simp [hp] at hcard
  exact ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBI (mem_sup_left ha)) (fun ha => hBI (mem_sup_right ha))⟩,hIH,hIM⟩

private theorem LargePrimeReduction_point_parabolic_largePrime_coprime
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    Nat.Coprime p (Nat.card (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  have hsix : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (pointQuotientEquiv_at (F := F) h structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  have h2 : Nat.Coprime p 2 :=
    (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime p 3 :=
    (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr (by omega)
  change Nat.Coprime p (Nat.card B)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hsix,hk]
  exact (h2.mul_right h3).mul_right (h2.pow_right k)

private theorem LargePrimeReduction_local_prime_core_of_split_point_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (X : Subgroup (HStar I)) [X.Normal] (hXp : IsPGroup p X)
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    X = pCore p (HStar I) ∧ Disjoint X
      (((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let f := q.comp (inclusion hBI)
  let B₀ := (B.subgroupOf I).map q
  have hfr : f.range = B₀ := by rw [MonoidHom.range_comp,inclusion_range]
  have hcop : Nat.Coprime p (Nat.card B₀) :=
    (LargePrimeReduction_point_parabolic_largePrime_coprime (F := F) h structural hp).of_dvd_right
      (hfr ▸ card_range_dvd f)
  have hidx : X.index ∣ Nat.card B₀ := by
    rw [←relIndex_top_right,←hgen,relIndex_sup_left]
    exact relIndex_dvd_card X B₀
  have hnot : ¬ p ∣ X.index := (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.of_dvd_right hidx)
  let S := hXp.toSylow hnot
  have hcore : pCore p (HStar I) ≤ X := pCore_isPGroup.le_sylow_of_normal S
  refine ⟨le_antisymm (le_sSup ⟨inferInstance,hXp⟩) hcore,?_⟩
  obtain ⟨k,hk⟩ := hXp.exists_card_eq
  exact disjoint_of_coprime_natCard (by rw [hk]; exact hcop.pow_left k)

omit [Finite G] in
/-- In the minimal large-prime subgroup, the original point-parabolic
image acts irreducibly on the elementary prime core. -/
private theorem LargePrimeReduction_local_largePrime_point_irreducible
    (I : Subgroup G) {p : ℕ} [Fact p.Prime]
    (X : Subgroup (HStar I)) (hX : IsElementaryAbelian p X)
    (hmin : ∀ W : Subgroup (HStar I), W.Normal → W ≤ X → W = ⊥ ∨ W = X)
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    ∀ W : Subgroup (HStar I), W ≤ X →
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
        normalizer (W : Set (HStar I)) → W = ⊥ ∨ W = X := by
  let := hX
  intro W hWX hBW
  have hXW : X ≤ normalizer (W : Set (HStar I)) :=
    (X.le_centralizer.trans (centralizer_le hWX)).trans (Subgroup.centralizer_le_normalizer _)
  have htop : (⊤ : Subgroup (HStar I)) ≤ normalizer (W : Set (HStar I)) :=
    hgen ▸ sup_le hXW hBW
  have hn : W.Normal := normalizer_eq_top_iff.mp (top_unique htop)
  exact hmin W hn hWX

/-- The first source reduction in 14.7.6: a large-prime core in any actual
local subgroup gives a minimal such subgroup generated by the point
parabolic and a normal elementary prime lift. -/
theorem local_largePrime_minimal_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hne : pCore p (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore p (HStar D) = ⊥) ∧
      X.Normal ∧ X ≠ ⊥ ∧ X ≤ pCore p (HStar I) ∧ IsElementaryAbelian p X ∧
      (∀ W : Subgroup (HStar I), W.Normal → W ≤ X → W = ⊥ ∨ W = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ (Nat.card X = p ∨ Nat.card X = p ^ 2) ∧
      X = pCore p (HStar I) ∧
      Disjoint X (((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I))) ∧
      X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)) = ⊤ ∧
      (∀ W : Subgroup (HStar I), W ≤ X →
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
          normalizer (W : Set (HStar I)) → W = ⊥ ∨ W = X) := by
  obtain ⟨I,⟨hI,hIp⟩,hIJ,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun D : Subgroup G => D ∈ F.Hz L (normalizer (L : Set G)) ∧ pCore p (HStar D) ≠ ⊥)
    J ⟨hJ,hne⟩
  obtain ⟨X,Y,hXn,hXne,hXle,hXp,hXmin,hYn,hYp,hYle,hYm,hYk,he,hout⟩ :=
    local_largePrime_core_lift h structural I hI hp hIp
  have hproper (D : Subgroup G) (hD : D ∈ F.Hz L (normalizer (L : Set G))) (hDI : D < I) :
      pCore p (HStar D) = ⊥ := by
    by_contra hn
    exact hDI.ne (hmin D ⟨hD,hn⟩ hDI.le)
  refine ⟨I,X,Y,hIJ,hI,hproper,hXn,hXne,hXle,hXp,hXmin,
    hYn,hYp,hYle,hYm,hYk,he,hout,?_⟩
  let N := Y.map I.subtype
  let D := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  have hNI : N ≤ I := map_subtype_le Y
  have hsub : N.subgroupOf I = Y := comap_map_eq_self_of_injective I.subtype_injective Y
  have hIN : I ≤ normalizer (N : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hNI).mp (hsub.symm ▸ hYn)
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hDI : D ≤ I := sup_le hNI hBI
  have hND : N ≤ D := le_sup_left
  have hDN : (N.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer (hDI.trans hIN)
  have hD : D ∈ F.Hz L (normalizer (L : Set G)) :=
    LargePrimeReduction_local_family_of_interval h D le_sup_right (hDI.trans hI.2.1)
      (fun hm => hout (hND.trans hm))
  let eN : Y ≃* N := equivMapOfInjective Y I.subtype I.subtype_injective
  let eQ : (N ⧸ pCore 2 N) ≃* X :=
    (QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).symm.trans he.some
  let E := (N.subgroupOf D).map (QuotientGroup.mk' (pCore 2 D))
  let e : X ≃* E := eQ.symm.trans (LargePrimeReduction_normalLocalCoreImageEquiv N D hND hDN)
  let := hDN
  let : E.Normal := (inferInstance : (N.subgroupOf D).Normal).map _ (QuotientGroup.mk'_surjective _)
  have hEp : IsPGroup p E := by
    let := hXp
    exact (IsElementaryAbelian.isPGroup p X).of_equiv e
  have hEne : E ≠ ⊥ := by
    intro hz
    have hcard := Nat.card_congr e.toEquiv
    rw [hz,card_bot] at hcard
    exact hXne (Subgroup.card_eq_one.mp hcard)
  have hDp : pCore p (HStar D) ≠ ⊥ := by
    intro hz
    exact hEne (bot_unique ((show E ≤ pCore p (HStar D) from le_sSup ⟨inferInstance,hEp⟩).trans_eq hz))
  have hgen : I = D := (hmin D ⟨hD,hDp⟩ hDI).symm
  refine ⟨hgen,?_,?_,?_⟩
  · let := hXp
    let : Group.IsSolvable (Y ⧸ pCore 2 Y) := Group.isSolvable_of_isSolvable_injective (f := he.some.toMonoidHom) he.some.injective
    let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable Y := (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr
      ⟨inferInstance,inferInstance⟩
    let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective (f := eN.symm.toMonoidHom) eN.symm.injective
    let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
    let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable (B ⧸ pCore 2 B) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (pointQuotientEquiv_at (F := F) h structural).toMonoidHom)
        (pointQuotientEquiv_at (F := F) h structural).injective
    let : Group.IsSolvable B := (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr
      ⟨inferInstance,inferInstance⟩
    exact hgen.symm ▸ Group.isSolvable_sup_of_normalizes N B (hBI.trans hIN)
  · have hpoint : F.Vi 1 ≠ ⊥ := by
      intro he
      have hc := F.card 1 (by decide)
      rw [he,card_bot] at hc
      norm_num at hc
    have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
      IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
    have hr : primeRank p I ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hI.2.1) (inclusion_injective hI.2.1)).trans
        ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin p Fact.out ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
    have hrs : primeRank p (HStar I) ≤ 2 :=
      (primeRank_quotient_le_of_isTwoGroup p ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (pCore 2 I) pCore_isPGroup).trans hr
    have hc : Nat.card X ≤ p ^ 2 := (primeRank_le_iff_elementary_card_le (HStar I)).mp hrs X hXp
    let := hXp
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p X).exists_card_eq
    have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hn ▸ hc)
    have hn0 : n ≠ 0 := by
      intro he0
      exact hXne (Subgroup.card_eq_one.mp (by simpa only [he0,pow_zero] using hn))
    rcases (show n = 1 ∨ n = 2 by omega) with h1 | h2
    · exact Or.inl (by simpa only [h1,pow_one] using hn)
    · exact Or.inr (by simpa only [h2] using hn)

  · let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 I)
    have hgenI : Y ⊔ B.subgroupOf I = ⊤ := by
      apply Subgroup.map_injective I.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBI,←MonoidHom.range_eq_map,range_subtype]
      exact hgen.symm
    have hgenStar : X ⊔ (B.subgroupOf I).map q = ⊤ := by
      have hh := congrArg (map q) hgenI
      rw [Subgroup.map_sup,hYm,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
      exact hh
    let := hXn
    let := hXp
    obtain ⟨hcore,hdis⟩ := LargePrimeReduction_local_prime_core_of_split_point_image h structural I hBI hp X
      (IsElementaryAbelian.isPGroup p X) hgenStar
    exact ⟨hcore,hdis,hgenStar,
      LargePrimeReduction_local_largePrime_point_irreducible I X hXp hXmin hgenStar⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Normal point residuals before the 14.7.52 classification

Normality of the literal L₁* lifts to relative normality of L₁ in H.
The same normal branch follows when the actual K/O₂(K) is abelian, using
its canonical comparison with O²(H/O₂(H)). The original point action
identifies L₁/O₂(L₁) as cubic. In the normal branch this gives |L₁*| = 3
and R₁* = C_{T*}(L₁*) of index two, without replacing the full star quotient.

Commutator generation gives a fixed-free cubic on every literal U/V₁
section. Each point-core displacement is a module for that cubic and
therefore has even dimension. The original 12.8.4 kernel theorem then
shows that actors with commutators in one line lie in O₂(H). Terminal-edge
transport proves that the actual critical actor Uα* is nontrivial and
centralizes L₁*. The final applications use the source's literal star
normality and abelian-residual antecedents.

Normality also supplies the plane geometry of 12.8.5, discharging the
plane-centralizer premise of the original 14.7.31 weak-closure implication
in the abelian-residual branch. These are preparations for the remaining
solvable exclusions. The equality QQ_H = R₁, the full clauses of 14.7.5(1),
and the residual alternatives through 14.7.52 remain to be established.
No source datum or local-recognition callback is assumed.

Source: Aschbacher–Smith, Lemmas 12.8.4–5 and 14.7.5, printed
pp.850–851 and 1043–1044; 14.7.31, printed p.1055.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

private theorem NormalPoint_point_residual_relative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 ((B).subgroupOf F.H)).map ((B).subgroupOf F.H).subtype =
      (F.Li L 1).subgroupOf F.H := by
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  apply map_injective F.H.subtype_injective
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hBH, residual_group_at h structural,
    map_subgroupOf_eq_of_le hLH]

/-- Normality of the literal star image lifts through the two-core kernel. -/
theorem pointResidual_normal_of_star_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : (star F (F.Li L 1)).Normal) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let A := (F.Li L 1).subgroupOf F.H
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hp : IsPPerfect 2 A := by
    change IsPPerfect 2 ((F.Li L 1).subgroupOf F.H)
    rw [← NormalPoint_point_residual_relative h structural]
    exact isPPerfect_embedded_pResidual 2 _
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkn : (starMap F).ker ≤ normalizer (A : Set F.H) := by
    rw [starMap, QuotientGroup.ker_mk']
    let S : Sylow 2 F.H := T.subtype (F.invariant 1)
    apply le_trans (pCore_isPGroup.le_sylow_of_normal S)
    change ((T : Subgroup G).subgroupOf F.H) ≤
      normalizer ((F.Li L 1).subgroupOf F.H : Set F.H)
    rw [← subgroupOf_normalizer_eq hLH]
    exact fun _ hx => T_normalizes_L₁_at h structural hx
  have he := comap_normalizer_map_of_pPerfect (starMap F) A hp hk hkn
  let : (A.map (starMap F)).Normal := hn
  rw [normalizer_eq_top, comap_top] at he
  exact normalizer_eq_top_iff.mp he.symm

/-- An abelian actual residual quotient forces relative point-residual normality. -/
theorem pointResidual_normal_of_abelian_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F))) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := ha
  let : IsMulCommutative (pResidual 2 (HStar F.H)) :=
    IsMulCommutative.of_comm (fun a b => (residualStarEquiv F).symm.injective
      (by simp only [map_mul, mul_comm]))
  rw [← NormalPoint_point_residual_relative h structural]
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  exact residual_normal_of_p_kernel_abelian_residual (starMap F)
    (QuotientGroup.mk'_surjective _) hk S ((B).subgroupOf F.H)
    (fun _ hx => mem_sup_right hx)

/-- The original point residual has cubic two-core quotient, before classification. -/
theorem pointResidual_core_quotient_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nat.card ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) = 3 := by
  obtain ⟨f,hf,hk⟩ := exists_point_permutation_action_at h structural
  let E : pResidual 2 B ≃* F.Li L 1 :=
    (equivMapOfInjective (pResidual 2 B) (B).subtype (B).subtype_injective).trans
      (MulEquiv.subgroupCongr (residual_group_at h structural))
  let Q := QuotientGroup.congr _ _ E (pCore_map_iso 2 E)
  rw [← Nat.card_congr Q.toEquiv,
    Nat.card_congr (f.pResidualCoreQuotientEquiv hf hk).toEquiv,
    Equiv.Perm.twoResidual_eq_alternating]
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hthree : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 (alternatingGroup (Fin 3)) = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hthree.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  rw [hcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hc]

/-- Relative normality identifies the point residual image as the same cubic quotient. -/
theorem pointResidual_star_card_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : Nat.card (star F (F.Li L 1)) = 3 := by
  let A := (F.Li L 1).subgroupOf F.H
  let : A.Normal := hn
  let f := (starMap F).subgroupMap A
  have hk : f.ker = pCore 2 A := by
    rw [ker_subgroupMap, starMap, QuotientGroup.ker_mk',
      pCore_subnormal_eq_comap 2 hn.isSubnormal]
    rfl
  have E := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((starMap F).subgroupMap_surjective A))
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    let e : A ≃* F.Li L 1 := subgroupOfEquivOfLe
      (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  exact (Nat.card_congr E.toEquiv).symm.trans hc

/-- The normal point residual generates the entire original H-span by commutators. -/
theorem commutator_U_point_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : ⁅F.U, F.Li L 1⁆ = F.U := by
  let := h.chosen.elementary
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  exact (conjugateSpanBy_eq_commutator_of_seed V F.H (F.Li L 1) (F.Li L 1)
    hLH ((normal_subgroupOf_iff_le_normalizer hLH).mp hn) le_rfl
    (seed_commutator h F)).symm

/-- The original H-span lies in the point residual in the normal branch. -/
theorem U_le_pointResidual_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : F.U ≤ F.Li L 1 := by
  let := h.chosen.elementary
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  rw [← commutator_U_point_of_normal h hn]
  exact le_normalizer_iff_commutator_le_right.mp
    (F.U_le_H.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))

/-- The original point core maps to the core of the original point image. -/
theorem point_core_star_eq_image_core :
    star F (F.Ri L 1) = (star F B).pCoreIn 2 := by
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have he : ((B).subgroupOf F.H).pCoreIn 2 =
      ((B).pCoreIn 2).subgroupOf F.H := by
    apply map_injective F.H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ F.H.subtype_injective,
      map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH)]
  change (((B).pCoreIn 2).subgroupOf F.H).map (starMap F) = _
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rw [← he, map_pCoreIn_of_ker_isPGroup (starMap F) hk]
  rfl

/-- In the normal-L₁ branch, R₁* is exactly the Sylow centralizer of L₁*. -/
theorem point_core_star_eq_centralizer_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
      centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let : (star F (F.Li L 1)).Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  let S' : Sylow 2 (HStar F.H) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hs : star F B = star F (F.Li L 1) ⊔ (S' : Subgroup (HStar F.H)) := by
    change ((B).subgroupOf F.H).map (starMap F) = _
    rw [subgroupOf_sup (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
      (show (T : Subgroup G) ≤ F.H from F.invariant 1), Subgroup.map_sup]
    rfl
  rw [point_core_star_eq_image_core, hs, core_join_odd_eq_sylow_centralizer _ hp S']
  rfl

/-- The centralizer of the normal cubic has index two in the original star Sylow. -/
theorem point_core_star_index_two_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 := by
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hBH : B ≤ F.H := sup_le hLH hTH
  let f : B →* HStar F.H := (starMap F).comp (inclusion hBH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hBH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)
  have hrange : f.range = star F B := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion hBH b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b.val,hb⟩,rfl⟩
  have hratio := point_image_ratio_at h structural f hk
  have hRcard : Nat.card (star F (F.Ri L 1)) = Nat.card (pCore 2 (star F B)) := by
    rw [point_core_star_eq_image_core]
    exact card_map_of_injective (star F B).subtype_injective
  rw [hrange, ← hRcard] at hratio
  have hc := pointResidual_star_card_of_normal h structural hn
  let : (star F (F.Li L 1)).Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hthree : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have htwo : IsPGroup 2 (star F (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map (starMap F)
  have hBcard : Nat.card (star F B) = 3 * Nat.card (star F (T : Subgroup G)) := by
    change Nat.card (((B).subgroupOf F.H).map (starMap F)) = _
    rw [subgroupOf_sup hLH hTH, Subgroup.map_sup]
    change Nat.card (star F (F.Li L 1) ⊔ star F (T : Subgroup G) : Subgroup (HStar F.H)) = _
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal
        (hthree.disjoint_of_coprime htwo (by decide : Nat.Coprime 3 2)), hc]
  rw [hBcard] at hratio
  have hRT : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup (HStar F.H)) _ _ bot_le hRT
  simp only [relIndex_bot_left] at hindex
  have hpos := Nat.card_pos (α := star F (F.Ri L 1))
  nlinarith

/-- The actual point core centralizes the cubic image; no quotient model is chosen. -/
theorem point_core_star_centralizes_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    star F (F.Ri L 1) ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  rw [point_core_star_eq_centralizer_of_normal h structural hn]
  exact inf_le_right

/-- Source 14.7.5(5) on every literal U/V₁ section. -/
theorem point_generates_section_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    Representation.BinaryOffender.subspaceCommutator ρ ⊤ ((F.Li L 1).subgroupOf F.H) = ⊤ := by
  have ht : s.imageSpace F.U = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v, hv⟩ := s.onto (Multiplicative.ofAdd w)
    exact (s.mem_imageSpace_iff _ _).mpr ⟨v, v.property, congrArg Multiplicative.toAdd hv⟩
  have he := s.imageSpace_commutator (F.Li L 1) F.U
    (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right) le_rfl
  rw [commutator_comm, commutator_U_point_of_normal h hn, ht] at he
  exact he.symm

/-- The same generated section retains the literal star marking. -/
theorem point_generates_star_section_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ) :
    Representation.BinaryOffender.subspaceCommutator σ ⊤ (star F (F.Li L 1)) = ⊤ := by
  rw [Source.star, ← Representation.BinaryOffender.subspaceCommutator_comp_map, hσ]
  exact point_generates_section_of_normal h hn s

/-- The cubic generator is fixed-free on the literal section in the normal branch. -/
theorem exists_fixedFree_cubic_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ) :
    ∃ z : HStar F.H, orderOf z = 3 ∧ zpowers z = star F (F.Li L 1) ∧
      ∀ v, σ z v = v → v = 0 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hc := pointResidual_star_card_of_normal h structural hn
  let : IsCyclic (star F (F.Li L 1)) := isCyclic_of_prime_card hc
  obtain ⟨z,hz⟩ := (star F (F.Li L 1)).isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (star F (F.Li L 1)))
  refine ⟨z, ?_, hz, ?_⟩
  · rw [← Nat.card_zpowers, hz, hc]
  · apply CyclicFixedRank.fixedFree_of_commutator_eq_top σ z
    rw [hz]
    exact point_generates_star_section_of_normal h hn s σ hσ

/-- The actual reciprocal actor centralizes L₁* in the normal branch,
as in source 14.7.5(4). -/
theorem critical_actor_star_centralizes_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (c : CriticalPath (L := L) F) :
    star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  apply le_trans (map_mono (subgroupOf_mono F.H (critical_le_Ri_at h structural c)))
  exact point_core_star_centralizes_of_normal h structural hn

/-- Every point-core displacement has even binary rank in the normal-L₁ branch.
This is the no-transvection calculation in the proof of source 14.7.5(1). -/
theorem point_core_displacement_even_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha : (a : G) ∈ F.Ri L 1) :
    Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  obtain ⟨z,_,hz,hfix⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  let r := starMap F a
  have hr : r ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
    point_core_star_centralizes_of_normal h structural hn (mem_map_of_mem _ ha)
  let D : Subrepresentation (σ.comp (star F (F.Li L 1)).subtype) := {
    toSubmodule := (σ r - LinearMap.id).range
    apply_mem_toSubmodule g v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨σ g.val w, ?_⟩
      change σ r (σ g.val w) - σ g.val w = σ g.val (σ r w - w)
      rw [map_sub]
      have hc := congrArg (fun f : Module.End (ZMod 2) W => f w)
        ((show Commute g.val r from hr g.val g.property).map σ).eq
      simpa only [Module.End.mul_apply] using congrArg (fun v : W => v - σ g.val w) hc.symm }
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  have hd : D.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfix v.val (congrArg Subtype.val
      (hv ⟨z, hz ▸ (show z ∈ zpowers z from mem_zpowers z)⟩))
  have he := Representation.BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
    D.toRepresentation Nat.prime_three (by decide) hp hd
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at he
  have heq : σ r = ρ a := congrArg (fun τ : Representation (ZMod 2) F.H W => τ a) hσ
  change 2 ∣ Module.finrank (ZMod 2) (σ r - LinearMap.id).range at he
  rw [heq] at he
  exact even_iff_two_dvd.mpr he

/-- A point-core actor with commutators in an ambient line acts trivially on
U/V₁ in the normal-L₁ branch. This supplies the literal section calculation
needed for the subsequent critical-pair argument. -/
theorem point_actor_trivial_of_line_commutator_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2)
    (a : F.H) (ha : (a : G) ∈ A) : ρ a = 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hcard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : G)) he)))
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra hn
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
    omega
  have hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1 :=
    (Submodule.finrank_mono
      (s.displacement_range_le_imageSpace_of_commutator_le A C hc a ha)).trans hdim
  have he := point_core_displacement_even_of_normal h structural hn s a (hA ha)
  have hz : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 0 := by
    obtain ⟨n,hn⟩ := he
    omega
  have hz' : (ρ a - LinearMap.id).range = ⊥ := Submodule.finrank_eq_zero.mp hz
  exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp hz')

/-- Escape supplies the exact kernel of every literal binary section, using
the original 12.8.4 theorem rather than a residual-model assumption. -/
theorem section_action_kernel_eq_core_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ρ.ker = pCore 2 F.H := by
  let := h.chosen.elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have he : ρ.ker = (F.localTildeAction F.H le_rfl).ker := by
    ext a
    exact (s.action_mem_ker_iff a).trans
      (F.mem_localTildeAction_ker_iff F.H le_rfl a).symm
  rw [he]
  exact F.localKernel_eq_pCore h.source.simpleQTKE L (normalizer (L : Set G)) F.H
    (by decide) h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2 (((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural)))
    h.centralizer_L (F.H_mem_Hz (by decide) L (normalizer (L : Set G)) hescape)

/-- The normal cubic detects point-core actors in the literal two-core,
once the earlier-source escape has supplied the exact section kernel. -/
theorem point_actor_in_core_of_line_commutator_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  intro a ha
  have haH : a ∈ F.H := ((pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))) (hA ha)
  have he := point_actor_trivial_of_line_commutator_of_normal h structural hn s
    A C hA hc hC ⟨a,haH⟩ ha
  exact mem_map_of_mem F.H.subtype
    ((section_action_kernel_eq_core_of_escape h structural hescape s).le
      (show (⟨a,haH⟩ : F.H) ∈ ρ.ker from he))

/-- Source 14.7.5's even-displacement argument forces the reciprocal actor
to have nontrivial star image on the actual critical path. -/
theorem critical_star_nontrivial_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (c : CriticalPath (L := L) F) : star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Ri_at h structural c).trans
    ((pCoreIn_le 2 B).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap,
        QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      obtain ⟨a',ha',he⟩ := hαQ ha
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f := f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  have hAQ := point_actor_in_core_of_line_commutator_of_normal h structural hescape hn
    s A C hAR hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      (hAQ.trans_eq hQmap.symm))

/-- The normal-point branch constructs a genuine critical actor,
centralizing the original cubic and with nonzero original star image.
The only escape input is the full earlier 12.2.13 theorem. -/
theorem exists_critical_geometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath_at h hab (h.flag_escape_at F previous) structural
  exact ⟨c,critical_le_Ri_at h structural c,
    critical_star_nontrivial_of_point_normal h hab structural (h.flag_escape_at F previous) hn c,
    critical_actor_star_centralizes_of_point_normal h structural hn c⟩

/-- An abelian literal K/O₂(K) supplies the normality needed for the
preceding critical-pair construction. This does not exclude that branch. -/
theorem exists_critical_geometry_of_abelian_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F))) :
    ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
  exists_critical_geometry_of_point_normal h hab structural previous
    (pointResidual_normal_of_abelian_residual h structural ha)

/-- Apply the normal-point reductions to the literal star-normality
antecedent of 14.7.5. The source equality Q* = R₁* and the full residual
classification are separate obligations and are not asserted here. -/
theorem normal_point_structure_of_star_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hstar : (star F (F.Li L 1)).Normal) :
    Nat.card (star F (F.Li L 1)) = 3 ∧
      star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
        centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 ∧
      ⁅F.U,F.Li L 1⁆ = F.U ∧
      ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have hn := pointResidual_normal_of_star_normal h structural hstar
  exact ⟨pointResidual_star_card_of_normal h structural hn,
    point_core_star_eq_centralizer_of_normal h structural hn,
    point_core_star_index_two_of_normal h structural hn,
    commutator_U_point_of_normal h hn,
    exists_critical_geometry_of_point_normal h hab structural previous hn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The normal-point source reduction before residual classification

For the original point normalizer, normality of L₁ gives a cubic star image.
If O₂(H) centralized the flag plane, the earlier natural-action reduction
13.3.14(c) would put a nontrivial two-core in that cubic image. Thus the
plane is moved, and its commutator with O₂(H) is exactly the original point.
The full three-space marking then identifies QQ_H with R₁ and preserves
that identity under the literal star map.

The neighborhood-kernel argument in CriticalSelection constructs a reverse
critical path from any nontrivial original star actor. The normal-point
cubic supplies this nontriviality; choosing an orientation and applying the
exact original section kernel gives a quadratic two-offender, its actual
reciprocal index bound, and even displacement for every actor.

The applications discharge these local geometric inputs both under the
source's star-normality antecedent and when the actual K/O₂(K) is abelian.
The full earlier 12.2.13 escape and Structural1222 remain explicit. The
noncyclic solvable exclusions, larger-field reductions and component sieve
through 14.7.52 remain separate work in the same source assembly.

Source: Aschbacher–Smith, 13.3.14(c), pp.891–892; 14.7.4(1),(4),
14.7.5 and Notation 14.7.1, printed pp.1043–1044; F.9.16–17, pp.323–324.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem NormalPointReduction_core_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)

omit [Finite G] in
/-- The LT two-core lies in the point-parabolic two-core. -/
private theorem NormalPointReduction_core_product_Q_le_Ri (F : InvariantFlag T V 3) : Q T L ≤ F.Ri L 1 := by
  have hQ := NormalPointReduction_core_le_sylow (L ⊔ (T : Subgroup G)) le_sup_right
  have hle : Rechoice.group F L ≤ L ⊔ (T : Subgroup G) := Rechoice.group_le_LT
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle)

omit [Finite G] in
/-- The H two-core lies in the same point-parabolic two-core. -/
private theorem NormalPointReduction_core_product_QH_le_Ri (F : InvariantFlag T V 3) : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
  have hQ := NormalPointReduction_core_le_sylow F.H (F.invariant 1)
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)

/-- The original two-cores generate the point-parabolic two-core. -/
theorem core_product_of_plane_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 := by
  let J := L ⊔ (T : Subgroup G)
  let R := (F.Ri L 1).subgroupOf J
  let N := (F.H.pCoreIn 2).subgroupOf J
  let D := (F.Li L 1).subgroupOf J
  have hRJ : F.Ri L 1 ≤ J := (pCoreIn_le 2 _).trans Rechoice.group_le_LT
  have hNJ : F.H.pCoreIn 2 ≤ J := (NormalPointReduction_core_le_sylow F.H (F.invariant 1)).trans le_sup_right
  have hDJ : F.Li L 1 ≤ J := (F.Li_le L 1).trans (inf_le_left.trans le_sup_left)
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSourceAt.exists_marking h F structural
  have hkerMap : q.ker.map J.subtype = Q T L := by
    rw [hker, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT_at structural
  have hNle : N.map q ≤ Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [←hR]
    exact map_mono (subgroupOf_mono J (NormalPointReduction_core_product_QH_le_Ri F))
  have hn : D ≤ normalizer (N : Set J) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ F.H.pCoreIn 2 ↔
      (a : G) * (x : G) * (a : G)⁻¹ ∈ F.H.pCoreIn 2
    exact mem_normalizer_iff.mp
      ((F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
          ((F.Li_le L 1 ha).2)) _
  have hlarge : 2 < Nat.card (N.map q) := by
    by_contra hc
    have hDN := commutator_le_ker_of_normalized_image_card_le_two q D N hn (by omega)
    have hDNQ : ⁅F.Li L 1,F.H.pCoreIn 2⁆ ≤ Q T L := by
      have hh := map_mono (f := J.subtype) hDN
      rw [map_commutator, map_subgroupOf_eq_of_le hDJ,
        map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
      exact hh
    have hQV : Q T L ≤ centralizer (V : Set G) := by
      change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
      rw [← h.centralizer_LT_at structural]
      exact inf_le_right
    have hpoint : F.H ≤ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have h1 : ⁅⁅F.Li L 1,F.H.pCoreIn 2⁆,V⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hDNQ.trans hQV)
    have h2 : ⁅⁅F.H.pCoreIn 2,V⁆,F.Li L 1⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      have hp : ⁅F.H.pCoreIn 2,V⁆ ≤ F.Vi 1 := by
        rw [commutator_comm]
        exact (commutator_mono (le_conjugateSpanBy V F.H) le_rfl).trans hcomm
      exact hp.trans (le_centralizer_iff.mp ((F.Li_le L 1).trans (inf_le_right.trans hpoint)))
    have hz := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [← seed_commutator h F] at hz
    exact hmove ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (F.le_seed 2)))
  have hc : Nat.card (N.map q) = 4 := by
    have hd := card_dvd_of_le hNle
    rw [Matrix.PSL3Two.MarkedAutomorphisms.card_pointV] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card (N.map q) <;> norm_num [h] at *
  have he : N.map q = R.map q := by
    rw [hR]
    exact eq_of_le_of_card_ge hNle (by rw [hc, Matrix.PSL3Two.MarkedAutomorphisms.card_pointV])
  have hRN : R ≤ N ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (map_le_iff_le_comap).mp he.ge
  have hh := map_mono (f := J.subtype) hRN
  rw [map_subgroupOf_eq_of_le hRJ, Subgroup.map_sup, map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
  exact le_antisymm (sup_le (NormalPointReduction_core_product_Q_le_Ri F) (NormalPointReduction_core_product_QH_le_Ri F)) (by simpa [sup_comm] using hh)


/-- The literal star quotient kills Q_H and preserves the product identity. -/
theorem core_product_star_of_plane_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    star F (Q T L) = star F (F.Ri L 1) := by
  have he := congrArg (fun A : Subgroup G => star F A)
    (core_product_of_plane_movement h structural hcomm hmove)
  change ((Q T L ⊔ F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = _ at he
  rw [subgroupOf_sup (Q_le_H F) (pCoreIn_le 2 F.H), Subgroup.map_sup] at he
  have hz : ((F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = ⊥ := by
    change (((pCore 2 F.H).map F.H.subtype).comap F.H.subtype).map (starMap F) = ⊥
    rw [comap_map_eq_self_of_injective F.H.subtype_injective,
      Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk']
  simpa only [CriticalFusion.Source.star,hz,sup_bot_eq] using he


/-- The normal cubic image has trivial two-core, contradicting reduction
13.3.14(c) if the original H-core centralized the original plane. -/
theorem plane_moved_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  have hne := Chapter13.Section03.Noncentrality.linearThree_star_core_ne_bot_of_plane_centralized
    h F (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have he : Chapter13.Section03.Noncentrality.star F.H (F.Li L 1)
      ((F.Li_le L 1).trans inf_le_right) = star F (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact mem_map_of_mem (starMap F) a.property
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [he] at hne
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  apply hne
  exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot)

/-- Source 14.7.5(2), with the literal two-cores and no recognition datum. -/
theorem core_product_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧ star F (Q T L) = star F (F.Ri L 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hc : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact section_core_commutator_le_point h s
  have hm := plane_moved_of_point_normal h structural hn
  exact ⟨core_product_of_plane_movement h structural hc hm,
    core_product_star_of_plane_movement h structural hc hm⟩

/-- The normal-point branch supplies the selected critical pair of
Notation 14.7.1, preserving the original actor and reciprocal core. -/
theorem exists_selected_critical_geometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  obtain ⟨c,_,hc,_⟩ := exists_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha⟩ := select_critical_orientation_of_nontrivial_star_at h structural c hc
  exact ⟨a,ha,critical_le_Ri_at h structural a,
    critical_star_nontrivial_of_point_normal h hab structural (h.flag_escape_at F previous) hn a,
    critical_actor_star_centralizes_of_point_normal h structural hn a⟩
open Representation.BinaryOffender
variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- The normal-point branch constructs an actual quadratic two-offender,
using the original quotient, the literal index and exact centralizer kernel. -/
theorem exists_selected_critical_action_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
      fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
      ∀ a : F.H, (a : G) ∈ c.Uα →
        Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) ∧
        Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  obtain ⟨c,hs,hplace,hne,hcent⟩ :=
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hb := critical_fixedCodim_bounds_of_kernel_at h hab structural
    (section_action_kernel_eq_core_of_escape h structural (h.flag_escape_at F previous) s) s c
  refine ⟨c,hs,hplace,hne,hcent,critical_quadratic h hab s c,?_,?_⟩
  · have hh := hb.1
    have hr := hs.comparison
    omega
  · intro a ha
    exact ⟨point_core_displacement_even_of_normal h structural hn s a (hplace ha),hb.2 a ha⟩

/-- Source 14.7.4(1) in the normal-point branch, on the actual plane. -/
theorem plane_core_commutator_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hc : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact section_core_commutator_le_point h s
  have hle : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≤ F.Vi 1 :=
    (commutator_mono ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) le_rfl).trans hc
  have hne : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    exact plane_moved_of_point_normal h structural hn
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  apply eq_of_le_of_card_ge hle
  rw [show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)]
  exact (one_lt_card_iff_ne_bot _).mpr hne

/-- Apply all the normal-point reductions to source 14.7.5's literal
star-normality antecedent. These are the source clauses at the original G₁. -/
theorem normal_point_source_structure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hstar : (star F (F.Li L 1)).Normal) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 ∧
      Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧
      Nat.card (star F (F.Li L 1)) = 3 ∧
      star F (Q T L) = star F (F.Ri L 1) ∧
      star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
        centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 ∧
      ⁅F.U,F.Li L 1⁆ = F.U ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have hn := pointResidual_normal_of_star_normal h structural hstar
  have hp := core_product_of_point_normal h hab structural hn
  exact ⟨plane_core_commutator_of_point_normal h hab structural hn, hp.1,
    pointResidual_star_card_of_normal h structural hn, hp.2,
    point_core_star_eq_centralizer_of_normal h structural hn,
    point_core_star_index_two_of_normal h structural hn,
    commutator_U_point_of_normal h hn,
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn⟩

/-- In the abelian-residual branch the actual section receives the normal
point cubic, the radical product, and the selected quadratic two-offender.
No cyclicity or final residual model is assumed. -/
theorem abelian_residual_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F)))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 ∧
      Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧
      star F (Q T L) = star F (F.Ri L 1) ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
        IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
        fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
        ∀ a : F.H, (a : G) ∈ c.Uα →
          Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) ∧
          Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
            Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  have hn := pointResidual_normal_of_abelian_residual h structural ha
  have hp := core_product_of_point_normal h hab structural hn
  exact ⟨plane_core_commutator_of_point_normal h hab structural hn, hp.1, hp.2,
    exists_selected_critical_action_of_point_normal h hab structural previous hn s⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Rank-one critical pairs in the normal-point branch

Assume the original L₁ is normal in H and the image R₁* has two-rank at
most one. The elementary selected critical actor then has order two, and
the reciprocal core index is two. The normal cubic makes every nonzero
actor displacement even; the critical bound therefore makes it exactly
two. Applying this on both orientations identifies both point commutators.
It also gives an order-eight full commutator and disjoint original and
reciprocal points. A bounded-image commutator argument then gives the exact
indices of the literal centralizer C_U(Uα).

The final application constructs its section and selected path from the
original flag. It retains normality and the rank bound as explicit local
antecedents: the residual classification deriving these from the
extraspecial branch is not supplied here. In particular, these results do
not assert all of 14.7.16, identify the full commutator with V, or complete
the solvable exclusion or the classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.15(1),(2), 14.7.16(6), Remark 14.7.17 and
the commutator and centralizer arguments in 14.7.16–18, printed pp.1047–1048.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- An order-two critical image forces the selected reciprocal index to be two. -/
theorem selected_critical_indices_of_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (F.U ⊓ c.Qα).relIndex F.U = 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient
    ((F.U ⊓ c.Qα).subgroupOf F.U) |>.exists_card_eq
  change (F.U ⊓ c.Qα).relIndex F.U = 2 ^ n at hn
  have hp := hs.positive
  have hb := hs.comparison
  rw [hn,Nat.log_pow Nat.one_lt_two] at hp hb
  rw [ha] at hb
  norm_num at hb
  have : n = 1 := by omega
  simpa only [this,pow_one] using hn

/-- The selected actor has order two when the point-parabolic star core has two-rank at most one. -/
theorem critical_card_two_of_point_core_rank_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (hr : primeRank 2 (star F (F.Ri L 1)) ≤ 1) :
    Nat.card (star F c.Uα) = 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (c.Uα.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((critical_le_Q_at h structural c).trans (Q_le_H F))
  let : IsElementaryAbelian 2 (star F c.Uα) := IsElementaryAbelian.map (starMap F)
  have hle : star F c.Uα ≤ star F (F.Ri L 1) :=
    map_mono (comap_mono (critical_le_Ri_at h structural c))
  have hb : primeRank 2 (star F c.Uα) ≤ 1 := (primeRank_mono 2 hle).trans hr
  have hpos := (one_lt_card_iff_ne_bot _).mpr (c.star_ne_bot hs)
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) (star F c.Uα)] at hpos ⊢
  have : primeRank 2 (star F c.Uα) = 1 := by
    have hn : primeRank 2 (star F c.Uα) ≠ 0 := by
      intro hz
      simp only [hz,pow_zero,lt_self_iff_false] at hpos
    omega
  rw [this,pow_one]

/-- Every nontrivial selected actor has displacement exactly two on the literal section. -/
theorem critical_displacement_two_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (a : F.H) (haA : (a : G) ∈ c.Uα) (haQ : a ∉ pCore 2 F.H) :
    Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := section_action_kernel_eq_core_of_escape h structural hescape s
  have hb := (critical_fixedCodim_bounds_of_kernel_at h hab structural hk s c).2 a haA
  rw [selected_critical_indices_of_card_two h hab c hs ha] at hb
  norm_num at hb
  have he := point_core_displacement_even_of_normal h structural hn s a
    (critical_le_Ri_at h structural c haA)
  have hne : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≠ 0 := by
    intro hz
    have he : ρ a = 1 := sub_eq_zero.mp
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    exact haQ (hk ▸ (show a ∈ ρ.ker from he))
  obtain ⟨k,hk⟩ := he
  omega

/-- The reciprocal core intersection has commutator exactly the reciprocal point. -/
theorem critical_intersection_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := section_action_kernel_eq_core_of_escape h structural hescape s
  have hle : ⁅F.U ⊓ c.Qα,c.Uα⁆ ≤ c.Zα :=
    (commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator_le_point h s c)
  have hcard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge hle
  rw [hcard]
  apply (one_lt_card_iff_ne_bot _).mpr
  intro hz
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdim := critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ
  have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
    intro v hv
    apply sub_eq_zero.mpr
    exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
      (by rw [commutator_comm,hz]; exact bot_le) a haA v hv
  have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα :=
    le_inf ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
      (point_le_reciprocal_core_of_kernel_at h structural hk s c)
  have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
    (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
  have hb := Submodule.finrank_mono hfix
  have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
  omega


/-- Reversing the selected pair recovers the original point as a commutator. -/
theorem critical_reverse_intersection_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 := by
  have hAH := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot_at h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q_at h structural r.path).trans (Q_le_H F))]
    exact selected_critical_indices_of_card_two h hab c hs ha
  have hrSel : r.path.RankSelection :=
    ⟨critical_index_positive r.path,by
      rw [r.reverse_index_of_placement hAH,ha,hrCard]⟩
  have he := congrArg (fun B : Subgroup G => conjugate B r.conjugator)
    (critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s r.path hrSel hrCard)
  have hm (A B : Subgroup G) : conjugate ⁅A,B⁆ r.conjugator =
      ⁅conjugate A r.conjugator,conjugate B r.conjugator⁆ := map_commutator _ _ _
  rw [hm,conjugate_inf,r.base_U,r.tip_core,r.tip_U,r.tip_point] at he
  exact he

/-- The full critical commutator has image of dimension two in the original section. -/
theorem critical_commutator_image_rank_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,c.Uα⁆) = 2 := by
  have hAH := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hz : zpowers (x : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card ha hx)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have ht : s.imageSpace F.U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨y,hy⟩ := s.onto (Multiplicative.ofAdd v)
    exact (s.mem_imageSpace_iff _ _).mpr ⟨y,y.property,congrArg Multiplicative.toAdd hy⟩
  rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,ht,←hσ,
    subspaceCommutator_comp_map]
  change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 2
  rw [←hz,CyclicFixedRank.commutator_eq_range,←he]
  change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range = 2
  rw [hσ]
  exact critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ

/-- The full critical commutator has order eight, including the original point. -/
theorem critical_commutator_card_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hpoint : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_reverse_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
      commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have hCU : ⁅F.U,c.Uα⁆ ≤ F.U := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans s.normalized)
  have he := s.imageSpace_card_eq_relIndex ⁅F.U,c.Uα⁆ hCU
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    critical_commutator_image_rank_of_normal_card_two h hab structural hescape hn s c hs ha] at he
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) ⁅F.U,c.Uα⁆ bot_le hpoint
  rw [relIndex_bot_left,relIndex_bot_left,←he] at hc
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  norm_num [hp] at hc
  exact hc.symm


/-- The ambient centralizer bound follows from the exact original kernel. -/
theorem centralizer_U_le_core_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 := by
  intro x hx
  have hxH : x ∈ F.H :=
    (Subgroup.centralizer_le_normalizer _) (centralizer_le s.kernel_le hx)
  let a : F.H := ⟨x,hxH⟩
  have hk : a ∈ ρ.ker := by
    apply (s.action_mem_ker_iff a).mpr
    intro v hv
    have he : ⁅x,v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hx v hv).symm
    exact he ▸ (F.Vi 1).one_mem
  rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
  exact mem_map_of_mem F.H.subtype hk

/-- The original and reciprocal points are distinct and have trivial intersection. -/
theorem critical_points_disjoint_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) : Disjoint (F.Vi 1) c.Zα := by
  have hnle : ¬ c.Zα ≤ F.Vi 1 := by
    intro hle
    let A := star F c.Uα
    let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
    obtain ⟨x,hx⟩ := exists_ne (1 : A)
    obtain ⟨a,haA,he⟩ := x.property
    have haQ : a ∉ pCore 2 F.H := by
      intro hq
      apply hx
      apply Subtype.ext
      rw [←he]
      exact (QuotientGroup.eq_one_iff _).mpr hq
    have hd := critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ
    let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
      (Multiplicative.toAdd.surjective.comp s.onto)
    have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
      intro v hv
      apply sub_eq_zero.mpr
      exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
        (by rw [commutator_comm,critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha]; exact hle)
        a haA v hv
    have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα := le_inf s.kernel_le
      (point_le_reciprocal_core_of_kernel_at h structural
        (section_action_kernel_eq_core_of_escape h structural hescape s) s c)
    have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
      (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
    have hb := Submodule.finrank_mono hfix
    have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
    omega
  have hzCard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply disjoint_iff.mpr
  by_contra hb
  have hlo := (one_lt_card_iff_ne_bot _).mpr hb
  have he : F.Vi 1 ⊓ c.Zα = c.Zα := eq_of_le_of_card_ge inf_le_right (by omega)
  exact hnle (he ▸ (inf_le_left : F.Vi 1 ⊓ c.Zα ≤ F.Vi 1))

/-- The two reciprocal core intersections commute. -/
theorem critical_intersection_centralizes_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ := by
  have h₁ : ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_right inf_le_left).trans (section_core_commutator_le_point h s)
  have h₂ : ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ ≤ c.Zα :=
    (commutator_mono inf_le_right inf_le_left).trans (reciprocal_core_commutator_le_point h s c)
  exact le_bot_iff.mp ((le_inf h₁ h₂).trans
    (critical_points_disjoint_of_normal_card_two h hab structural hescape hn s c hs ha).le_bot)

/-- The actual centralizer has index two in the reciprocal intersection and index four in U. -/
theorem critical_centralizer_indices_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  let := hab
  let D := F.U ⊓ c.Qα
  let A := c.Uα ⊓ F.H.pCoreIn 2
  let C := F.U ⊓ centralizer (c.Uα : Set G)
  have hcc : centralizer (c.Uα : Set G) ≤ c.Qα := by
    have he : conjugate (centralizer (F.U : Set G)) c.conjugator = centralizer (c.Uα : Set G) := by
      apply le_antisymm
      · exact map_centralizer_le_centralizer_image _ _
      · intro x hx
        refine ⟨(MulAut.conj c.conjugator) x, ?_, by simp [MulAut.conj_apply,mul_assoc]⟩
        intro a ha
        apply (MulAut.conj c.conjugator⁻¹).injective
        simpa [map_mul,MulAut.conj_apply,mul_assoc] using
          hx ((MulAut.conj c.conjugator⁻¹) a) (mem_map_of_mem _ ha)
    rw [←he]
    exact (map_mono (centralizer_U_le_core_of_escape h structural hescape s)).trans_eq
      (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective)
  have hCD : C ≤ D := inf_le_inf_left _ hcc
  have hz : ⁅D,c.Uα⁆ = c.Zα :=
    critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha
  have hZA : c.Zα ≤ D := by
    let := h.chosen.elementary
    let := elementary_U F
    have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
      (IsElementaryAbelian.isPGroup 2 F.U) s.section_le s.normalized
    refine le_inf ?_ ?_
    · rw [←hz]
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans s.normalized))
    · exact (map_mono (s.kernel_le.trans hUQ)).trans_eq
        (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective)
  have hzCard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hi : A.relIndex c.Uα = 2 := by
    rw [show A = F.H.pCoreIn 2 ⊓ c.Uα from inf_comm _ _]
    rw [CriticalIntersections.core_intersection_index_eq_star_card c.Uα
      ((critical_le_Q_at h structural c).trans (Q_le_H F)),ha]
  have hcent : A ≤ centralizer (D : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (critical_intersection_centralizes_of_normal_card_two h hab structural hescape hn s c hs ha))
  let : IsMulCommutative D := le_centralizer_iff_isMulCommutative.mp
    (inf_le_left.trans (F.U.le_centralizer.trans (centralizer_le inf_le_left)))
  obtain ⟨B,hBD,hcard,hBfix⟩ := exists_large_subgroup_commutator_le_of_index_two
    D D c.Uα A ⊥ c.Zα le_rfl inferInstance hZA hz.le inf_le_left hcent hi
  have hBC : B ≤ C := le_inf (hBD.trans inf_le_left)
    (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hBfix))
  rw [relIndex_bot_left,hzCard] at hcard
  have hb : Nat.card D ≤ 2 * Nat.card C := hcard.trans (Nat.mul_le_mul_left 2 (card_le_of_le hBC))
  have hci : C.relIndex D = 2 := by
    have hc := relIndex_mul_card_of_le hCD
    have hp : 0 < Nat.card C := Nat.card_pos
    have hpos : C.relIndex D ≠ 0 := (C.subgroupOf D).index_ne_zero_of_finite
    have hne : C.relIndex D ≠ 1 := by
      intro he
      have hfix : ⁅D,c.Uα⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        ((relIndex_eq_one.mp he).trans inf_le_right)
      rw [hz] at hfix
      rw [hfix,card_bot] at hzCard
      omega
    have hge : 2 ≤ C.relIndex D := by omega
    have hle : C.relIndex D ≤ 2 := by nlinarith
    omega
  refine ⟨hci,?_⟩
  have ht := relIndex_mul_relIndex C D F.U hCD inf_le_left
  rw [hci,selected_critical_indices_of_card_two h hab c hs ha] at ht
  exact ht.symm

/-- Apply the rank-one geometry to the original normal point normalizer.
The local antecedents are exactly normality from 14.7.15(1) and the
rank-one consequence of 14.7.15(2); the literal section, selected path
and displayed critical-pair conclusions are constructed here. -/
theorem normal_point_rank_one_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hr : primeRank 2 (star F (F.Ri L 1)) ≤ 1) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
      ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
      Disjoint (F.Vi 1) c.Zα ∧
      ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
      Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨c,hs,hplace,_,_⟩ :=
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have ha := critical_card_two_of_point_core_rank_one h hab structural c hs hr
  have hescape := h.flag_escape_at F previous
  exact ⟨c,hs,hplace,ha,selected_critical_indices_of_card_two h hab c hs ha,
    critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_reverse_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_points_disjoint_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_intersection_centralizes_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_commutator_card_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_centralizer_indices_of_normal_card_two h hab structural hescape hn s c hs ha⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The six-dimensional section in the normal extraspecial residual branch

Assume the actual K/O₂(K) is extraspecial of order 27 and L₁ is normal in
H. The canonical residual comparison identifies L₁* with the cubic center
of O²(H/O₂(H)). Each elementary subgroup of R₁* acts faithfully on that
residual and fixes its center, so R₁* has two-rank at most one. This removes
the rank premise of NormalPointRankOne and makes the selected actor's
nonzero displacement exactly two.

On any literal U/V₁ conjugation section, the original kernel theorem gives
a faithful star action and the cubic center has zero fixed space. The
small-involution calculation forces binary dimension six and irreducibility
on the actual residual. The original-group application starts with the
literal Heisenberg isomorphism, constructs its section and selected path,
and proves |U| = 128 together with the earlier exact critical geometry.

Normality from 14.7.15(1) remains an explicit premise to be obtained from
the ambient source hypotheses in this task. This module proves the module
step of 14.7.16 under that premise; it does not assert the extraspecial
exclusion 14.7.14 or the residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.15–17, printed pp.1047–1048.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialBranch_point_star_le_residual : star F (F.Li L 1) ≤ pResidual 2 (HStar F.H) := by
  have hh : (F.Li L 1).subgroupOf F.H ≤ pResidual 2 F.H := by
    rw [← residual_subgroupOf F]
    exact subgroupOf_mono F.H (pointResidual_le F)
  exact (map_mono hh).trans (map_pResidual_le 2 (starMap F))

/-- The normal point cubic is exactly the embedded center of the actual star residual. -/
theorem point_star_eq_residual_center_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F))) :
    star F (F.Li L 1) = (center (pResidual 2 (HStar F.H))).map
      (pResidual 2 (HStar F.H)).subtype := by
  let P := pResidual 2 (HStar F.H)
  let Z := star F (F.Li L 1)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZP : Z ≤ P := ExtraspecialBranch_point_star_le_residual
  have hc : Nat.card (Z.subgroupOf P) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv]
    exact pointResidual_star_card_of_normal h structural hn
  have he : Z.subgroupOf P = center P := eq_of_le_of_card_ge
    ((IsExtraspecial.isPGroup 3 P).normal_le_center_of_card_dvd_prime _ (by rw [hc]))
    (by rw [hc,IsExtraspecial.center_order_p 3 P])
  have hm := congrArg (Subgroup.map P.subtype) he
  rwa [map_subgroupOf_eq_of_le hZP] at hm

private theorem ExtraspecialBranch_residual_actor_faithful
    {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥) (hodd : Odd (Nat.card (pResidual 2 D)))
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (pResidual 2 D)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (pResidual 2 D : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot hcore hc
  have hdis : Disjoint A (pResidual 2 D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hz := hdis.le_bot ⟨a.property,hp⟩
  exact Subtype.ext (mem_bot.mp hz)

/-- The normal extraspecial branch supplies the rank bound used by the critical geometry. -/
theorem point_core_rank_one_of_normal_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let R := star F (F.Ri L 1)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := ExtraspecialBranch_residual_actor_faithful
    (pCore_quotient_pCore_eq_bot 2) (by rw [hP]; decide) A (IsElementaryAbelian.isPGroup 2 A)
  have hcenter : ∀ a : A, ∀ z ∈ center P, f a z = z := by
    intro a z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem P.subtype hz
    have hc := point_core_star_centralizes_of_normal h structural hn
      (map_subtype_le E a.property)
    change (a : HStar F.H) * (z : HStar F.H) * (a : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  have hb := MulAut.elementary_two_center_preserving_card_le_two hP f hf hcenter
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb

/-- The selected critical actor has order two, with no separate rank premise. -/
theorem critical_card_two_of_normal_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 :=
  critical_card_two_of_point_core_rank_one h hab structural c hs
    (point_core_rank_one_of_normal_extraspecial_residual h structural hn hex hcard)


variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- Every literal section has a faithful star action and an irreducible residual action of binary degree six. -/
theorem normal_extraspecial_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hescape := h.flag_escape_at F previous
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by
      rw [←hσ]
      exact hx
    rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have hfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥ := by
    obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply hfree w
    have hzm : z ∈ (center P).map P.subtype := by
      rw [←point_star_eq_residual_center_of_normal h structural hn hex,←hgen]
      exact mem_zpowers z
    obtain ⟨z,hzc,rfl⟩ := hzm
    exact hw ⟨z,hzc⟩
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hx2 : (x : HStar F.H) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfaith := ExtraspecialBranch_residual_actor_faithful (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A hA2
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact hx (hfaith (he.trans (map_one _).symm))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem P.subtype hz
    have hc := critical_actor_star_centralizes_of_point_normal h structural hn c x.property
    change (x : HStar F.H) * (z : HStar F.H) * (x : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdisp := critical_displacement_two_of_normal_card_two
    h hab structural hescape hn s c hs hA a haA haQ
  have hsmall : fixedCodim σ (zpowers (x : HStar F.H)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank,←he]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 2
    rw [hσ,hdisp]
  exact ⟨σ,hσ,hf,ExtraspecialBinarySix.six_and_irreducible_of_small_involution σ hf P hP hfix x hx2 hne hcenter hsmall⟩

/-- Apply the extraspecial module and critical geometry to the original flag.
The residual is identified by an actual isomorphism; only point normality
from 14.7.15(1) remains beyond the earlier source inputs. -/
theorem normal_extraspecial_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Nat.card F.U = 128 ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
        ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
        ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
        Disjoint (F.Vi 1) c.Zα ∧
        ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
        Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,_,_,hdim,_⟩ := normal_extraspecial_section h hab structural previous hn hex hcard s
  have hUcard := s.card_section
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),Nat.card_zmod,hdim,
    show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)] at hUcard
  refine ⟨hUcard,?_⟩
  exact normal_point_rank_one_source_reduction h hab structural previous hn
    (point_core_rank_one_of_normal_extraspecial_residual h structural hn hex hcard)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Point normality in the original extraspecial residual branch

The point cubic has order three and is centralized by R₁* before any point
normality is assumed. Faithful action on the extraspecial residual therefore
bounds the two-rank of R₁* by one. Cubic displacement excludes transvections
on the literal U/V₁ section, so critical reciprocity supplies a nontrivial
selected involution. It moves at most two dimensions, hence fixes the residual
center. Its fixed subgroup in the residual is exactly that center; since it
also fixes the point cubic, the two cubics coincide. Relative normality in H
then follows through the original star map.

The application starts with the actual Heisenberg isomorphism and discharges
the point-normality premise of ExtraspecialBranch. It yields the faithful
irreducible six-dimensional section, |U| = 128, and reciprocal critical
geometry from the original flag and the named earlier-source inputs.
The subsequent extraspecial exclusion 14.7.14 and residual classification
through 14.7.52 remain separate mathematical obligations in this task.

Source: Aschbacher–Smith, 14.7.15(1) and 14.7.16, printed pp.1047–1048.
The argument uses the faithful section as an alternative to the source's
initial central-cubic placement argument.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

omit [Finite G] in
private theorem ExtraspecialPointNormality_point_star_le_residual' : star F (F.Li L 1) ≤ pResidual 2 (HStar F.H) := by
  have hh : (F.Li L 1).subgroupOf F.H ≤ pResidual 2 F.H := by
    rw [←residual_subgroupOf F]
    exact subgroupOf_mono F.H (pointResidual_le F)
  exact (map_mono hh).trans (map_pResidual_le 2 (starMap F))

/-- An odd three-residual gives the actual point image order three, without normality. -/
theorem point_star_card_of_three_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hp : IsPGroup 3 (pResidual 2 (HStar F.H))) :
    Nat.card (star F (F.Li L 1)) = 3 := by
  let A := (F.Li L 1).subgroupOf F.H
  let f := (starMap F).subgroupMap A
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,starMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hA3 : IsPGroup 3 (star F (F.Li L 1)) := hp.to_le ExtraspecialPointNormality_point_star_le_residual'
  have hc : pCore 2 (star F (F.Li L 1)) = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hA3.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hcard : Nat.card (A ⧸ pCore 2 A) = 3 := by
    let e : A ≃* F.Li L 1 := subgroupOfEquivOfLe
      (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have he := Nat.card_congr (f.pCoreQuotientEquiv
    ((starMap F).subgroupMap_surjective A) hk).toEquiv
  change Nat.card (A ⧸ pCore 2 A) = Nat.card
    ((star F (F.Li L 1)) ⧸ pCore 2 (star F (F.Li L 1))) at he
  rw [hc,Nat.card_congr QuotientGroup.quotientBot.toEquiv,hcard] at he
  exact he.symm

/-- The point core centralizes the cubic image inside an odd three-residual. -/
theorem point_core_centralizes_of_three_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hp : IsPGroup 3 (pResidual 2 (HStar F.H))) :
    star F (F.Ri L 1) ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let R := star F (F.Ri L 1)
  let A := star F (F.Li L 1)
  have hn : B ≤ normalizer (F.Li L 1 : Set G) :=
    sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁_at h structural)
  have hcomm : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Li L 1 :=
    le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 B).trans hn)
  have hcommR : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Ri L 1 := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((show F.Li L 1 ≤ B from le_sup_left).trans
        ((show B ≤ normalizer (B : Set G) from Subgroup.le_normalizer).trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))))
  have hrel : ⁅(F.Ri L 1).subgroupOf F.H,(F.Li L 1).subgroupOf F.H⁆ ≤
      (F.Ri L 1).subgroupOf F.H ⊓ (F.Li L 1).subgroupOf F.H := by
    intro x hx
    have hm := mem_map_of_mem F.H.subtype hx
    rw [map_commutator,subgroupOf_map_subtype,subgroupOf_map_subtype] at hm
    have hm' := (commutator_mono inf_le_left inf_le_left) hm
    exact ⟨hcommR hm',hcomm hm'⟩
  have hRA : ⁅R,A⁆ ≤ R ⊓ A := by
    change ⁅((F.Ri L 1).subgroupOf F.H).map (starMap F),
      ((F.Li L 1).subgroupOf F.H).map (starMap F)⁆ ≤ _
    rw [←map_commutator]
    exact le_inf (map_mono (hrel.trans inf_le_left)) (map_mono (hrel.trans inf_le_right))
  have hd : Disjoint R A := (isPGroup_pCoreIn 2 B).comap_subtype.map (starMap F)
    |>.disjoint_of_coprime (hp.to_le ExtraspecialPointNormality_point_star_le_residual') (by decide : Nat.Coprime 2 3)
  exact commutator_eq_bot_iff_le_centralizer.mp (bot_unique (hRA.trans hd.le_bot))

private theorem ExtraspecialPointNormality_residual_actor_faithful'
    {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥) (hodd : Odd (Nat.card (pResidual 2 D)))
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (pResidual 2 D)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (pResidual 2 D : Set D) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot hcore hc
  have hdis : Disjoint A (pResidual 2 D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨a.property,hp⟩))

/-- The extraspecial residual bounds the point core rank before point normality is known. -/
theorem point_core_rank_one_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  let X := (star F (F.Li L 1)).subgroupOf P
  have hX : Nat.card X = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ExtraspecialPointNormality_point_star_le_residual').toEquiv]
    exact point_star_card_of_three_residual h structural (IsExtraspecial.isPGroup 3 P)
  let R := star F (F.Ri L 1)
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := ExtraspecialPointNormality_residual_actor_faithful' (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A (IsElementaryAbelian.isPGroup 2 A)
  have hfix : ∀ a : A, ∀ x ∈ X, f a x = x := by
    intro a x hx
    apply Subtype.ext
    have hc := point_core_centralizes_of_three_residual h structural
      (IsExtraspecial.isPGroup 3 P) (map_subtype_le E a.property)
    change (a : HStar F.H)*(x : HStar F.H)*(a : HStar F.H)⁻¹=x
    rw [←hc x hx,mul_inv_cancel_right]
  have hb := MulAut.elementary_two_cubic_fixer_card_le_two hP f hf X hX hfix
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb
private theorem ExtraspecialPointNormality_extraspecial_actor_trivial_of_line_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A]
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2)
    (a : F.H) (ha : (a : G) ∈ A) : ρ a = 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have himageCard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : G)) he)))
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at himageCard
    by_contra hn
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
    omega
  have hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1 :=
    (Submodule.finrank_mono
      (s.displacement_range_le_imageSpace_of_commutator_le A C hc a ha)).trans hdim
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 := by
    rw [←Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F),hexp]
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have ht : starMap F a ^ 2 = 1 := by
    rw [←map_pow]
    have he : (a : G)^2=1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a,ha⟩ : A))
    rw [show a^2=1 from Subtype.ext he,map_one]
  have hs : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 1
    rwa [hσ]
  have he := Representation.ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP heP
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    (starMap F a) ht hs
  rw [←hσ]
  change σ (starMap F a) = 1
  rw [he,map_one]

private theorem ExtraspecialPointNormality_extraspecial_actor_in_core_of_line_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  intro a ha
  have haH : a ∈ F.H := ((pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))) (hA ha)
  have he := ExtraspecialPointNormality_extraspecial_actor_trivial_of_line_commutator h structural hescape hex hcard hexp s
    A C hc hC ⟨a,haH⟩ ha
  exact mem_map_of_mem F.H.subtype
    ((section_action_kernel_eq_core_of_escape h structural hescape s).le
      (show (⟨a,haH⟩ : F.H) ∈ ρ.ker from he))

/-- Source 14.7.5's even-displacement argument forces the reciprocal actor
to have nontrivial star image on the actual critical path. -/
theorem critical_star_nontrivial_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) : star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Ri_at h structural c).trans
    ((pCoreIn_le 2 B).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap,
        QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      obtain ⟨a',ha',he⟩ := hαQ ha
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f := f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hAQ := ExtraspecialPointNormality_extraspecial_actor_in_core_of_line_commutator h structural hescape hex hcard hexp
    s A C hAR hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      (hAQ.trans_eq hQmap.symm))


/-- The actual extraspecial residual forces relative point normality. -/
theorem pointResidual_normal_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hescape := h.flag_escape_at F previous
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath_at h hab hescape structural
  obtain ⟨c,hs⟩ := select_critical_orientation_of_nontrivial_star_at h structural c
    (critical_star_nontrivial_of_extraspecial_residual h hab structural hescape hex hcard hexp c)
  have hA := critical_card_two_of_point_core_rank_one h hab structural c hs
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨t,htne⟩ := exists_ne (1 : A)
  have ht2 : (t : HStar F.H)^2=1 := by
    have he := pow_card_eq_one' (x := t)
    rw [hA] at he
    exact congrArg Subtype.val he
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hkernel := section_action_kernel_eq_core_of_escape h structural hescape s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [hkernel] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  obtain ⟨a,ha,he⟩ := t.property
  have hsmall : fixedCodim σ (zpowers (t : HStar F.H)) ≤ 2 := by
    have hb := (critical_fixedCodim_bounds_of_kernel_at h hab structural hkernel s c).2 a ha
    rw [selected_critical_indices_of_card_two h hab c hs hA] at hb
    norm_num at hb
    rw [fixedCodim_zpowers_eq_displacement_rank,←he]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 2
    rwa [hσ]
  have hcenter := Representation.ExtraspecialBinarySix.small_actor_fixes_extraspecial_center
    σ hf P hP t hsmall
  have hfaith := ExtraspecialPointNormality_residual_actor_faithful' (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A (IsPGroup.of_card (n := 1) (by simpa using hA))
  have hne : (MulAut.conjNormal (t : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact htne (hfaith (he.trans (map_one _).symm))
  have hinv : Function.Involutive (MulAut.conjNormal (t : HStar F.H) : MulAut P) := by
    intro x
    have he : (MulAut.conjNormal (t : HStar F.H) : MulAut P)^2=1 := by
      rw [←map_pow,ht2,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hfixed := MulAut.fixed_eq_center_of_extraspecial27_involution hP
    (MulAut.conjNormal (t : HStar F.H)) hinv hne hcenter
  have hle : star F (F.Li L 1) ≤ (center P).map P.subtype := by
    intro x hx
    let xP : P := ⟨x,ExtraspecialPointNormality_point_star_le_residual' hx⟩
    have hxP : xP ∈ center P := by
      rw [←hfixed]
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      have htR : (t : HStar F.H) ∈ star F (F.Ri L 1) :=
        (map_mono (subgroupOf_mono F.H (critical_le_Ri_at h structural c))) t.property
      have hc := point_core_centralizes_of_three_residual h structural
        (IsExtraspecial.isPGroup 3 P) htR x hx
      change (t : HStar F.H)*x*(t : HStar F.H)⁻¹=x
      rw [←hc,mul_inv_cancel_right]
    exact mem_map_of_mem P.subtype hxP
  have heq : star F (F.Li L 1) = (center P).map P.subtype :=
    eq_of_le_of_card_ge hle (by
      rw [point_star_card_of_three_residual h structural (IsExtraspecial.isPGroup 3 P),
        card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P])
  apply pointResidual_normal_of_star_normal h structural
  rw [heq]
  infer_instance

/-- The embedded point cubic is the actual residual center, with no normality premise. -/
theorem point_star_eq_center_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    star F (F.Li L 1) = (center (pResidual 2 (HStar F.H))).map
      (pResidual 2 (HStar F.H)).subtype :=
  point_star_eq_residual_center_of_normal h structural
    (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp) hex

/-- Apply the proved point normality to any literal binary section, retaining its star map. -/
theorem extraspecial_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) :=
  normal_extraspecial_section h hab structural previous
    (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp)
    hex hcard s

/-- The original extraspecial branch now discharges the point-normality premise. -/
theorem extraspecial_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).subgroupOf F.H).Normal ∧
    Nat.card F.U = 128 ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
        ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
        ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
        Disjoint (F.Vi 1) c.Zα ∧
        ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
        Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨hn,normal_extraspecial_source_reduction h hab structural previous hn ⟨e⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Displacement on the original centralizer series in the extraspecial branch

Reversal of the selected critical pair gives |Uα:C_{Uα}(U)| = 4.
Since |Uα| = 128, its centralizer Eα has order 32. The order-eight
commutator [U,Uα] lies in U ∩ Eα, so |Eα:Eα ∩ U| ≤ 4.
The reciprocal point lies in U. Its full centralizer normalizes Uα,
which proves [C_H(U),Uα] ≤ Eα with the original conjugation conventions.

Consequently every literal binary section B/N of C_H(U)/U has
selected-actor displacement at most two. If a section attains two,
both index comparisons are equalities: Eα lies in B and Eα ∩ N = Eα ∩ U.
The selected actor therefore centralizes C_H(U)/B and N/U. The final
application constructs the selected path from the actual Heisenberg
residual and supplies these bounds for every original section.

These are the group and displacement steps in 14.7.20(2), with numerator
B and denominator N. Classification and faithfulness of a noncentral
chief factor, the remaining extraspecial exclusion, and the residual
classification through 14.7.52 still require proof.
Source: Aschbacher–Smith, 14.7.17–18 and 14.7.20(2), printed pp.1048–1049.
-/


public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialCentralizerFactors_conjugate_centralizer' (A : Subgroup G) (g : G) :
    conjugate (centralizer (A : Set G)) g = centralizer (conjugate A g : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨(MulAut.conj g) x, ?_, by simp [MulAut.conj_apply,mul_assoc]⟩
    intro a ha
    apply (MulAut.conj g⁻¹).injective
    simpa [map_mul,MulAut.conj_apply,mul_assoc] using
      hx ((MulAut.conj g⁻¹) a) (mem_map_of_mem _ ha)

omit [Finite G] in
private theorem ExtraspecialCentralizerFactors_partner_normalized (c : CriticalPath (L := L) F) :
    centralizer (c.Zα : Set G) ≤ normalizer (c.Uα : Set G) := by
  have hn : conjugate F.H c.conjugator = normalizer (c.Zα : Set G) :=
    map_equiv_normalizer_eq (F.Vi 1) (MulAut.conj c.conjugator⁻¹)
  have hh := (map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom)
    (le_normalizer_conjugateSpanBy V F.H)).trans (le_normalizer_map _)
  change conjugate F.H c.conjugator ≤ normalizer (c.Uα : Set G) at hh
  exact (Subgroup.centralizer_le_normalizer _).trans (hn ▸ hh)

private theorem ExtraspecialCentralizerFactors_critical_commutator_le_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : ⁅F.U,c.Uα⁆ ≤ F.U ⊓ c.Uα := by
  exact le_inf (le_normalizer_iff_commutator_le_left.mp
    (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans
      (le_normalizer_conjugateSpanBy V F.H)))
    (le_normalizer_iff_commutator_le_right.mp (G2Source.normalizes_partner h c))

private theorem ExtraspecialCentralizerFactors_critical_point_le_span_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) : c.Zα ≤ F.U := by
  rw [←critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha]
  exact (commutator_mono inf_le_left le_rfl).trans
    ((ExtraspecialCentralizerFactors_critical_commutator_le_intersection h structural c).trans inf_le_left)

/-- The full U-centralizer moves the reciprocal span only inside its actual U-centralizer. -/
theorem centralizer_critical_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
  have hZU := ExtraspecialCentralizerFactors_critical_point_le_span_of_normal_card_two h hab structural hescape hn s c hs ha
  exact le_inf (le_normalizer_iff_commutator_le_right.mp
    ((centralizer_le hZU).trans (ExtraspecialCentralizerFactors_partner_normalized c)))
    (le_normalizer_iff_commutator_le_left.mp
      (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans
        (s.normalized.trans (normalizer_le_normalizer_centralizer _))))

/-- The reciprocal U-centralizer has the same index four as the original one. -/
theorem reciprocal_centralizer_index_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (c.Uα ⊓ centralizer (F.U : Set G)).relIndex c.Uα = 4 := by
  have hAH := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot_at h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q_at h structural r.path).trans (Q_le_H F))]
    exact selected_critical_indices_of_card_two h hab c hs ha
  have hrSel : r.path.RankSelection :=
    ⟨critical_index_positive r.path,by
      rw [r.reverse_index_of_placement hAH,ha,hrCard]⟩
  have hi := (critical_centralizer_indices_of_normal_card_two h hab structural hescape hn s
    r.path hrSel hrCard).2
  have hm := relIndex_map_map_of_injective
    (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom)
    (F.U ⊓ centralizer (r.path.Uα : Set G)) F.U (MulAut.conj r.conjugator⁻¹).injective
  change (conjugate (F.U ⊓ centralizer (r.path.Uα : Set G)) r.conjugator).relIndex
    (conjugate F.U r.conjugator) = _ at hm
  rw [conjugate_inf,r.base_U,ExtraspecialCentralizerFactors_conjugate_centralizer',r.tip_U] at hm
  exact hm.trans hi

/-- The reciprocal centralizer has order 32 and at most four cosets modulo U.
The order-eight critical commutator is retained inside the intersection. -/
theorem extraspecial_reciprocal_centralizer_size
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    Nat.card (c.Uα ⊓ centralizer (F.U : Set G) : Subgroup G) = 32 ∧
      F.U.relIndex (c.Uα ⊓ centralizer (F.U : Set G)) ≤ 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have ha := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hescape := h.flag_escape_at F previous
  obtain ⟨σ,hσ,hf,hd,hirr⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  have hU : Nat.card F.U = 128 := by
    have hc := s.card_section
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),Nat.card_zmod,hd] at hc
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    simpa only [hp,Nat.reducePow,Nat.reduceMul] using hc
  have hA : Nat.card c.Uα = 128 := by
    rw [CriticalPath.Uα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective,hU]
  let E := c.Uα ⊓ centralizer (F.U : Set G)
  have hE : Nat.card E = 32 := by
    have hc := relIndex_mul_card_of_le (inf_le_left : E ≤ c.Uα)
    rw [reciprocal_centralizer_index_of_normal_card_two h hab structural hescape hn s c hs ha,hA] at hc
    change 4 * Nat.card E = 128 at hc
    omega
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.U ⊓ E := by
    have hi := ExtraspecialCentralizerFactors_critical_commutator_le_intersection h structural c
    exact le_inf (hi.trans inf_le_left)
      (le_inf (hi.trans inf_le_right) ((hi.trans inf_le_left).trans F.U.le_centralizer))
  have hlo : 8 ≤ Nat.card (F.U ⊓ E : Subgroup G) := by
    rw [←critical_commutator_card_of_normal_card_two h hab structural hescape hn s c hs ha]
    exact card_le_of_le hcomm
  refine ⟨hE,?_⟩
  have hc := relIndex_mul_card_of_le (inf_le_right : F.U ⊓ E ≤ E)
  rw [inf_relIndex_right,hE] at hc
  nlinarith

/-- Every literal binary section of the full centralizer above U has
selected-actor displacement at most two. No chief or faithfulness premise
is assumed to obtain this source estimate. -/
theorem extraspecial_centralizer_section_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ)
    (a : F.H) (ha : (a : G) ∈ c.Uα) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hc := centralizer_critical_commutator_of_normal_card_two h hab structural
    (h.flag_escape_at F previous) hn sU c hs htwo
  have hmove : ⁅c.Uα,B⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
    rw [commutator_comm]
    exact (commutator_mono hB le_rfl).trans hc
  exact s.displacement_rank_le_of_commutator_bound c.Uα
    (c.Uα ⊓ centralizer (F.U : Set G)) F.U hUN hmove 2
    (extraspecial_reciprocal_centralizer_size h hab structural previous hex hcard hexp c hs).2 a ha

/-- If a section uses the full displacement budget, the controlling
reciprocal centralizer lies in its numerator and meets its denominator
only inside U. Thus the selected actor is trivial both above and below
that section in the centralizer series. -/
theorem extraspecial_centralizer_section_saturation
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ)
    (a : F.H) (ha : (a : G) ∈ c.Uα)
    (hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1))) :
    (c.Uα ⊓ centralizer (F.U : Set G)) ≤ B ∧
      (c.Uα ⊓ centralizer (F.U : Set G)) ⊓ N =
        F.U ⊓ (c.Uα ⊓ centralizer (F.U : Set G)) ∧
      ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ B ∧ ⁅N,c.Uα⁆ ≤ F.U := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  let E := c.Uα ⊓ centralizer (F.U : Set G)
  have hc : ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ E :=
    centralizer_critical_commutator_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn sU c hs htwo
  have hmove : ⁅c.Uα,B⁆ ≤ E := by
    rw [commutator_comm]
    exact (commutator_mono hB le_rfl).trans hc
  have hb : (F.U ⊓ E).relIndex E ≤ 2^2 := by
    rw [inf_relIndex_right]
    exact (extraspecial_reciprocal_centralizer_size h hab structural previous hex hcard hexp c hs).2
  obtain ⟨hEB,hEN,_⟩ := s.endpoints_of_displacement_saturation c.Uα E (F.U ⊓ E)
    inf_le_right (inf_le_left.trans hUN) hmove 2 hb a ha hr
  refine ⟨hEB,hEN,hc.trans hEB,?_⟩
  have hNN : F.H ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx n hnN
    have hnB := s.kernel_le hnN
    apply (s.coordinates_eq_one_iff ⟨x*n*x⁻¹,
      (mem_normalizer_iff.mp (s.normalized hx) n).mp hnB⟩).mp
    apply Multiplicative.toAdd.injective
    rw [s.equivariant ⟨x,hx⟩ ⟨n,hnB⟩,(s.coordinates_eq_one_iff _).mpr hnN]
    exact map_zero _
  have hN : ⁅N,c.Uα⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp
    (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans hNN)
  have hE : ⁅N,c.Uα⁆ ≤ E :=
    (commutator_mono (s.kernel_le.trans hB) le_rfl).trans hc
  exact (le_inf hE hN).trans (hEN.le.trans inf_le_left)

/-- Original-group application of the centralizer-series estimate in
14.7.20(2). The actual Heisenberg residual supplies point normality,
the selected reciprocal path, and all displacement bounds. -/
theorem extraspecial_centralizer_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (c.Uα ⊓ centralizer (F.U : Set G) : Subgroup G) = 32 ∧
      F.U.relIndex (c.Uα ⊓ centralizer (F.U : Set G)) ≤ 4 ∧
      ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) ∧
      ∀ (B N : Subgroup G), B ≤ centralizer (F.U : Set G) → F.U ≤ N →
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) F.H W),
      BinaryConjugationSection F.H B N ρ →
      ∀ a : F.H, (a : G) ∈ c.Uα →
        Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 ∧
        (2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) →
          ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ B ∧ ⁅N,c.Uα⁆ ≤ F.U) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hplace,_,_⟩ :=
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨hsize,hindex⟩ := extraspecial_reciprocal_centralizer_size
    h hab structural previous hex hcard hexp c hs
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  refine ⟨c,hs,hplace,hsize,hindex,
    centralizer_critical_commutator_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn sU c hs htwo,?_⟩
  intro B N hB hUN W aW mW ρ s a ha
  refine ⟨extraspecial_centralizer_section_displacement
    h hab structural previous hex hcard hexp c hs hB hUN s a ha,?_⟩
  intro hr
  exact (extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr).2.2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
