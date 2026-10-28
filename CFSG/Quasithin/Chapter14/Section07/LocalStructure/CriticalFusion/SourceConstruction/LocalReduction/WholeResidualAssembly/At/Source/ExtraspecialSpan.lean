module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ExtraspecialCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
public import Theory.LinearAlgebra.BinaryTwoTransitivity
public import Theory.GroupTheory.Commutator.TwoOrbitSpan
public import Theory.ThreeSubgroups
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanModule
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryFullPlane
public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SpanMarking
public import Theory.Representation.PSL3Two.ParabolicCyclic
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanCentral
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanFaithfulPlane
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanFaithful
public import Theory.Representation.BinaryConjugationSection.IntersectedChiefFactor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralSeed
public import Theory.Representation.PSL3Two.CoreCentralSeed
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralSubgroup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCenterControl
public import Theory.GroupTheory.CubicCentralLayer
public import Theory.GroupTheory.PGroup.NormalIndexTwoStep
public import Theory.Representation.BinaryConjugationSection.EmbeddedSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterFixedPlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreMovement
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterSpan
public import Theory.Representation.BinaryConjugationSection.ElementaryQuotient
public import Theory.Frattini.PGroup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterCore
public import Theory.Representation.BinaryConjugationSection.RelativeIntersectedChiefFactor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterCentralSeed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralCompletion

/-!
# Guarded extraspecial span

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/
/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original extraspecial commutator spans

The full natural L-action gives the two-orbit cover on U-conjugates without
assuming the later Data record. Apply the two-orbit commutator argument to
S = ⟨Uᴸ⟩ and R = ⟨[U,Q]ᴸ⟩. In the extraspecial branch, the critical interchange
puts the two core commutators in the opposite two-cores. The three-subgroups
lemma places [[U,Q],Uα] in both distinct critical point groups, so it vanishes.
Thus R lies in Z(S). The critical actor's square root makes [R,Q] nontrivial;
natural transitivity then gives [R,Q] = V. Also Φ(S) = S′ = V.

The order-four actor has a four-dimensional displacement on U/V₁. Comparing
it with the actual index-four centralizer proves [U,Q] = C_U(Uα), of order 32.
It follows that U ∩ R = [U,Q] ≤ O₂(K). The final original-group application
constructs the selected path and supplies all four clauses of 14.7.19, together
with this centralizer and intersection. Both remaining centralizer alternatives
and the later residual classification still require proof.

Source: Aschbacher–Smith, 14.7.12–13, 14.7.18–19 and the opening of 14.7.23,
printed pp.1046,1048–1050, refs/quasithin.pdf. The genuine earlier Structural1222,
Theorem12213 and faithful-classification inputs retain their existing producers;
final discharge remains with qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
private theorem ExtraspecialSpanStructure_original_pair_transporter
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) {a b c e : G}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (he : e ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (he1 : e ≠ 1)
    (hab : a ≠ b) (hce : c ≠ e) :
    ∃ l ∈ L, l*a*l⁻¹ = c ∧ l*b*l⁻¹ = e := by
  let := h.chosen.elementary
  let a' : Additive V := Additive.ofMul ⟨a,ha⟩
  let b' : Additive V := Additive.ofMul ⟨b,hb⟩
  let c' : Additive V := Additive.ofMul ⟨c,hc⟩
  let e' : Additive V := Additive.ofMul ⟨e,he⟩
  obtain ⟨f,hfa,hfb⟩ := BinaryLinear.exists_linearEquiv_pair a' b' c' e'
    (fun hh => ha1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hb1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hc1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => he1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hab (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hce (congrArg (fun v : Additive V => (v.toMul : G)) hh))
  obtain ⟨l,hl⟩ := h.naturalMarking.geometryAction.surjective f
  refine ⟨l,l.property,?_,?_⟩
  · have hh := h.naturalMarking.geometryAction.conjugation l a'
    rw [hl,hfa] at hh
    exact hh.symm
  · have hh := h.naturalMarking.geometryAction.conjugation l b'
    rw [hl,hfb] at hh
    exact hh.symm

omit [Finite G] in
private theorem ExtraspecialSpanStructure_original_mem_H_of_fixes_point
    (z : G) (hz : F.Vi 1 = zpowers z) {a : G} (h : (MulAut.conj a) z = z) : a ∈ F.H := by
  change a ∈ normalizer (F.Vi 1 : Set G)
  rw [mem_normalizer_iff_map_conj_eq,hz,MonoidHom.map_zpowers]
  exact congrArg zpowers h
omit [Finite G] in
private theorem ExtraspecialSpanStructure_original_map_U_eq_of_point_eq
    (z : G) (hz : F.Vi 1 = zpowers z) {a b : G}
    (h : (MulAut.conj a) z = (MulAut.conj b) z) :
    F.U.conjBy a = F.U.conjBy b := by
  have hf : (MulAut.conj (b⁻¹*a)) z = z := by
    have hh := congrArg (MulAut.conj b⁻¹) h
    simpa [MulAut.conj_apply,mul_assoc] using hh
  have hn := mem_normalizer_iff_map_conj_eq.mp
    ((le_normalizer_conjugateSpanBy V F.H) (ExtraspecialSpanStructure_original_mem_H_of_fixes_point z hz hf))
  change F.U.conjBy (b⁻¹*a) = F.U at hn
  have hh := congrArg (fun A : Subgroup G => A.conjBy b) hn
  simpa only [conjBy_conjBy,mul_inv_cancel_left] using hh
/-- The full natural action gives the original two-orbit cover, before Data. -/
theorem original_span_two_orbit
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) {A : Subgroup G}
    (ha : ∃ a ∈ L, A = F.U.conjBy a) (hne : A ≠ F.U) (l : L) :
    F.U.conjBy (l : G) = F.U ∨
      ∃ p : (L ⊓ F.H : Subgroup G), F.U.conjBy (l : G) = A.conjBy (p : G) := by
  classical
  obtain ⟨z,hz1,hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  by_cases he : F.U.conjBy (l : G) = F.U
  · exact Or.inl he
  right
  obtain ⟨a,ha,rfl⟩ := ha
  have hzV : z ∈ V := F.le_seed 1 (hz.symm ▸ mem_zpowers z)
  have haz : (MulAut.conj a) z ∈ V :=
    (mem_normalizer_iff.mp (h.chosen.normalizes ha) z).mp hzV
  have hlz : (MulAut.conj (l : G)) z ∈ V :=
    (mem_normalizer_iff.mp (h.chosen.normalizes l.property) z).mp hzV
  have hazne : (MulAut.conj a) z ≠ 1 := (map_ne_one_iff _ (MulAut.conj a).injective).mpr hz1
  have hlzne : (MulAut.conj (l : G)) z ≠ 1 := (map_ne_one_iff _ (MulAut.conj (l : G)).injective).mpr hz1
  have hza : z ≠ (MulAut.conj a) z := by
    intro hez
    exact hne (by simpa only [conjBy_one] using
      ExtraspecialSpanStructure_original_map_U_eq_of_point_eq z hz (a := a) (b := 1) (by simpa using hez.symm))
  have hzl : z ≠ (MulAut.conj (l : G)) z := by
    intro hez
    exact he (by simpa only [conjBy_one] using
      ExtraspecialSpanStructure_original_map_U_eq_of_point_eq z hz (a := l) (b := 1) (by simpa using hez.symm))
  obtain ⟨p,hp,hpz,hpaz⟩ := ExtraspecialSpanStructure_original_pair_transporter h hzV haz hzV hlz hz1 hazne
    hz1 hlzne hza hzl
  have hpH : p ∈ F.H := ExtraspecialSpanStructure_original_mem_H_of_fixes_point z hz hpz
  refine ⟨⟨p,hp,hpH⟩,?_⟩
  rw [conjBy_conjBy]
  apply ExtraspecialSpanStructure_original_map_U_eq_of_point_eq z hz
  simpa only [MulAut.conj_apply,mul_inv_rev,mul_assoc] using hpaz.symm

omit [Finite G] in
private theorem ExtraspecialSpanStructure_original_L_normalizes_Q : L ≤ normalizer (Q T L : Set G) :=
  le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The original elementary span and its L-closure lie in Q, without Data. -/
theorem original_span_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.U ≤ Q T L ∧ conjugateSpanBy F.U L ≤ Q T L := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let := F.U_normal
  have hp : IsPGroup 2 (F.U.subgroupOf F.H) :=
    (IsElementaryAbelian.isPGroup 2 F.U).comap_subtype
  have hUT : F.U ≤ (T : Subgroup G) := by
    have hh := hp.le_sylow_of_normal (T.subtype (F.invariant 1))
    intro x hx
    exact hh (show (⟨x,F.U_le_H hx⟩ : F.H) ∈ F.U.subgroupOf F.H from hx)
  have hU : F.U ≤ Q T L := by
    change F.U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←h.centralizer_LT_at structural]
    exact le_inf (hUT.trans le_sup_right)
      (F.U.le_centralizer.trans (centralizer_le (le_conjugateSpanBy V F.H)))
  exact ⟨hU,conjugateSpanBy_le hU ExtraspecialSpanStructure_original_L_normalizes_Q⟩

/-- The original commutator span is [S,Q], with both spans literal. -/
theorem original_span_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ⁅conjugateSpanBy F.U L,Q T L⁆ = conjugateSpanBy ⁅F.U,Q T L⁆ L := by
  have hh := commutator_iSup_conjugates F.U L (Q T L)
    (original_span_le_core h hab structural).1 ExtraspecialSpanStructure_original_L_normalizes_Q
  simpa only [←conjugateSpanBy_eq_iSup_conj] using hh

/-- The two-orbit commutator calculation applies before recognition. -/
theorem original_span_frattini_derived
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {A : Subgroup G} (ha : ∃ a ∈ L, A = F.U.conjBy a) (hne : A ≠ F.U) :
    (frattini (conjugateSpanBy F.U L)).map (conjugateSpanBy F.U L).subtype =
      conjugateSpanBy ⁅F.U,A⁆ L ∧
    ⁅conjugateSpanBy F.U L,conjugateSpanBy F.U L⁆ = conjugateSpanBy ⁅F.U,A⁆ L := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨hUQ,hSQ⟩ := original_span_le_core h hab structural
  have hd := TwoOrbitSpan.derived_span F.U A L (L ⊓ F.H) (Q T L)
    hUQ ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
    ExtraspecialSpanStructure_original_L_normalizes_Q
    (inf_le_right.trans (le_normalizer_conjugateSpanBy V F.H)) inf_le_left
    (commutator_eq_bot_iff_le_centralizer.mpr F.U.le_centralizer)
    (by obtain ⟨a,ha,he⟩ := ha; exact ⟨⟨a,ha⟩,he⟩)
    (original_span_two_orbit h ha hne)
  have hPhi := TwoOrbitSpan.frattini_span F.U L
    ((isPGroup_pCoreIn 2 _).to_le hSQ)
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu)
  exact ⟨hPhi.trans hd,hd⟩

/-- In the extraspecial branch S has derived and Frattini subgroup V. -/
theorem extraspecial_span_frattini_derived
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    (frattini (conjugateSpanBy F.U L)).map (conjugateSpanBy F.U L).subtype = V ∧
      ⁅conjugateSpanBy F.U L,conjugateSpanBy F.U L⁆ = V := by
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful he c hs
  have hne : c.Uα ≠ F.U := by
    intro hh
    have hc := extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs
    rw [hh,commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr hab)] at hc
    have hv := h.seed_card
    rw [←hc,Nat.card_unique] at hv
    norm_num at hv
  have hh := original_span_frattini_derived h hab structural ⟨g,hg,hgU.symm⟩ hne
  rw [extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs] at hh
  have hv : conjugateSpanBy V L = V :=
    le_antisymm (conjugateSpanBy_le le_rfl h.chosen.normalizes) (le_conjugateSpanBy V L)
  simpa only [hv] using hh


private theorem ExtraspecialSpanStructure_normalized_two_image_commutator {D X : Type*} [Group D] [Group X]
    (f : D →* X) (A B : Subgroup D) (hn : A ≤ normalizer (B : Set D))
    (hc : Nat.card (B.map f) = 2) : ⁅A,B⁆ ≤ f.ker := by
  have hnorm : A.map f ≤ normalizer (B.map f : Set X) :=
    (map_mono hn).trans (B.le_normalizer_map f)
  have hh : (⁅A,B⁆).map f = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hnorm.trans (normalizer_le_centralizer_of_card_two _ hc))
  exact (Subgroup.map_eq_bot_iff _).mp hh

/-- Both original core commutators lie in the opposite H-type two-cores. -/
theorem extraspecial_opposite_core_commutators
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅Q T L,c.Uα⁆ ≤ F.H.pCoreIn 2 ∧ ⁅Q T L,F.U⁆ ≤ c.Qα := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  obtain ⟨hz,_,_⟩ := extraspecial_critical_interchange h hab structural previous faithful ⟨e⟩ c hs
  obtain ⟨g,hg,hU,hA,hcore⟩ := G2Source.critical_span_core_interchange h c hz
  have hQA : Q T L ≤ normalizer (c.Uα : Set G) := by
    rw [←hU]
    exact TwoOrbitSpan.normalizes_conjugate F.U L (Q T L)
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H)) ExtraspecialSpanStructure_original_L_normalizes_Q ⟨g,hg⟩
  have hnorm : (Q T L).subgroupOf F.H ≤ normalizer (c.Uα.subgroupOf F.H : Set F.H) := by
    apply le_normalizer_iff.mpr
    intro q hq a ha
    exact (mem_normalizer_iff.mp (hQA hq) a).mp ha
  have hk := ExtraspecialSpanStructure_normalized_two_image_commutator (starMap F)
    ((Q T L).subgroupOf F.H) (c.Uα.subgroupOf F.H) hnorm htwo
  rw [starMap,QuotientGroup.ker_mk'] at hk
  have hfirst := map_mono (f := F.H.subtype) hk
  rw [map_commutator,map_subgroupOf_eq_of_le (Q_le_H F),
    map_subgroupOf_eq_of_le ((critical_le_Q_at h structural c).trans (Q_le_H F))] at hfirst
  refine ⟨hfirst,?_⟩
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfirst
  rw [map_commutator] at hh
  change ⁅(Q T L).conjBy g⁻¹,c.Uα.conjBy g⁻¹⁆ ≤ (F.H.pCoreIn 2).conjBy g⁻¹ at hh
  have hQi : (Q T L).conjBy g⁻¹ = Q T L :=
    mem_normalizer_iff_map_conj_eq.mp (ExtraspecialSpanStructure_original_L_normalizes_Q (T := T) (L.inv_mem hg))
  rw [hQi,
    ←hU,conjBy_conjBy,inv_mul_cancel,conjBy_one,
    ←hcore,conjBy_conjBy,inv_mul_cancel,conjBy_one] at hh
  exact hh

/-- The original E=[U,Q] centralizes the reciprocal U, using both point groups. -/
theorem extraspecial_commutator_centralizes_partner
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅⁅F.U,Q T L⁆,c.Uα⁆ = ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨hQA,hQU⟩ := extraspecial_opposite_core_commutators h hab structural previous faithful he c hs
  have hQV : Q T L ≤ centralizer (V : Set G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [←h.centralizer_LT_at structural]
    exact inf_le_right
  have hrot : ⁅⁅c.Uα,F.U⁆,Q T L⁆ = ⊥ := by
    rw [commutator_comm c.Uα,extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs,
      commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hQV
  have hfirst : ⁅⁅F.U,Q T L⁆,c.Uα⁆ ≤ F.Vi 1 :=
    commutator_commutator_le_of_rotate_of_le_normalizer F.U_le_H (Q_le_H F)
      ((critical_le_Q_at h structural c).trans (Q_le_H F))
      ((commutator_mono hQA le_rfl).trans (section_core_commutator_le_point h s))
      (hrot.le.trans bot_le)
  have hsecond : ⁅⁅F.U,Q T L⁆,c.Uα⁆ ≤ c.Zα := by
    rw [commutator_comm F.U]
    exact (commutator_mono hQU le_rfl).trans (reciprocal_core_commutator_le_point h s c)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  exact le_bot_iff.mp ((le_inf hfirst hsecond).trans
    (critical_points_disjoint_of_normal_card_two h hab structural (h.flag_escape_at F previous) hn s c hs htwo).le_bot)


/-- The original E-span is central in S; the core moves R only inside V. -/
theorem extraspecial_commutator_span_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    conjugateSpanBy ⁅F.U,Q T L⁆ L ≤
      (center (conjugateSpanBy F.U L)).map (conjugateSpanBy F.U L).subtype ∧
    ⁅conjugateSpanBy ⁅F.U,Q T L⁆ L,Q T L⁆ ≤ V := by
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  have hEA := extraspecial_commutator_centralizes_partner h hab structural previous faithful he c hs
  have hPE : L ⊓ F.H ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) := by
    intro p hp
    have hU : F.U.map (MulAut.conj p).toMonoidHom = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H hp.2)
    have hQ : (Q T L).map (MulAut.conj p).toMonoidHom = Q T L :=
      mem_normalizer_iff_map_conj_eq.mp (ExtraspecialSpanStructure_original_L_normalizes_Q hp.1)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅F.U,Q T L⁆).map (MulAut.conj p).toMonoidHom = _
    rw [map_commutator,hU,hQ]
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful he c hs
  have hne : c.Uα ≠ F.U := by
    intro hh
    have hc := extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs
    rw [hh,commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr hab)] at hc
    have hv := h.seed_card
    rw [←hc,Nat.card_unique] at hv
    norm_num at hv
  have hcentral := iSup_conjugates_le_center_of_two_orbits F.U ⁅F.U,Q T L⁆ c.Uα L (L ⊓ F.H)
    hEU hPE (commutator_eq_bot_iff_le_centralizer.mpr
      (hEU.trans (le_centralizer_iff_isMulCommutative.mpr hab))) hEA
    (original_span_two_orbit h ⟨g,hg,hgU.symm⟩ hne)
  rw [←conjugateSpanBy_eq_iSup_conj,←conjugateSpanBy_eq_iSup_conj] at hcentral
  refine ⟨?_,?_⟩
  · intro x hx
    have hh := hcentral hx
    refine ⟨⟨x,hh.1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro t
    exact Subtype.ext (hh.2 t t.property)
  · have hEC : ⁅F.U,Q T L⁆ ≤ F.U ⊓ centralizer (c.Uα : Set G) :=
      le_inf hEU (commutator_eq_bot_iff_le_centralizer.mp hEA)
    have hmove : ⁅⁅F.U,Q T L⁆,Q T L⁆ ≤ V := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hEC).trans
        (extraspecial_core_critical_centralizer_commutator h hab structural previous faithful he c hs)
    have hh := commutator_iSup_conjugates ⁅F.U,Q T L⁆ L (Q T L)
      (hEU.trans (original_span_le_core h hab structural).1) ExtraspecialSpanStructure_original_L_normalizes_Q
    rw [←conjugateSpanBy_eq_iSup_conj,←conjugateSpanBy_eq_iSup_conj] at hh
    rw [hh]
    exact conjugateSpanBy_le hmove h.chosen.normalizes

/-- An order-four critical root prevents the second core commutator from vanishing. -/
theorem extraspecial_commutator_span_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅conjugateSpanBy ⁅F.U,Q T L⁆ L,Q T L⁆ ≠ ⊥ := by
  intro hzero
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,_⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  have hc : ⁅Q T L,⁅Q T L,F.U⁆⁆ ≤ F.Vi 1 := by
    rw [commutator_comm (Q T L) F.U,commutator_comm]
    exact ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hzero.le).trans bot_le
  have hquad := BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    F.H F.U (F.Vi 1) (Q T L) ρ (MonoidHom.id F.H) s hc
  have hbb : b ∈ ((Q T L).subgroupOf F.H).map (MonoidHom.id F.H) := ⟨b,hb,rfl⟩
  have hnil : (ρ b-1)^2=0 := by
    ext v
    exact sub_eq_zero.mpr (hquad b hbb b hbb v)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,_,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let : Nontrivial (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2)
      (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)))
  let : CharP (Module.End (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U))) 2 :=
    charP_of_injective_algebraMap' (ZMod 2) 2
  have hpow : (ρ b)^2=1 := by
    apply sub_eq_zero.mp
    simpa only [sub_pow_char_of_commute 2 (Commute.one_right (ρ b)),one_pow] using hnil
  have hk : b^2 ∈ ρ.ker := by change ρ (b^2)=1; rwa [map_pow]
  rw [section_action_kernel_eq_core_of_escape h structural (h.flag_escape_at F previous) s] at hk
  apply hane
  rw [←hba,←map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hk

/-- Original 14.7.19(2): the second commutator span is exactly V. -/
theorem extraspecial_commutator_span_core_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅conjugateSpanBy ⁅F.U,Q T L⁆ L,Q T L⁆ = V := by
  let B := ⁅conjugateSpanBy ⁅F.U,Q T L⁆ L,Q T L⁆
  have hBV : B ≤ V := (extraspecial_commutator_span_central h hab structural previous faithful he c hs).2
  have hne : B ≠ ⊥ := extraspecial_commutator_span_core_ne_bot h hab structural previous faithful he c hs
  have hn : L ≤ normalizer (B : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [B]
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ L hl),
      mem_normalizer_iff_map_conj_eq.mp (ExtraspecialSpanStructure_original_L_normalizes_Q hl)]
  obtain ⟨x,hx,hx1⟩ := (B.bot_or_exists_ne_one).resolve_left hne
  apply le_antisymm hBV
  intro v hv
  by_cases hv1 : v=1
  · simpa only [hv1] using B.one_mem
  obtain ⟨l,hl,hxv,_⟩ := G2Source.vector_interchange h (hBV hx) hv hx1 hv1
  rw [←hxv]
  exact (mem_normalizer_iff.mp (hn hl) x).mp hx


/-- Source 14.7.18 identifies E=[U,Q] with the actual reciprocal centralizer,
including its order and its two-dimensional quotient over V. -/
theorem extraspecial_commutator_eq_critical_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅F.U,Q T L⁆ = F.U ⊓ centralizer (c.Uα : Set G) ∧
      Nat.card (⁅F.U,Q T L⁆ : Subgroup G) = 32 ∧ V.relIndex ⁅F.U,Q T L⁆ = 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let E := ⁅F.U,Q T L⁆
  let C := F.U ⊓ centralizer (c.Uα : Set G)
  have hEU : E ≤ F.U := le_normalizer_iff_commutator_le_left.mp ((Q_le_H F).trans s.normalized)
  have hVE : V ≤ E := by
    rw [←extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs]
    exact commutator_mono le_rfl (critical_le_Q_at h structural c)
  have hZE : F.Vi 1 ≤ E := (F.le_seed 1).trans hVE
  have hEC : E ≤ C := le_inf hEU
    (commutator_eq_bot_iff_le_centralizer.mp
      (extraspecial_commutator_centralizes_partner h hab structural previous faithful he c hs))
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  have hk := (extraspecial_critical_root_fixed_plane h hab structural previous he s c hs
    a b ha hane hb hba (hbo ▸ pow_orderOf_eq_one _)).1
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  obtain ⟨_,_,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  have hZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hV : Nat.card V = 8 := h.seed_card
  have hvrel : (F.Vi 1).relIndex V = 4 := by
    have hh := relIndex_mul_card_of_le (F.le_seed 1)
    rw [hZ,hV] at hh
    omega
  have hvdim := s.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2 hvrel
  have hr := (ρ b-1).finrank_range_add_finrank_ker
  rw [hk,hvdim,hd] at hr
  have hCr : C.relIndex F.U = 4 :=
    (critical_centralizer_indices_of_normal_card_two h hab structural (h.flag_escape_at F previous) hn s c hs htwo).2
  have hCdim := s.imageSpace_codimension_of_index C inf_le_left (hZE.trans hEC) 2 hCr
  rw [hd] at hCdim
  have hrE := Submodule.finrank_mono
    (s.displacement_range_le_imageSpace_of_commutator_le (Q T L) E (commutator_comm _ _).le b hb)
  have hECim := s.imageSpace_mono hEC
  have hECdim := Submodule.finrank_mono hECim
  have him : s.imageSpace E = s.imageSpace C :=
    Submodule.eq_of_le_of_finrank_eq hECim (by omega)
  have heq : E = C := by
    apply le_antisymm hEC
    intro x hx
    apply (s.coordinates_mem_imageSpace_iff_of_kernel_le E hZE ⟨x,hx.1⟩).mp
    rw [him]
    exact (s.mem_imageSpace_iff C _).mpr ⟨⟨x,hx.1⟩,hx,rfl⟩
  have hU : Nat.card F.U = 128 := by
    have hh := s.card_section
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),Nat.card_zmod,hd,hZ] at hh
    exact hh
  have hE : Nat.card E = 32 := by
    have hh := relIndex_mul_card_of_le (inf_le_left : C ≤ F.U)
    change C.relIndex F.U * Nat.card C = Nat.card F.U at hh
    rw [hCr,hU,←heq] at hh
    omega
  refine ⟨heq,hE,?_⟩
  have hh := relIndex_mul_card_of_le hVE
  change V.relIndex E = 4
  change V.relIndex E * Nat.card V = Nat.card E at hh
  rw [hV,hE] at hh
  omega


/-- The literal intersection needed for 14.7.23 is exactly E, and E lies in P. -/
theorem extraspecial_span_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    F.U ⊓ conjugateSpanBy ⁅F.U,Q T L⁆ L = ⁅F.U,Q T L⁆ ∧
      ⁅F.U,Q T L⁆ ≤ (K F).pCoreIn 2 := by
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have hc := (extraspecial_commutator_span_central h hab structural previous faithful he c hs).1
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful he c hs
  have hAS : c.Uα ≤ S := by
    rw [←hgU]
    change F.U.map (MulAut.conj g).toMonoidHom ≤ S
    exact (map_mono (le_conjugateSpanBy F.U L)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy F.U L hg))
  have hRA : R ≤ centralizer (c.Uα : Set G) := by
    intro r hr a ha
    obtain ⟨r',hr',rfl⟩ := hc hr
    exact congrArg Subtype.val ((mem_center_iff.mp hr') ⟨a,hAS ha⟩)
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  refine ⟨le_antisymm ?_ (le_inf hEU (le_conjugateSpanBy _ _)),
    hEU.trans (span_le_residual_core h hab)⟩
  exact (inf_le_inf_left F.U hRA).trans_eq
    (extraspecial_commutator_eq_critical_centralizer h hab structural previous faithful he c hs).1.symm

/-- The literal R is abelian and lies in C_H(U), while U is not contained in R. -/
theorem extraspecial_span_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    IsMulCommutative (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
      conjugateSpanBy ⁅F.U,Q T L⁆ L ≤ F.H ⊓ centralizer (F.U : Set G) ∧
      ¬ F.U ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L := by
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have hcent : R ≤ (center S).map S.subtype :=
    (extraspecial_commutator_span_central h hab structural previous faithful he c hs).1
  have hRS : R ≤ S := hcent.trans (map_subtype_le _)
  have hRC : R ≤ centralizer (S : Set G) := by
    intro r hr s hs
    obtain ⟨r',hr',rfl⟩ := hcent hr
    exact congrArg Subtype.val ((mem_center_iff.mp hr') ⟨s,hs⟩)
  refine ⟨le_centralizer_iff_isMulCommutative.mp (hRC.trans (centralizer_le hRS)),
    le_inf (hRS.trans ((original_span_le_core h hab structural).2.trans (Q_le_H F)))
      (hRC.trans (centralizer_le (le_conjugateSpanBy F.U L))),?_⟩
  intro hUR
  have hUcent : F.U ≤ centralizer (S : Set G) := hUR.trans hRC
  have hSS : S ≤ centralizer (S : Set G) := by
    apply conjugateSpanBy_le
    · exact hUcent
    · exact (le_normalizer_conjugateSpanBy F.U L).trans (normalizer_le_normalizer_centralizer _)
  have hz := commutator_eq_bot_iff_le_centralizer.mpr hSS
  rw [(extraspecial_span_frattini_derived h hab structural previous faithful he c hs).2] at hz
  have hc := h.seed_card
  rw [hz,Nat.card_unique] at hc
  norm_num at hc

/-- Original application of 14.7.18--19 and the intersection in 14.7.23.
The Heisenberg residual supplies the selected path. E, R, S and every
centralizer are the literal subgroups, with no Data or module-recognition premise. -/
theorem extraspecial_span_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let E := ⁅F.U,Q T L⁆
    let R := conjugateSpanBy E L
    let S := conjugateSpanBy F.U L
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      E = F.U ⊓ centralizer (c.Uα : Set G) ∧ Nat.card E = 32 ∧ V.relIndex E = 4 ∧
      ⁅S,Q T L⁆ = R ∧ ⁅R,Q T L⁆ = V ∧ R ≤ (center S).map S.subtype ∧
      (frattini S).map S.subtype = V ∧ ⁅S,S⁆ = V ∧
      IsMulCommutative R ∧ R ≤ F.H ⊓ centralizer (F.U : Set G) ∧ ¬ F.U ≤ R ∧
      F.U ⊓ R = E ∧ E ≤ (K F).pCoreIn 2 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hplace,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨hE,hEc,hEi⟩ := extraspecial_commutator_eq_critical_centralizer h hab structural previous faithful ⟨e⟩ c hs
  obtain ⟨hPhi,hder⟩ := extraspecial_span_frattini_derived h hab structural previous faithful ⟨e⟩ c hs
  obtain ⟨hinter,hEP⟩ := extraspecial_span_intersection h hab structural previous faithful ⟨e⟩ c hs
  obtain ⟨hRab,hRC,hUnR⟩ := extraspecial_span_centralizer h hab structural previous faithful ⟨e⟩ c hs
  exact ⟨c,hs,hplace,hE,hEc,hEi,original_span_core_commutator h hab structural,
    extraspecial_commutator_span_core_eq_seed h hab structural previous faithful ⟨e⟩ c hs,
    (extraspecial_commutator_span_central h hab structural previous faithful ⟨e⟩ c hs).1,
    hPhi,hder,hRab,hRC,hUnR,hinter,hEP⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original elementary commutator-span module

Let E = [U,Q] and R = ⟨Eᴸ⟩ in the Heisenberg residual branch. The proved
span identities make R elementary and give [R,Q] = V. Construct its literal
binary conjugation section R/V for LT, retaining the trivial Q-action.
The index |E:V| = 4 gives a plane. Transfer the point cubic's zero norm
from U/V₁ to this plane through the actual coordinate kernels; full movement
then makes the plane irreducible for L₁. A two-group fixed-point argument
constructs a nonzero (T ∩ L)-fixed vector in it. Irreducibility and the
conjugate-span definition make that vector cyclic for R/V, with point-parabolic
orbit exactly E/V. These are the original inputs to H.6.5.

Source: Aschbacher–Smith 14.7.19 and 14.7.22(1), printed pp.1048–1050,
refs/quasithin.pdf. The genuine Structural1222, Theorem12213 and earlier
faithful-classification inputs retain their producers and final discharge
with qt-d-14775-source. No later Data or recognition conclusion is assumed.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The elementary commutator span in the original Heisenberg branch. -/
theorem extraspecial_commutator_span_elementary
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    IsElementaryAbelian 2 (conjugateSpanBy ⁅F.U,Q T L⁆ L) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  let : IsElementaryAbelian 2 (⁅F.U,Q T L⁆ : Subgroup G) := IsElementaryAbelian.of_le hEU
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,hR,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  let : IsMulCommutative (conjugateSpanBy ⁅F.U,Q T L⁆ L) := hR
  exact conjugateSpanBy_elementary_of_commutative _ _

omit [Finite G] in
private theorem ExtraspecialSpanModule_spanModule_normalizes_span (A B N : Subgroup G)
    (hNA : N ≤ normalizer (A : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer (conjugateSpanBy A B : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
    mem_normalizer_iff_map_conj_eq.mp (hNA hn),mem_normalizer_iff_map_conj_eq.mp (hNB hn)]

omit [Finite G] in
private theorem ExtraspecialSpanModule_spanModule_normalizes_commutator (A B N : Subgroup G)
    (hNA : N ≤ normalizer (A : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hNA hn),mem_normalizer_iff_map_conj_eq.mp (hNB hn)]

/-- Both LT and its point parabolic preserve the original commutator construction. -/
theorem original_commutator_span_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (L ⊔ (T : Subgroup G)) ≤ normalizer (conjugateSpanBy ⁅F.U,Q T L⁆ L : Set G) ∧
      (L ⊓ F.H) ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) := by
  have hQN : L ⊔ (T : Subgroup G) ≤ normalizer (Q T L : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTN : (T : Subgroup G) ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) :=
    ExtraspecialSpanModule_spanModule_normalizes_commutator _ _ _ ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (le_sup_right.trans hQN)
  exact ⟨sup_le (le_normalizer_conjugateSpanBy _ _) (ExtraspecialSpanModule_spanModule_normalizes_span _ _ _ hTN
    (h.sylow_normalizes_at structural)),ExtraspecialSpanModule_spanModule_normalizes_commutator _ _ _
      (inf_le_right.trans (le_normalizer_conjugateSpanBy V F.H))
      ((inf_le_left.trans le_sup_left).trans hQN)⟩

/-- The actual R/V section, with its plane E/V and trivial Q-action. -/
theorem extraspecial_span_binary_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,Q T L⁆) = 2 ∧
      (∀ l : (L ⊔ (T : Subgroup G) : Subgroup G), (l : G) ∈ L ⊓ F.H →
        ∀ w ∈ s.imageSpace ⁅F.U,Q T L⁆, ρ l w ∈ s.imageSpace ⁅F.U,Q T L⁆) := by
  dsimp only
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let J := L ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 R :=
    extraspecial_commutator_span_elementary h hab structural previous faithful he
  obtain ⟨c,hs,_,_,_,hEV,_,hRQ,_,_,_,_,hRC,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hEQ : ⁅F.U,Q T L⁆ ≤ conjugateSpanBy F.U L :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))).trans
      (le_conjugateSpanBy _ _)
  have hRQle : R ≤ Q T L :=
    (conjugateSpanBy_mono (le_normalizer_iff_commutator_le_left.mp
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))) le_rfl).trans
      (original_span_le_core h hab structural).2
  have hVR : V ≤ R := hRQ.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((pCoreIn_le 2 _).trans (original_commutator_span_normalized h structural).1))
  obtain ⟨ρ,⟨s⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates J R V
    (hRQle.trans (pCoreIn_le 2 _)) (original_commutator_span_normalized h structural).1 hVR
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
  refine ⟨Additive (R ⧸ V.subgroupOf R),inferInstance,inferInstance,ρ,s,?_,?_,?_⟩
  · intro a ha
    apply MonoidHom.mem_ker.mpr
    ext w
    obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
    have hh := s.equivariant a r
    have heq : s.coordinates
        ⟨(a : G)*(r : G)*(a : G)⁻¹,(mem_normalizer_iff.mp (s.normalized a.property) r).mp r.property⟩ =
        s.coordinates r := by
      apply div_eq_one.mp
      rw [←map_div]
      apply (s.coordinates_eq_one_iff _).mpr
      have hc : ⁅(a : G),(r : G)⁆ ∈ ⁅Q T L,R⁆ := commutator_mem_commutator ha r.property
      rw [commutator_comm (Q T L) R] at hc
      simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv] using hRQ.le hc
    change ρ a w = w
    simpa only [hr,toAdd_ofAdd] using hh.symm.trans (congrArg Multiplicative.toAdd heq)
  · exact s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hEV
  · intro l hl w hw
    exact s.imageSpace_apply_mem _ l ((original_commutator_span_normalized h structural).2 hl) w hw


omit [Finite G] in
private theorem ExtraspecialSpanModule_spanModule_norm_transfer
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    {τ : Representation (ZMod 2) F.H X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ)
    (s₀ : BinaryConjugationSection F.H F.U (F.Vi 1) τ)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (ha : (a : G) ∈ F.H)
    (hn : ∀ x, x + τ ⟨a,ha⟩ x + τ ⟨a,ha⟩ (τ ⟨a,ha⟩ x) = 0)
    (w : W) (hw : w ∈ s.imageSpace ⁅F.U,Q T L⁆) :
    w + ρ a w + ρ a (ρ a w) = 0 := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  obtain ⟨r,hr,rfl⟩ := (s.mem_imageSpace_iff _ w).mp hw
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  let u : F.U := ⟨r,hEU hr⟩
  let cR (x : R) : R := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s.normalized a.property) x).mp x.property⟩
  let cU (x : F.U) : F.U := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s₀.normalized ha) x).mp x.property⟩
  have hnU : ((u * cU u * cU (cU u) : F.U) : G) ∈ F.Vi 1 := by
    apply (s₀.coordinates_eq_one_iff _).mp
    apply Multiplicative.toAdd.injective
    change (s₀.coordinates _).toAdd = 0
    simp only [map_mul, toAdd_mul]
    rw [show (s₀.coordinates (cU u)).toAdd = τ ⟨a,ha⟩ (s₀.coordinates u).toAdd
      from s₀.equivariant ⟨a,ha⟩ u,
      show (s₀.coordinates (cU (cU u))).toAdd = τ ⟨a,ha⟩ (τ ⟨a,ha⟩ (s₀.coordinates u).toAdd) from
        (s₀.equivariant ⟨a,ha⟩ (cU u)).trans
          (congrArg (τ ⟨a,ha⟩) (s₀.equivariant ⟨a,ha⟩ u))]
    exact hn _
  have hnR : s.coordinates (r * cR r * cR (cR r)) = 1 :=
    (s.coordinates_eq_one_iff _).mpr (F.le_seed 1 hnU)
  have hh := congrArg Multiplicative.toAdd hnR
  simp only [map_mul, toAdd_mul] at hh
  rw [show (s.coordinates (cR r)).toAdd = ρ a (s.coordinates r).toAdd from s.equivariant a r,
    show (s.coordinates (cR (cR r))).toAdd = ρ a (ρ a (s.coordinates r).toAdd) from
      (s.equivariant a (cR r)).trans (congrArg (ρ a) (s.equivariant a r))] at hh
  exact hh

/-- The point cubic has zero norm on the actual E/V plane, not merely on U/V₁. -/
theorem extraspecial_span_plane_cubic_norm
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    ∃ a : (L ⊔ (T : Subgroup G) : Subgroup G), (a : G) ∈ F.Li L 1 ∧
      ∀ w ∈ s.imageSpace ⁅F.U,Q T L⁆, w + ρ a w + ρ a (ρ a w) = 0 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hnormal := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨τ,⟨s₀⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := exists_star_representation h s₀
  obtain ⟨z,hz,hzp,hfix⟩ := exists_fixedFree_cubic_of_point_normal h structural hnormal s₀ σ hσ
  have hzm : z ∈ star F (F.Li L 1) := hzp ▸ mem_zpowers z
  obtain ⟨a,ha,haz⟩ := hzm
  let aJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 ha).1⟩
  have heq : τ a = σ z := by
    rw [←haz,←hσ]
    rfl
  have hz3 (x) : σ z (σ z (σ z x)) = x := by
    calc _ = σ (z ^ 3) x := by simp [pow_succ,map_mul,Module.End.mul_apply]
         _ = x := by rw [show z ^ 3 = 1 from orderOf_dvd_iff_pow_eq_one.mp (by rw [hz]),map_one]; rfl
  refine ⟨aJ,ha,?_⟩
  apply ExtraspecialSpanModule_spanModule_norm_transfer s s₀ aJ a.property
  intro x
  change x + τ a x + τ a (τ a x) = 0
  rw [heq]
  apply hfix
  simp only [map_add,hz3]
  abel


private theorem ExtraspecialSpanModule_spanModule_binary_neg {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (w : W) : -w = w := by
  simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) w).symm

/-- The original point residual acts irreducibly on E/V. The norm relation
supplies full movement, so a binary line quotient would be impossible. -/
theorem extraspecial_span_plane_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    ∃ D : Subrepresentation (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
      D.toSubmodule = s.imageSpace ⁅F.U,Q T L⁆ ∧ IsIrreducible D.toRepresentation := by
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace ⁅F.U,Q T L⁆
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem _ (j a)
      ((original_commutator_span_normalized h structural).2 (F.Li_le L 1 a.property)) w hw }
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨c,hs,_,_,_,hi,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hd : Module.finrank (ZMod 2) D.toSubmodule = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
  let b : F.Li L 1 := ⟨a,ha⟩
  have hnorm (w : D.toSubmodule) :
      w + D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w) = 0 := by
    apply Subtype.ext
    exact hn w w.property
  have hm : Representation.BinaryOffender.subspaceCommutator D.toRepresentation ⊤ ⊤ = ⊤ := by
    apply top_unique
    intro w _
    have hmove : D.toRepresentation b (D.toRepresentation b w) - D.toRepresentation b w = w := by
      calc _ = -(D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w)) := by
             simp only [sub_eq_add_neg,ExtraspecialSpanModule_spanModule_binary_neg]
             exact add_comm _ _
           _ = w := (eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hnorm w)).symm
    exact Submodule.subset_span ⟨b,mem_top b,D.toRepresentation b w,Submodule.mem_top,hmove.symm⟩
  exact ⟨D,rfl,Representation.BinaryOffender.irreducible_of_rank_two_full_movement _ hd hm⟩

omit [Finite G] in
/-- The conjugates of the literal E/V plane generate the entire R/V section. -/
theorem extraspecial_span_plane_generates
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ)
    (A : Submodule (ZMod 2) W) (hA : s.imageSpace ⁅F.U,Q T L⁆ ≤ A)
    (hstable : ∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) : A = ⊤ := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let B : Subgroup R := A.toAddSubgroup.toSubgroup.comap s.coordinates
  have hRB : R ≤ B.map R.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨l,hl,e,he,rfl⟩
    let eR : R := ⟨e,le_conjugateSpanBy _ _ he⟩
    let lJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨l,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩
    refine ⟨⟨l*e*l⁻¹,(mem_normalizer_iff.mp (s.normalized lJ.property) e).mp eR.property⟩,?_,rfl⟩
    change (s.coordinates _).toAdd ∈ A
    rw [s.equivariant lJ eR]
    exact hstable ⟨l,hl⟩ _ (hA ((s.mem_imageSpace_iff _ _).mpr ⟨eR,he,rfl⟩))
  apply top_unique
  intro w _
  obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
  obtain ⟨b,hb,hbr⟩ := hRB r.property
  have hbr' : b = r := Subtype.ext hbr
  subst b
  change (s.coordinates r).toAdd ∈ A at hb
  simpa only [hr,toAdd_ofAdd] using hb

/-- Original application: construct R/V and prove all elementary-section,
plane, and residual-irreducibility inputs to the parabolic module recognition. -/
theorem extraspecial_span_plane_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,Q T L⁆) = 2 ∧
      (∃ D : Subrepresentation (ρ.comp (inclusion
        (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
        D.toSubmodule = s.imageSpace ⁅F.U,Q T L⁆ ∧ IsIrreducible D.toRepresentation) ∧
      ∀ A : Submodule (ZMod 2) W, s.imageSpace ⁅F.U,Q T L⁆ ≤ A →
        (∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) → A = ⊤ := by
  obtain ⟨W,ha,hm,ρ,s,hker,hd,_⟩ :=
    extraspecial_span_binary_section h hab structural previous faithful he
  exact ⟨W,ha,hm,ρ,s,hker,hd,
    extraspecial_span_plane_irreducible h hab structural previous faithful he s,
    extraspecial_span_plane_generates s⟩


open BinaryLinearThree.ParabolicCyclic in
/-- The original section has a Sylow-fixed cyclic seed whose point-parabolic
orbit spans exactly E/V. This supplies the geometric hypotheses of H.6.5
before choosing a matrix marking. -/
theorem extraspecial_span_cyclic_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
    ∃ w ∈ s.imageSpace ⁅F.U,Q T L⁆, w ≠ 0 ∧
      (∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w) ∧
      orbitSpan τ ⊤ w = ⊤ ∧
      orbitSpan τ (F.H.subgroupOf L) w = s.imageSpace ⁅F.U,Q T L⁆ ∧
      Module.finrank (ZMod 2) (orbitSpan τ (F.H.subgroupOf L) w) = 2 := by
  dsimp only
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  let D := s.imageSpace ⁅F.U,Q T L⁆
  let S := (T : Subgroup G).subgroupOf L
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have stable (l : L) (hl : (l : G) ∈ F.H) (w : W) (hw : w ∈ D) : τ l w ∈ D :=
    s.imageSpace_apply_mem _ (inclusion le_sup_left l)
      ((original_commutator_span_normalized h structural).2 ⟨l.property,hl⟩) w hw
  let : MulAction S D := {
    smul t w := ⟨τ t w,stable t (F.invariant 1 t.property) w w.property⟩
    one_smul w := by apply Subtype.ext; exact congrArg (fun f => f w.val) τ.map_one
    mul_smul t r w := by apply Subtype.ext; exact congrArg (fun f => f w.val) (τ.map_mul t r) }
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  obtain ⟨c,hs,_,_,_,hi,_⟩ := extraspecial_span_source_reduction h hab structural previous faithful he
  have hcard : Nat.card D = 4 := (s.imageSpace_card_eq_relIndex _ (le_conjugateSpanBy _ _)).trans hi
  have hd : Module.finrank (ZMod 2) D = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨w,hw,hw0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := D) (by rw [hcard]; decide)
    (show (0 : D) ∈ MulAction.fixedPoints S D from fun a => Subtype.ext (map_zero (τ a)))
  have hn : (w : W) ≠ 0 := fun hh => hw0 (Subtype.ext hh.symm)
  have hfix : ∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w :=
    fun t ht => congrArg Subtype.val (hw ⟨t,ht⟩)
  let A := orbitSpan τ (F.H.subgroupOf L) w
  have hAD : A ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l,hl,rfl⟩
    exact stable l hl w w.property
  obtain ⟨I,hI,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
  let : IsIrreducible I.toRepresentation := hirr
  have hstable (a : F.Li L 1) (v : W) (hv : v ∈ A) :
      ρ (inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) a) v ∈ A :=
    orbitSpan_stable τ (F.H.subgroupOf L) w
      ⟨a,(F.Li_le L 1 a.property).1⟩ (F.Li_le L 1 a.property).2 v hv
  let B : Subrepresentation I.toRepresentation := {
    toSubmodule := A.comap I.toSubmodule.subtype
    apply_mem_toSubmodule a v hv := hstable a v hv }
  have hB : B = ⊤ := (eq_bot_or_eq_top B).resolve_left (by
    intro hb
    have hm : (⟨w,hI ▸ w.property⟩ : I.toSubmodule) ∈ B := mem_orbitSpan τ _ w
    rw [hb] at hm
    exact hn (congrArg Subtype.val hm))
  have hDA : D ≤ A := by
    intro v hv
    have hm : (⟨v,hI ▸ hv⟩ : I.toSubmodule) ∈ B := hB ▸ Submodule.mem_top
    exact hm
  have hplane : A = D := le_antisymm hAD hDA
  have hfull : orbitSpan τ ⊤ w = ⊤ := by
    apply extraspecial_span_plane_generates s
    · apply hDA.trans
      apply Submodule.span_mono
      rintro v ⟨a,_,ha⟩
      exact ⟨a,mem_top a,ha⟩
    · intro l v hv
      exact orbitSpan_stable τ ⊤ w l (mem_top l) v hv
  exact ⟨w,w.property,hn,hfix,hfull,hplane,by change Module.finrank (ZMod 2) A = 2; rw [hplane]; exact hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Recognition and chief counts for the original R/V

Descend the original L-action on R/V through its marked quotient, using
unit-valued linear automorphisms to retain the full action kernel. The
compatible Sylow and parabolic marking carries the constructed cyclic plane
to the hypotheses of the proved H.6.5 classification. This gives actual
equivariant isomorphisms with the natural, core, Steinberg, and the two
indicated direct-sum models. The marking retains the dual-natural orientation
relative to the original natural action.

Transport each concrete chief count along the image of the literal L₁.
Finite residual-image compatibility identifies that image with the intrinsic
two-residual of the line parabolic. The five alternatives therefore have
respectively one, two, three, four and five noncentral L₁-chief factors.
The final application constructs the original LT conjugation section, kills Q,
and supplies the classification with no module-recognition premise.

Source: Aschbacher–Smith 14.7.22 and H.6.5, printed pp.1050,388,
refs/quasithin.pdf. The earlier source inputs retain their existing producers;
final discharge remains with qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialSpanRecognition_spanRecognition_descent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
    (hk : (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker) :
    ∃ σ : Representation (ZMod 2) BinaryLinearThree.Group W,
      σ.comp (SpanMarking.qL h) = ρ.comp (inclusion le_sup_left) := by
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  have hcore : L.pCoreIn 2 ≤ Q T L :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  have hkill : (SpanMarking.qL h).ker ≤ τ.ker := by
    rw [SpanMarking.qL_ker]
    intro l hl
    exact hk (hcore hl)
  have hkillU : (SpanMarking.qL h).ker ≤ τ.asGroupHom.ker := by
    intro l hl
    apply Units.ext
    exact hkill hl
  let β := (SpanMarking.qL h).liftOfSurjective (SpanMarking.qL_surjective h) ⟨τ.asGroupHom,hkillU⟩
  let σ : Representation (ZMod 2) BinaryLinearThree.Group W := (Units.coeHom _).comp β
  refine ⟨σ,?_⟩
  apply MonoidHom.ext
  intro l
  exact congrArg Units.val ((SpanMarking.qL h).liftOfRightInverse_comp_apply
    (Function.surjInv (SpanMarking.qL_surjective h))
    (Function.rightInverse_surjInv (SpanMarking.qL_surjective h)) ⟨τ.asGroupHom,hkillU⟩ l)

private theorem ExtraspecialSpanRecognition_spanRecognition_orbit_map
    {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W) (q : A →* B) (P : Subgroup A) (w : W) :
    BinaryLinearThree.ParabolicCyclic.orbitSpan σ (P.map q) w =
      BinaryLinearThree.ParabolicCyclic.orbitSpan (σ.comp q) P w := by
  unfold BinaryLinearThree.ParabolicCyclic.orbitSpan
  congr 1
  ext v
  constructor
  · rintro ⟨b,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨q a,mem_map_of_mem q ha,he⟩


private theorem ExtraspecialSpanRecognition_spanRecognition_relative_first_actor : (F.Li L 1).subgroupOf L =
    (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
  apply map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
    map_embedded_pResidual,subgroupOf_map_subtype]
  simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,↓reduceIte]
  change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
  rw [inf_comm]

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Model chief counts pull back along the literal original L₁-action.
Relative residuals and the full quotient map are retained. -/
theorem extraspecial_span_model_count
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (σ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (hσ : σ.comp q = ρ.comp (inclusion le_sup_left))
    {n : ℕ} (hc : HasCount (σ.comp actor.subtype) n) :
    HasCount (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) n := by
  have hmap : ((F.Li L 1).subgroupOf L).map q = actor := by
    rw [ExtraspecialSpanRecognition_spanRecognition_relative_first_actor,map_embedded_pResidual,hP]
    rfl
  let j : F.Li L 1 →* L := inclusion ((F.Li_le L 1).trans inf_le_left)
  let f : F.Li L 1 →* actor := (q.comp j).codRestrict actor (by
    intro a
    rw [←hmap]
    exact ⟨j a,a.property,rfl⟩)
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : BinaryLinearThree.Group) ∈ ((F.Li L 1).subgroupOf L).map q := by
      rw [hmap]
      exact a.property
    obtain ⟨l,hl,he⟩ := ha
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  have hh := hc.reindex f hf
  have heq : (σ.comp actor.subtype).comp f = ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))) := by
    ext a w
    exact congrArg (fun ψ : Representation (ZMod 2) L W => ψ (j a) w) hσ
  rwa [heq] at hh

set_option backward.isDefEq.respectTransparency false in
open BinaryLinearThree BinaryLinearThree.ParabolicCyclic BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Each source alternative carries its exact number of noncentral L₁-chief
factors. Thus the one- and two-factor cases identify the dual natural and
core alternatives under the already oriented marking. -/
theorem extraspecial_span_counted_alternatives
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (σ : Representation (ZMod 2) BinaryLinearThree.Group X)
    (hσ : σ.comp q = ρ.comp (inclusion le_sup_left))
    (hc : Alternatives σ) :
    let τ := ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))
    (Nonempty (σ.Equiv BinaryLinearThree.W) ∧ HasCount τ 1) ∨
    (Nonempty (σ.Equiv U₂) ∧ HasCount τ 2) ∨
    (Nonempty (σ.Equiv S) ∧ HasCount τ 3) ∨
    (Nonempty (σ.Equiv (BinaryLinearThree.W.prod S)) ∧ HasCount τ 4) ∨
    (Nonempty (σ.Equiv (U₂.prod S)) ∧ HasCount τ 5) := by
  dsimp only
  change Nonempty (σ.Equiv BinaryLinearThree.W) ∨ Nonempty (σ.Equiv U₂) ∨
    Nonempty (σ.Equiv S) ∨ Nonempty (σ.Equiv (BinaryLinearThree.W.prod S)) ∨
    Nonempty (σ.Equiv (U₂.prod S)) at hc
  rcases hc with hh | hh | hh | hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (natural_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (core_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩)
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (steinberg_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩))
  · obtain ⟨e⟩ := hh
    have ee : Representation.Equiv ((BinaryLinearThree.W.prod S).comp actor.subtype)
        (σ.comp actor.subtype) := .mk e.symm.toLinearEquiv
          (fun a => e.symm.toIntertwiningMap.isIntertwining' a.val)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (natural_prod_steinberg_count.mapEquiv ee)⟩)))
  · obtain ⟨e⟩ := hh
    have ee : Representation.Equiv ((U₂.prod S).comp actor.subtype)
        (σ.comp actor.subtype) := .mk e.symm.toLinearEquiv
          (fun a => e.symm.toIntertwiningMap.isIntertwining' a.val)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (core_prod_steinberg_count.mapEquiv ee)⟩)))

open BinaryLinearThree.ParabolicCyclic in
/-- The original R/V has one of the five actual H.6.5 module structures.
The quotient map, parabolic orientation, natural-to-dual equivalence and
literal conjugation section are retained in the same witness. -/
theorem extraspecial_span_module_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ)
      (e : MulAut BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group W),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      σ.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)) = ρ.comp (inclusion le_sup_left) ∧
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) ∧
      Alternatives σ ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ BinaryLinearThree.ParabolicCyclic.ChiefCounts.HasCount
        (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) n := by
  obtain ⟨W,ha,hm,ρ,s,hker,_,_⟩ :=
    extraspecial_span_binary_section h hab structural previous faithful he
  obtain ⟨τ,hτ⟩ := ExtraspecialSpanRecognition_spanRecognition_descent h structural ρ hker
  obtain ⟨e,hS,hP,hdual⟩ := SpanMarking.exists_marking h F (h.sylow_normalizes_at structural)
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let σ := τ.comp e.toMonoidHom
  have hσ : σ.comp q = ρ.comp (inclusion le_sup_left) := by
    calc _ = τ.comp (SpanMarking.qL h) := by
           ext l w
           change τ (e (e.symm (SpanMarking.qL h l))) w = _
           rw [e.apply_symm_apply]
           rfl
         _ = _ := hτ
  have hq : Function.Surjective q := e.symm.surjective.comp (SpanMarking.qL_surjective h)
  obtain ⟨w,_,_,hfix,hgen,hplane,hd⟩ :=
    extraspecial_span_cyclic_seed h hab structural previous faithful he s
  have hfixed : ∀ a ∈ Matrix.PSL3Two.borelSL, σ a w = w := by
    intro a ha
    rw [←hS] at ha
    obtain ⟨l,hl,rfl⟩ := ha
    have hh := congrArg (fun ψ : Representation (ZMod 2) L W => ψ l w) hσ
    exact hh.trans (hfix l hl)
  have hfull : orbitSpan σ ⊤ w = ⊤ := by
    rw [←map_top_of_surjective q hq,ExtraspecialSpanRecognition_spanRecognition_orbit_map,hσ]
    exact hgen
  have hdim : Module.finrank (ZMod 2) (orbitSpan σ Matrix.PSL3Two.lineParabolicSL w) = 2 := by
    rw [←hP,ExtraspecialSpanRecognition_spanRecognition_orbit_map,hσ]
    exact hd
  have hclass := parabolic_seed_alternatives σ w hfixed hfull hdim
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,?_⟩
  rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
  · exact ⟨1,by omega,by omega,hh.2⟩
  · exact ⟨2,by omega,by omega,hh.2⟩
  · exact ⟨3,by omega,by omega,hh.2⟩
  · exact ⟨4,by omega,by omega,hh.2⟩
  · exact ⟨5,by omega,by omega,hh.2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The dual-natural commutator span in the central branch

In case (i) of 14.7.20(2), R ≤ C_H(U) and U ∩ R = E imply [R,L₁] ≤ E.
Thus E/V is an irreducible noncentral plane and R/E is central for L₁.
Refine the central upper interval to an actual chief series; exactly one
factor is noncentral. The five proved model counts exclude all but the
natural module in the switched marking. Undoing that marking gives an
explicit equivalence with the dual of the original natural L-action.

The final original-group application strengthens the existing centralizer
alternatives by this recognition. The faithful order-64 branch keeps its
exact kernel and both central flanks; its further reduction remains open.
Source: Aschbacher–Smith 14.7.23(1), printed pp.1050–1051,
refs/quasithin.pdf. Structural1222, Theorem12213 and the earlier faithful
classification retain their existing producers and final discharge with
qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- In the central alternative of 14.7.20(2), the actual E/V plane is the
only noncentral L₁-chief factor on R/V. -/
theorem extraspecial_span_count_one_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1 := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hcomm : ⁅F.Li L 1,R⁆ ≤ ⁅F.U,Q T L⁆ := by
    rw [←hinter]
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono (hRC.trans inf_le_right) (pointResidual_le F)).trans hc
    · exact le_normalizer_iff_commutator_le_right.mp
        ((((F.Li_le L 1).trans inf_le_left).trans le_sup_left).trans s.normalized)
  obtain ⟨D,hD,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hupper : Central D ⊤ := by
    intro a w _
    change ρ (j a) w - w ∈ D.toSubmodule
    rw [hD]
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator (F.Li L 1) R
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,
      s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,w,Submodule.mem_top,rfl⟩
  have hlower : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    apply hatom.ne_bot
    apply le_antisymm _ bot_le
    intro w hw
    have hfix : ρ a w = w := sub_eq_zero.mp (htriv ⟨a,ha⟩ w hw)
    have hh := hn w (hD ▸ hw)
    rw [hfix,hfix] at hh
    have hww : w+w=0 := by
      calc w+w = (2 : ZMod 2) • w := (two_smul (ZMod 2) w).symm
           _ = 0 := by simp
    change w = 0
    simpa only [hww,zero_add] using hh
  simpa only [HasCount,Nat.add_zero] using
    exists_series_count_join
      (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hlower)
      (exists_central_series D ⊤ le_top hupper)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The central branch of 14.7.23 identifies the actual R/V with the dual
of the original natural action, through the original quotient map on L. -/
theorem extraspecial_span_dual_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
        (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
        (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
      HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
        (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1 := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,_,hP,⟨ed⟩,hclass,_⟩ :=
    extraspecial_span_module_alternatives h hab structural previous faithful he
  have hcount := extraspecial_span_count_one_of_central h hab structural previous faithful he hc s
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  have hnat : Nonempty (σ.Equiv BinaryLinearThree.W) := by
    rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
    · exact hh.1
    all_goals have := hcount.unique hh.2; omega
  obtain ⟨en⟩ := hnat
  refine ⟨W,ha,hm,ρ,s,hker,?_,hcount⟩
  rw [←hσ]
  exact ⟨(restrictEquiv en q).trans (restrictEquiv ed (SpanMarking.qL h))⟩

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Original-group application: the centralizer alternatives now carry the
proved dual-natural R/V recognition in the central case. The faithful
order-64 interval retains its exact kernel and both central flanks. -/
theorem extraspecial_span_central_or_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      ((⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∧
        ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
          (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
          (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
            (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ),
          (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
          Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
            (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
          HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
            (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1) ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  obtain ⟨hp,hc | hf⟩ := extraspecial_centralizer_core_reduction_no_small_intervals
    h hab structural previous faithful he
  · exact ⟨hp,Or.inl ⟨hc,extraspecial_span_dual_of_central h hab structural previous faithful he hc⟩⟩
  · exact ⟨hp,Or.inr hf⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original commutator span inside a faithful chief interval

In the faithful case of 14.7.20(2), the selected critical involution has a
square root in the literal Q. The commuting point cubic is fixed-free on
the six-dimensional chief action. Even kernel dimensions identify the root's
fixed plane with the involution's displacement. Since [R,Q] = V and
[Uα,B] ≤ [S,Q] = R, that plane is exactly the image of R in B/N and the
full Q-fixed space. Its point-residual action is irreducible and noncentral.

The final application constructs the original chief coordinates, proves
N's relative index in R ∩ B is four, and retains the exact action kernel
O₂(H) and both central flanks. The count on all of R/V and its Core
recognition are separate subsequent steps; neither is assumed here.
Source: Aschbacher–Smith 14.7.23(2), printed pp.1050–1051,
refs/quasithin.pdf. The stated earlier source implications retain their
existing producers and final discharge with qt-d-14775-source.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_faithful_chief_span_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) =
      s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
    Module.finrank (ZMod 2) (s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L)) = 2 ∧
    ∀ w ∈ s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L),
      (∀ a : F.Li L 1, ρ (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) → w = 0 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_point_noncentral_chief
    h hab structural previous hex hcard hexp hB hUN s hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let Z := star F (F.Li L 1)
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZc : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  have hZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZc)
  have hfixed : invariants (σ.comp Z.subtype) = ⊥ := by
    by_contra hh
    have hk := le_ker_of_normal_invariants_ne_bot σ Z hh
    have hb : Z = ⊥ := by
      apply bot_unique
      intro z hz
      exact hf ((hk hz).trans (map_one σ).symm)
    have hz1 : Nat.card Z = 1 := by rw [hb]; exact Nat.card_unique
    omega
  have hfree (w : W) (hw : ∀ a : F.Li L 1,
      ρ (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) : w = 0 := by
    have hh : w ∈ invariants (σ.comp Z.subtype) := by
      rintro ⟨z,hz⟩
      obtain ⟨a,ha,rfl⟩ := hz
      change σ (starMap F a) w = w
      rw [show σ (starMap F a) = ρ a from congrArg (fun ψ => ψ a) hσ]
      exact hw ⟨a,ha⟩
    simpa only [hfixed,Submodule.mem_bot] using hh
  obtain ⟨a,b,ha,hane,ha2,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hExp : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hlo : 2 ≤ Module.finrank (ZMod 2) (ρ a-1).range := by
    by_contra hh
    have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
      rw [fixedCodim_zpowers_eq_displacement_rank]
      change Module.finrank (ZMod 2) (σ.comp (starMap F) a-1).range ≤ 1
      rw [hσ]
      omega
    exact hane (ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP hExp
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
      (starMap F a) ha2 hsmall)
  have hr : Module.finrank (ZMod 2) (ρ a-1).range = 2 := le_antisymm
    (extraspecial_centralizer_section_displacement h hab structural previous hex hcard hexp c hs hB hUN s a ha) hlo
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z : Z, Commute (σ z) (σ (starMap F b)) := by
    intro z
    exact (show Commute (z : HStar F.H) (starMap F b) from
      point_core_star_centralizes_of_normal h structural hn hbR z z.property).map σ
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have h4 : (σ (starMap F b))^4=1 := by
    rw [←map_pow,show (starMap F b)^4=1 from hbo ▸ pow_orderOf_eq_one _,map_one]
  obtain ⟨heq,hk⟩ := order_four_fixed_plane_of_commuting_three_group σ Z hZ hfixed hd _ h4
    (by rw [hsq,show σ (starMap F a)=ρ a from congrArg (fun ψ => ψ a) hσ]; exact hr) hcomm
  rw [hsq,show σ (starMap F a)=ρ a from congrArg (fun ψ => ψ a) hσ,
    show σ (starMap F b)=ρ b from congrArg (fun ψ => ψ b) hσ] at heq
  rw [show σ (starMap F b)=ρ b from congrArg (fun ψ => ψ b) hσ] at hk
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have hRQ : ⁅Q T L,R⁆ ≤ N := by
    rw [commutator_comm,extraspecial_commutator_span_core_eq_seed h hab structural previous faithful ⟨e⟩ c hs]
    exact (le_conjugateSpanBy V F.H).trans hUN
  have hfixR : s.imageSpace R ≤ invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) := by
    intro w hw q
    exact s.fixed_on_imageSpace_of_commutator_le (Q T L) R hRQ q q.property w hw
  have hfixb : invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) ≤ (ρ b-1).ker := by
    intro w hw
    exact sub_eq_zero.mpr (hw ⟨b,hb⟩)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hCT : centralizer (F.U : Set G) ≤ (T : Subgroup G) :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hBQ : B ≤ Q T L := by
    change B ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←h.centralizer_LT_at structural]
    exact le_inf ((hB.trans hCT).trans le_sup_right)
      (hB.trans (centralizer_le (le_conjugateSpanBy V F.H)))
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful ⟨e⟩ c hs
  have hAS : c.Uα ≤ conjugateSpanBy F.U L := by
    rw [←hgU,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨g,hg⟩ : L) le_rfl
  have hmove : ⁅c.Uα,B⁆ ≤ R := by
    exact (commutator_mono hAS hBQ).trans_eq (original_span_core_commutator h hab structural)
  have hrR : (ρ a-1).range ≤ s.imageSpace R :=
    s.displacement_range_le_imageSpace_of_commutator_le c.Uα R hmove a ha
  have hR : s.imageSpace R = (ρ b-1).ker :=
    le_antisymm (hfixR.trans hfixb) (heq.symm ▸ hrR)
  exact ⟨le_antisymm (hfixb.trans hR.symm.le) hfixR,by rw [hR]; exact hk,fun w _ => hfree w⟩


private theorem ExtraspecialSpanFaithfulPlane_spanFaithful_irreducible_plane
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) A X) (hd : Module.finrank (ZMod 2) X = 2)
    (hf : ∀ x, (∀ a, τ a x = x) → x = 0) : τ.IsIrreducible := by
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) X)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun N => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  by_cases ht : N = ⊤
  · exact Or.inr ht
  exfalso
  have hNb : N.toSubmodule ≠ ⊥ := fun hh => hb (Subrepresentation.toSubmodule_injective hh)
  have hNt : N.toSubmodule ≠ ⊤ := fun hh => ht (Subrepresentation.toSubmodule_injective hh)
  have hpos : 0 < Module.finrank (ZMod 2) N.toSubmodule :=
    Nat.pos_of_ne_zero (fun hh => hNb (Submodule.finrank_eq_zero.mp hh))
  have hlt := Submodule.finrank_lt hNt
  have hdim : Module.finrank (ZMod 2) N.toSubmodule = 1 := by omega
  apply hNb
  apply bot_unique
  intro x hx
  exact hf x (fun a => by
    have hh := BinaryParabolicNatural.linear_one_trivial hdim
      (LinearMap.GeneralLinearGroup.toLinearEquiv (N.toRepresentation.asGroupHom a))
    exact congrArg (fun f : N.toSubmodule ≃ₗ[ZMod 2] N.toSubmodule => (f ⟨x,hx⟩ : X)) hh)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The faithful chief interval meets the original commutator span in one
noncentral irreducible plane for the literal point residual. -/
theorem extraspecial_faithful_chief_span_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right))),
      D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
      Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
      IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
      invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace R
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem R (j a)
      ((original_commutator_span_normalized h structural).1
        ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 a.property).1)) w hw }
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨hfixed,hd,hfree⟩ :=
    extraspecial_faithful_chief_span_plane h hab structural previous faithful he hB hUN s hm c hs
  have hirr : IsIrreducible D.toRepresentation := ExtraspecialSpanFaithfulPlane_spanFaithful_irreducible_plane _ hd (by
    intro w hw
    apply Subtype.ext
    exact hfree w w.property (fun a => congrArg Subtype.val (hw a)))
  refine ⟨D,rfl,hd,hirr,?_,hfixed⟩
  intro hc
  have hz : D = ⊥ := by
    apply bot_unique
    intro w hw
    exact hfree w hw (fun a => sub_eq_zero.mp (hc a w hw))
  have hh : Module.finrank (ZMod 2) D.toSubmodule = 0 := by
    rw [hz]
    exact finrank_bot _ _
  change Module.finrank (ZMod 2) D.toSubmodule = 2 at hd
  omega


open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The original order-64 interval has an actual irreducible noncentral
intersection with R, of relative index four and equal to its full Q-fixed space. -/
theorem extraspecial_span_faithful_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) F.H W)
      (s : BinaryConjugationSection F.H (B.val.map F.H.subtype) (N.val.map F.H.subtype) ρ)
      (D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right)))),
      D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
      Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
      IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
      invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule ∧
      (N.val.map F.H.subtype).relIndex
        (conjugateSpanBy ⁅F.U,Q T L⁆ L ⊓ B.val.map F.H.subtype) = 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let C := (centralizer (F.U : Set G)).subgroupOf F.H
  have hC : IsPGroup 2 C :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  obtain ⟨c,hs,_⟩ := extraspecial_span_source_reduction h hab structural previous faithful he
  obtain ⟨D,hD,hd,hirr,hcentral,hfixed⟩ :=
    extraspecial_faithful_chief_span_irreducible h hab structural previous faithful he hBC hUN s hm c hs
  refine ⟨Additive (Section N B),inferInstance,inferInstance,ρ,s,D,hD,hd,hirr,hcentral,hfixed,?_⟩
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have him : s.imageSpace (R ⊓ B.val.map F.H.subtype) = s.imageSpace R := by
    apply le_antisymm (s.imageSpace_mono inf_le_left)
    intro w hw
    obtain ⟨b,hb,rfl⟩ := (s.mem_imageSpace_iff R w).mp hw
    exact (s.mem_imageSpace_iff _ _).mpr ⟨b,⟨hb,b.property⟩,rfl⟩
  have hc := s.imageSpace_card_eq_relIndex (R ⊓ B.val.map F.H.subtype) inf_le_right
  rw [him,←hD,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd] at hc
  exact hc.symm

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Original-source application of the faithful plane calculation. The
central case remains available; the faithful case retains the exact chief
action kernel and both central flanks, and constructs the intersected plane. -/
theorem extraspecial_span_central_or_faithful_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U ∧
          ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
            (ρ : Representation (ZMod 2) F.H W)
            (s : BinaryConjugationSection F.H (B.val.map F.H.subtype) (N.val.map F.H.subtype) ρ)
            (D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right)))),
            D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
            Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
            IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
            invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule ∧
            (N.val.map F.H.subtype).relIndex
              (conjugateSpanBy ⁅F.U,Q T L⁆ L ⊓ B.val.map F.H.subtype) = 4) := by
  obtain ⟨hp,hc | ⟨N,B,hNB,hUN,hBC,hm,hsize,hker,hupper,hlower⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · exact ⟨hp,Or.inl hc⟩
  · exact ⟨hp,Or.inr ⟨N,B,hNB,hUN,hBC,hm,hsize,hker,hupper,hlower,
      extraspecial_span_faithful_interval h hab structural previous faithful he N B hNB hUN hBC hm⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The two original module alternatives for R/V

The faithful chief interval meets R in a noncentral point-residual plane.
Compare its literal coordinates with R/V: its kernel is the image of the
original lower endpoint. Together with E/V, these give two noncentral
chief intervals. The original centralizer bounds make both intervening
gaps central. Refining the gaps proves an exact count of two.

The five marked H.6.5 alternatives have counts one through five, so only
the six-dimensional core survives in the faithful branch. The original
central branch has count one and is dual-natural. The final original-group
application discharges the chief-interval premises and retains the actual
L quotient map, dual marking, exact H-kernel and both central flanks.

Source: Aschbacher–Smith 14.7.23, printed pp.1050–1051,
refs/quasithin.pdf. The retained earlier source implications have their
existing producers; their final discharge remains with qt-d-14775-source.
Maximal-normalizer control and the later local residual reductions through
14.7.52 remain open.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}




open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The faithful interval contributes precisely one further noncentral factor
to R/V, in addition to E/V. Both gaps are the original central flanks. -/
theorem extraspecial_span_count_two_of_faithful_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype)
    (hupper : ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype)
    (hlower : ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V τ) :
    HasCount (τ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  let : Finite X := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let E := ⁅F.U,Q T L⁆
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hnorm (D : NormalNode F.H) : F.H ≤ normalizer (D.val.map F.H.subtype : Set G) := by
    have hh := (map_mono (f := F.H.subtype)
      (show (⊤ : Subgroup F.H) ≤ normalizer (D.val : Set F.H) from le_normalizer_of_normal)).trans
        (D.val.le_normalizer_map F.H.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  let I (D : NormalNode F.H) : Subrepresentation (τ.comp j) := {
    toSubmodule := s.imageSpace (D.val.map F.H.subtype)
    apply_mem_toSubmodule a x hx := s.imageSpace_apply_mem _ (j a)
      (hnorm D (F.Li_le L 1 a.property).2) x hx }
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  obtain ⟨D,hD,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hDN : D ≤ I N := by
    change D.toSubmodule ≤ s.imageSpace (N.val.map F.H.subtype)
    rw [hD]
    exact s.imageSpace_mono ((hinter.symm.le.trans inf_le_left).trans hUN)
  have hIB : I N ≤ I B := s.imageSpace_mono (map_mono hNB.le)
  have hcentral₀ : Central D (I N) := by
    have hcomm : ⁅F.Li L 1,R ⊓ N.val.map F.H.subtype⁆ ≤ E := by
      change ⁅F.Li L 1,R ⊓ N.val.map F.H.subtype⁆ ≤ ⁅F.U,Q T L⁆
      rw [←hinter]
      apply le_inf
      · rw [commutator_comm]
        exact (commutator_mono inf_le_right (pointResidual_le F)).trans hlower
      · exact (commutator_mono le_rfl inf_le_left).trans
          (le_normalizer_iff_commutator_le_right.mp
            ((((F.Li_le L 1).trans inf_le_left).trans le_sup_left).trans s.normalized))
    intro a x hx
    change τ (j a) x-x ∈ D.toSubmodule
    rw [hD]
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) inf_le_left]
    apply Submodule.subset_span
    refine ⟨j a,a.property,x,?_,rfl⟩
    obtain ⟨r,hr,heq⟩ := (s.mem_imageSpace_iff _ x).mp hx
    exact (s.mem_imageSpace_iff _ x).mpr ⟨r,⟨r.property,hr⟩,heq⟩
  have hcentral₁ : Central (I B) ⊤ := by
    have hcomm : ⁅F.Li L 1,R⁆ ≤ B.val.map F.H.subtype := by
      rw [commutator_comm]
      exact (commutator_mono (hRC.trans inf_le_right) (pointResidual_le F)).trans hupper
    intro a x _
    change τ (j a) x-x ∈ s.imageSpace (B.val.map F.H.subtype)
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,x,Submodule.mem_top,rfl⟩
  have hnoncentral : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    apply hatom.ne_bot
    apply bot_unique
    intro x hx
    have hfix : τ a x=x := sub_eq_zero.mp (htriv ⟨a,ha⟩ x hx)
    have hh := hn x (hD ▸ hx)
    rw [hfix,hfix] at hh
    have hxx : x+x=0 := by
      calc x+x = (2 : ZMod 2) • x := (two_smul (ZMod 2) x).symm
           _ = 0 := by simp
    change x = 0
    simpa only [hxx,zero_add] using hh
  obtain ⟨Y,ha,hmY,ρ,t,J,hJ,_,hJirr,hJnc,_,_⟩ :=
    extraspecial_span_faithful_interval h hab structural previous faithful he N B hNB hUN hBC hm
  let : J.toRepresentation.IsIrreducible := hJirr
  obtain ⟨f,hf,hk⟩ := BinaryConjugationSection.exists_intersection_intertwiner
    (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
    ((F.Li_le L 1).trans inf_le_right) s t ((le_conjugateSpanBy V F.H).trans hUN)
    (I N) (I B) J rfl rfl hJ
  have hJmove : ¬ ∀ a y, J.toRepresentation a y = y := by
    intro htriv
    apply hJnc
    intro a y hy
    exact sub_eq_zero.mpr (congrArg Subtype.val (htriv a ⟨y,hy⟩))
  obtain ⟨hcover,hnc⟩ := BinaryConjugationSection.chief_interval_of_surjective_intertwiner (ν := J.toRepresentation) (I N) (I B) hIB f hf hk hJmove
  have h01 := exists_series_count_join
    (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hnoncentral)
    (exists_central_series D (I N) hDN hcentral₀)
  have h012 := exists_series_count_join h01
    (exists_noncentral_chief_series (I N) (I B) hcover hnc)
  simpa only [HasCount,Nat.add_zero,Nat.reduceAdd] using exists_series_count_join h012
    (exists_central_series (I B) ⊤ le_top hcentral₁)

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic
  BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Source 14.7.23's two module alternatives for the original R/V. The
central case is the dual-natural action; the faithful case is the six-dimensional
permutation core under the same dual marking. The original quotient map,
point-parabolic marking, chief kernels, and both central flanks are retained. -/
theorem extraspecial_span_two_module_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ)
      (e : MulAut BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group W),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      σ.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)) = ρ.comp (inclusion le_sup_left) ∧
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) ∧
      ((⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∧
        Nonempty (σ.Equiv BinaryLinearThree.W) ∧
        Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
          (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
        HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1) ∨
       (Nonempty (σ.Equiv BinaryLinearThree.U₂) ∧
        Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
          (BinaryLinearThree.U₂.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)))) ∧
        HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 ∧
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,_⟩ :=
    extraspecial_span_module_alternatives h hab structural previous faithful he
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,?_⟩
  obtain ⟨_,hc | ⟨N,B,hNB,hUN,hBC,hmove,hsize,hkernel,hupper,hlower⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · have hcount := extraspecial_span_count_one_of_central h hab structural previous faithful he hc s
    have hnat : Nonempty (σ.Equiv BinaryLinearThree.W) := by
      rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
      · exact hh.1
      all_goals have := hcount.unique hh.2; omega
    obtain ⟨en⟩ := hnat
    obtain ⟨ed⟩ := hdual
    refine Or.inl ⟨hc,⟨en⟩,?_,hcount⟩
    rw [←hσ]
    exact ⟨(restrictEquiv en q).trans (restrictEquiv ed (SpanMarking.qL h))⟩
  · have hcount := extraspecial_span_count_two_of_faithful_interval h hab structural previous faithful he
      N B hNB hUN hBC hmove hupper hlower s
    have hcore : Nonempty (σ.Equiv BinaryLinearThree.U₂) := by
      rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
      · have := hcount.unique hh.2; omega
      · exact hh.1
      all_goals have := hcount.unique hh.2; omega
    obtain ⟨ec⟩ := hcore
    refine Or.inr ⟨⟨ec⟩,?_,hcount,N,B,hNB,hUN,hBC,hmove,hsize,hkernel,hupper,hlower⟩
    rw [←hσ]
    exact ⟨restrictEquiv ec q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# A central seed in the original faithful core branch

The marked Fano core contains a nonzero fixed displacement for L₁.
Lift its displacement through the literal R/V coordinates. It belongs to
O₂(K) and the upper chief endpoint. Its image in the faithful chief plane
is fixed by L₁, hence zero, so it belongs to the lower endpoint as well.
The cubic norm on E/V proves that this lift lies outside U.

Taking the fixed-space preimage and intersecting the original endpoints
produces C ≤ O₂(K) with C not contained in U, [C,L₁] ≤ V and [C,K] ≤ U.
The actual original-group application assumes only the faithful branch
of the already proved 14.7.23 alternatives and the named earlier inputs.

Source: Aschbacher–Smith 14.7.25, printed pp.1051–1052, refs/quasithin.pdf.
The faithful central-subgroup application is in ExtraspecialCentralSubgroup;
the central branch of 14.7.24 and maximal-normalizer control remain separate.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialCentralSeed_centralSeed_point_image
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL) :
    ((F.Li L 1).subgroupOf L).map q = actor := by
  have he : (F.Li L 1).subgroupOf L =
      (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
      map_embedded_pResidual,subgroupOf_map_subtype]
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,↓reduceIte]
    change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
    rw [inf_comm]
  rw [he,map_embedded_pResidual,hP]
  rfl

/-- The faithful core alternative supplies an actual subgroup outside U,
inside both the residual two-core and the lower central flank, whose
point-residual displacement lies in V. -/
theorem extraspecial_faithful_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ C : Subgroup G, C ≤ (K F).pCoreIn 2 ∧ ¬ C ≤ F.U ∧
      C ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L ∧
      ⁅C,F.Li L 1⁆ ≤ V ∧ ⁅C,K F⁆ ≤ F.U := by
  obtain ⟨X,ha,hm,τ,s,e,σ,_,hσ,_,hP,_,hc | ⟨⟨ec⟩,_,_,N,B,hNB,hUN,hBC,hmov,_,_,hupper,hlower⟩⟩ :=
    extraspecial_span_two_module_alternatives h hab structural previous faithful he
  · exact (hnc hc.1).elim
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hmap := ExtraspecialCentralSeed_centralSeed_point_image q hP
  have hq (a : F.Li L 1) : q ⟨a,(F.Li_le L 1 a.property).1⟩ ∈ actor := by
    rw [←hmap]
    exact ⟨⟨a,(F.Li_le L 1 a.property).1⟩,a.property,rfl⟩
  have hact (a : F.Li L 1) (v : X) :
      ec (τ (j a) v) = BinaryLinearThree.U₂ (q ⟨a,(F.Li_le L 1 a.property).1⟩) (ec v) := by
    have hh := congrArg (fun ψ : Representation (ZMod 2) L X =>
      ψ ⟨a,(F.Li_le L 1 a.property).1⟩ v) hσ
    change σ (q ⟨a,(F.Li_le L 1 a.property).1⟩) v = τ (j a) v at hh
    exact (congrArg ec hh.symm).trans (IntertwiningMap.isIntertwining _ _ ec.toIntertwiningMap _ _)
  obtain ⟨v,w,a,hv,hfix,hdisp⟩ := BinaryLinearThree.core_exists_fixed_displacement
  let v' := ec.symm v
  let w' := ec.symm w
  have hv' : v' ≠ 0 := by
    intro hh
    apply hv
    have := congrArg ec hh
    simpa only [v',ec.apply_symm_apply,map_zero] using this
  have hfixed (b : F.Li L 1) : τ (j b) v' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j b) v') = ec v'
    rw [hact,ec.apply_symm_apply,hfix ⟨_,hq b⟩]
  have ham : (a : BinaryLinearThree.Group) ∈ ((F.Li L 1).subgroupOf L).map q := by
    rw [hmap]
    exact a.property
  obtain ⟨aL,haL,haq⟩ := ham
  let a₁ : F.Li L 1 := ⟨aL,haL⟩
  have hdisplacement : τ (j a₁) w' - w' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j a₁) w' - w') = ec v'
    rw [map_sub,hact,ec.apply_symm_apply,ec.apply_symm_apply]
    change BinaryLinearThree.U₂ (q aL) w - w = v
    rw [haq]
    exact hdisp
  have hvcomm : v' ∈ s.imageSpace ⁅F.Li L 1,R⁆ := by
    rw [s.imageSpace_commutator (F.Li L 1) R
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a₁,a₁.property,w',Submodule.mem_top,hdisplacement.symm⟩
  obtain ⟨x,hxcomm,hxcoord⟩ := (s.mem_imageSpace_iff ⁅F.Li L 1,R⁆ v').mp hvcomm
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hxB : (x:G) ∈ B.val.map F.H.subtype := by
    apply hupper
    rw [commutator_comm] at hxcomm
    exact commutator_mono (hRC.trans inf_le_right) (pointResidual_le F) hxcomm
  have hRP : ⁅R,F.Li L 1⁆ ≤ (K F).pCoreIn 2 := by
    have hRH : R ≤ F.H := hRC.trans inf_le_left
    have hRK : R ≤ normalizer (K F : Set G) := hRH.trans (H_normalizes_K F)
    have hcommK : ⁅R,K F⁆ ≤ K F := le_normalizer_iff_commutator_le_right.mp hRK
    have hRcore : R ≤ F.H.pCoreIn 2 := by
      let := h.chosen.elementary
      let := hab
      let := elementary_U F
      obtain ⟨ρ,⟨sU⟩⟩ := exists_section F
      exact (hRC.trans inf_le_right).trans
        (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show K F ≤ F.H from map_subtype_le _))
    apply le_inf
    · exact (commutator_mono le_rfl (pointResidual_le F)).trans hcommK
    · exact (commutator_mono hRcore le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (((F.Li_le L 1).trans inf_le_right).trans
            (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))))
  have hxP : (x:G) ∈ (K F).pCoreIn 2 := by
    apply hRP
    rwa [commutator_comm]
  have hxN : (x:G) ∈ N.val.map F.H.subtype := by
    let C := (centralizer (F.U : Set G)).subgroupOf F.H
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    obtain ⟨ρU,⟨sU⟩⟩ := exists_section F
    have hC : IsPGroup 2 C :=
      ((isPGroup_pCoreIn 2 F.H).to_le
        (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
    have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
    let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
    let ρ := binarySectionRepresentation N B
    let : ρ.IsIrreducible := binarySection_irreducible N B hNB
    let t := ambientBinarySection F.H N B hNB.le
    have hVN : V ≤ N.val.map F.H.subtype := (le_conjugateSpanBy V F.H).trans hUN
    obtain ⟨_,_,hfree⟩ := extraspecial_faithful_chief_span_plane
      h hab structural previous faithful he hBC hUN t hmov c hs
    apply (t.coordinates_eq_one_iff ⟨x,hxB⟩).mp
    apply hfree
    · exact (t.mem_imageSpace_iff R _).mpr ⟨⟨x,hxB⟩,x.property,rfl⟩
    · intro b
      apply (t.fixed_coordinate_iff_commutator_mem (inclusion ((F.Li_le L 1).trans inf_le_right) b) ⟨x,hxB⟩).mpr
      apply hVN
      apply (s.fixed_coordinate_iff_commutator_mem (j b) x).mp
      rw [hxcoord]
      exact hfixed b
  have hxU : (x:G) ∉ F.U := by
    intro hx
    obtain ⟨b,hb,hnorm⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    have him : v' ∈ s.imageSpace ⁅F.U,Q T L⁆ := by
      apply (s.mem_imageSpace_iff _ _).mpr
      exact ⟨x,hinter.le ⟨hx,x.property⟩,hxcoord⟩
    have hbfix : τ b v' = v' := hfixed ⟨b,hb⟩
    have hh := hnorm v' him
    rw [hbfix,hbfix] at hh
    have htwo : v'+v'=0 := by
      calc v'+v' = (2 : ZMod 2) • v' := (two_smul (ZMod 2) v').symm
           _ = 0 := by simp
    exact hv' (by simpa only [htwo,zero_add] using hh)
  let I := fixedSpace τ ((F.Li L 1).subgroupOf (L ⊔ (T : Subgroup G)))
  let C := s.subspacePreimage I ⊓ N.val.map F.H.subtype ⊓ (K F).pCoreIn 2
  have hxC : (x:G) ∈ C := by
    refine ⟨⟨(s.mem_subspacePreimage I x).mpr ⟨x.property,?_⟩,hxN⟩,hxP⟩
    intro b
    rw [hxcoord]
    exact hfixed ⟨b.val,b.property⟩
  refine ⟨C,inf_le_right,(fun hc => hxU (hc hxC)),
    (inf_le_left.trans inf_le_left).trans (s.subspacePreimage_le I),?_,?_⟩
  · rw [commutator_comm]
    apply s.commutator_le_of_imageSpace_fixed (F.Li L 1) C
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
      ((inf_le_left.trans inf_le_left).trans (s.subspacePreimage_le I))
    exact (s.imageSpace_mono (inf_le_left.trans inf_le_left)).trans
      (s.imageSpace_subspacePreimage I).le
  · exact (commutator_mono (inf_le_left.trans inf_le_right) le_rfl).trans hlower

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The central subgroup in the original faithful branch

Adjoin U to the central seed C constructed from the actual permutation core.
The lower chief flank makes CU invariant under K. Its commutator with
P = O₂(K) lies in V. Irreducibility of K on the original U/V₁ section
reduces this commutator to V₁, retaining the exact original quotient map.

The point residual has two-core P and cubic quotient. Coprime fixed-point
lifting and two-perfect commutator idempotence therefore give an element
of Z(P) outside U. The proved center control Z(P) ≤ Z(K) gives V₁ < Z(K).
An invariant index-two step above V₁ in Z(P) constructs an actual subgroup
of order four, central in K and normalized by H = KT.

Source: the faithful case of Aschbacher–Smith 14.7.25 and the following
choice of D, printed pp.1051–1052, refs/quasithin.pdf. The original flag,
point normality and named earlier implications remain intact. Their final
source discharge stays with the existing qt-d-14775-source producers.
The central case of 14.7.24, maximal-normalizer control and the remaining
reductions through 14.7.52 are not asserted here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialCentralSubgroup_centralSeed_residual_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    IsIrreducible (ρ.comp (inclusion (K_le_H F))) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,_,_,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let q := (residualStarEquiv F).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F)))
  have hq : Function.Surjective q := (residualStarEquiv F).surjective.comp (QuotientGroup.mk'_surjective _)
  have heq : (σ.comp (pResidual 2 (HStar F.H)).subtype).comp q =
      ρ.comp (inclusion (K_le_H F)) := by
    ext k w
    change σ (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k)) w = _
    rw [residualStarEquiv_mk]
    exact congrArg (fun τ : Representation (ZMod 2) F.H W => τ (inclusion (K_le_H F) k) w) hσ
  exact heq ▸ (irreducible_comp_surjective_iff q hq _).mpr hi

omit [Finite G] in
private theorem ExtraspecialCentralSubgroup_centralSeed_normalizes_commutator (A B C : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hAC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer ((⁅B,C⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hAB ha),mem_normalizer_iff_map_conj_eq.mp (hAC ha)]

/-- A literal central seed outside U forces the strict central-subgroup
conclusion. The seed's commutators, residual-core placement and genuine
earlier source implications are all explicit here. -/
theorem extraspecial_core_center_strict_of_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (C : Subgroup G) (hCP : C ≤ (K F).pCoreIn 2) (hCU : ¬ C ≤ F.U)
    (hCA : ⁅C,F.Li L 1⁆ ≤ V) (hCK : ⁅C,K F⁆ ≤ F.U) :
    F.Vi 1 < (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype := by
  let P := (K F).pCoreIn 2
  let A := F.Li L 1
  let D := C ⊔ F.U
  have hUP : F.U ≤ P := span_le_residual_core h hab
  have hDP : D ≤ P := sup_le hCP hUP
  have hPH : P ≤ F.H := (pCoreIn_le 2 _).trans (K_le_H F)
  have hcore : A.pCoreIn 2 = P :=
    (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  have hPA : P ≤ A := hcore ▸ pCoreIn_le 2 A
  have hAK : A ≤ K F := pointResidual_le F
  have hAH : A ≤ F.H := hAK.trans (K_le_H F)
  have hHnU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hPnU : P ≤ normalizer (F.U : Set G) := hPH.trans hHnU
  have hDK : ⁅D,K F⁆ ≤ F.U := by
    have hn := commutator_commutatorPreimage_le P (K F) F.U hPnU
    have hD : D ≤ commutatorPreimage P (K F) F.U := sup_le
      (le_commutatorPreimage hCP hCK)
      (le_commutatorPreimage hUP (le_normalizer_iff_commutator_le_left.mp ((K_le_H F).trans hHnU)))
    exact (commutator_mono hD le_rfl).trans hn
  have hKnD : K F ≤ normalizer (D : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hDK.trans le_sup_right)
  have hKnP : K F ≤ normalizer (P : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))
  have hPnV : P ≤ normalizer (V : Set G) :=
    (hPA.trans ((F.Li_le L 1).trans inf_le_left)).trans h.chosen.normalizes
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUPcomm : ⁅F.U,P⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro p hp u hu
    apply (s.action_mem_ker_iff ⟨p,hPH hp⟩).mp _ u hu
    apply core_le_action_kernel h s
    have hcoreP : P ≤ F.H.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
    have hrelative : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
      comap_map_eq_self_of_injective F.H.subtype_injective _
    rw [←hrelative]
    exact hcoreP hp
  have hPV : ⁅D,P⁆ ≤ V := by
    have hD : D ≤ commutatorPreimage P P V := sup_le
      (le_commutatorPreimage hCP ((commutator_mono le_rfl hPA).trans hCA))
      (le_commutatorPreimage hUP (hUPcomm.trans (F.le_seed 1)))
    exact (commutator_mono hD le_rfl).trans (commutator_commutatorPreimage_le P P V hPnV)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) := by
    apply le_centralizer_iff.mp
    exact (K_le_H F).trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))
  let M := ⁅D,P⁆ ⊔ F.Vi 1
  have hMV : M ≤ V := sup_le hPV (F.le_seed 1)
  have hKnM : K F ≤ normalizer (M : Set G) :=
    (le_inf (ExtraspecialCentralSubgroup_centralSeed_normalizes_commutator (K F) D P hKnD hKnP)
      ((le_centralizer_iff.mp hpoint).trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : IsIrreducible (ρ.comp (inclusion (K_le_H F))) :=
    ExtraspecialCentralSubgroup_centralSeed_residual_irreducible h hab structural previous he s
  let t := s.restrictActor (K_le_H F) (hUP.trans (pCoreIn_le 2 _))
  have hUnM : ¬ F.U ≤ M := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion (hh.trans hMV)) (inclusion_injective _)
    rw [(extraspecial_source_reduction h hab structural previous he).2.1,h.seed_card] at hc
    omega
  have hPM : ⁅D,P⁆ ≤ F.Vi 1 := by
    rw [←t.inf_eq_kernel_of_irreducible M hKnM le_sup_right hUnM]
    exact le_inf (hPV.trans (le_conjugateSpanBy V F.H)) le_sup_left
  have hAp : IsPPerfect 2 A := by
    change IsPPerfect 2 (F.Li L 1)
    simp only [InvariantFlag.Li]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)
  have hfix : ¬ D ⊓ centralizer (A : Set G) ≤ F.U := by
    apply cubic_central_layer_lift A D F.U (F.Vi 1) hAp
      (pointResidual_core_quotient_card h structural)
      (hcore.symm ▸ hDP) le_sup_right (fun hh => hCU (le_sup_left.trans hh))
      (hAK.trans hKnD) (hAH.trans hHnU)
      (hpoint.trans (centralizer_le hAK))
      ((commutator_mono le_rfl hAK).trans hDK)
    rwa [hcore]
  have hcent : D ⊓ centralizer (A : Set G) ≤ (center P).map P.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf (inf_le_left.trans hDP) (inf_le_right.trans (centralizer_le hPA))
  have hVZ : F.Vi 1 ≤ (center P).map P.subtype := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact inf_le_right
  apply lt_of_le_not_ge hVZ
  intro hle
  exact hfix (hcent.trans (hle.trans s.kernel_le))

/-- Source 14.7.25 in the faithful alternative of 14.7.23. The actual core
marking constructs the central seed; no extra local recognition premise remains. -/
theorem extraspecial_center_strict_of_faithful
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    F.Vi 1 < (center (K F)).map (K F).subtype := by
  obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
    extraspecial_faithful_central_seed h hab structural previous faithful he hnc
  exact (extraspecial_core_center_strict_of_central_seed h hab structural previous faithful
    he C hCP hCU hCA hCK).trans_le
      (extraspecial_core_center_central d h hab structural previous faithful earlier he)

/-- The literal order-four subgroup needed immediately after 14.7.25, in
its faithful branch. It contains V₁, is central in K and is normalized by H. -/
theorem extraspecial_center_four_of_faithful
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ F.H ≤ normalizer (D : Set G) := by
  obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
    extraspecial_faithful_central_seed h hab structural previous faithful he hnc
  have hlt := extraspecial_core_center_strict_of_central_seed h hab structural previous faithful
    he C hCP hCU hCA hCK
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZK : Z ≤ (center (K F)).map (K F).subtype :=
    extraspecial_core_center_central d h hab structural previous faithful earlier he
  have hPT : P ≤ (T : Subgroup G) := by
    exact (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hZT : Z ≤ (T : Subgroup G) := (map_subtype_le _).trans hPT
  have hVT : F.Vi 1 ≤ (T : Subgroup G) := hlt.le.trans hZT
  have hHnZ : F.H ≤ normalizer (Z : Set G) :=
    ((H_normalizes_K F).trans
      (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  let V₀ := (F.Vi 1).subgroupOf (T : Subgroup G)
  let Z₀ := Z.subgroupOf (T : Subgroup G)
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (F.invariant 1)
  let : Z₀.Normal := normal_subgroupOf_of_le_normalizer ((F.invariant 1).trans hHnZ)
  have hlt₀ : V₀ < Z₀ := by
    apply lt_of_le_not_ge (subgroupOf_mono _ hlt.le)
    intro hh
    have hm := map_mono (f := (T : Subgroup G).subtype) hh
    rw [map_subgroupOf_eq_of_le hZT,map_subgroupOf_eq_of_le hVT] at hm
    exact hlt.not_ge hm
  obtain ⟨X,hX,hVX,hXZ,hindex⟩ := exists_normal_index_two_step
    (T : Subgroup G) T.isPGroup' V₀ Z₀ hlt₀
  let D := X.map (T : Subgroup G).subtype
  have hVD : F.Vi 1 ≤ D := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hVX
    rwa [map_subgroupOf_eq_of_le hVT] at hh
  have hDZ : D ≤ Z := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hXZ
    rwa [map_subgroupOf_eq_of_le hZT] at hh
  have hcard : Nat.card D = 4 := by
    have hmul := relIndex_mul_card_of_le hVX
    have hVcard : Nat.card V₀ = 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv]
      simpa using F.card 1 (by decide)
    rw [hindex,hVcard] at hmul
    rw [card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hmul.symm
  have hTnD : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    let : X.Normal := hX
    have hh := (map_mono (f := (T : Subgroup G).subtype)
      (show (⊤ : Subgroup (T : Subgroup G)) ≤ normalizer (X : Set (T : Subgroup G)) from
        le_normalizer_of_normal)).trans
      (X.le_normalizer_map (T : Subgroup G).subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨D,hVD,hDZ.trans hZK,hcard,?_⟩
  rw [residual_product]
  apply sup_le _ hTnD
  apply (le_centralizer_iff.mp _).trans (Subgroup.centralizer_le_normalizer _)
  rw [map_center_subtype_eq_inf_centralizer] at hZK
  exact hDZ.trans (hZK.trans inf_le_right)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The outer span's plane in the original residual-core quotient

Use the literal duality P/C_P(U) ≃ (U/V₁)*, where P = O₂(K). The
commutator [U,Q] has rank four modulo V₁, so the dual Q-fixed space
has dimension two. The image of S ∩ P lies in that fixed space, because
[S,Q] = R centralizes U. A critical involution's displacement has dimension
two and lifts into S ∩ P, proving equality. Full L₁-movement on U/V₁
also excludes L₁-fixed vectors on the dual.

Both original coordinate maps and the full C_P(U) kernel remain literal.
The application in ExtraspecialOuterCore uses this plane as the second
noncentral chief factor of S/R.
Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
The named earlier inputs retain their existing producers and final discharge
at qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original S-image in P/C_P(U) is exactly its Q-fixed plane; the
whole dual module has no nonzero L₁-fixed vector. -/
theorem extraspecial_core_outer_fixed_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (sP : BinaryConjugationSection F.H ((K F).pCoreIn 2)
      ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual) :
    fixedSpace ρ.dual ((Q T L).subgroupOf F.H) =
      sP.imageSpace (conjugateSpanBy F.U L) ∧
    Module.finrank (ZMod 2) (sP.imageSpace (conjugateSpanBy F.U L)) = 2 ∧
    ∀ w : Module.Dual (ZMod 2) W,
      (∀ a : F.Li L 1, ρ.dual (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) →
      w = 0 := by
  let : Finite W := Finite.of_surjective (fun u => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let P := (K F).pCoreIn 2
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let E := ⁅F.U,Q T L⁆
  let A := (Q T L).subgroupOf F.H
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨_,_,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp sU
  obtain ⟨c,hs,_,_,hEc,_,hSQ,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful ⟨e⟩
  have hEU : E ≤ F.U := hinter.symm.le.trans inf_le_left
  have hZE : F.Vi 1 ≤ E := by
    exact (F.le_seed 1).trans
      ((extraspecial_critical_commutator_eq_seed h hab structural previous faithful ⟨e⟩ c hs).symm.le.trans
        (commutator_mono le_rfl (critical_le_Q_at h structural c)))
  have hEi : (F.Vi 1).relIndex E = 16 := by
    have hh := relIndex_mul_card_of_le hZE
    have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hz,hEc] at hh
    omega
  have hEd := sU.imageSpace_finrank_of_index E hEU 4 hEi
  have hmove : subspaceCommutator ρ ⊤ A = sU.imageSpace E := by
    rw [←sU.imageSpace_self,←sU.imageSpace_commutator (Q T L) F.U (Q_le_H F) le_rfl]
    rw [commutator_comm]
  have hcodim : fixedCodim ρ.dual A = 4 := by
    rw [fixedCodim_dual_eq_moved_finrank,hmove,hEd]
  have hfixdim : Module.finrank (ZMod 2) (fixedSpace ρ.dual A) = 2 := by
    have hh := fixedCodim_add_finrank ρ.dual A
    rw [Subspace.dual_finrank_eq,hd,hcodim] at hh
    omega
  have hfixed : sP.imageSpace S ≤ fixedSpace ρ.dual A := by
    intro w hw a
    obtain ⟨p,hp,rfl⟩ := (sP.mem_imageSpace_iff S w).mp hw
    apply (sP.fixed_coordinate_iff_commutator_mem a p).mpr
    refine ⟨?_,?_⟩
    · exact (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_H F).trans sP.normalized))
        (commutator_mem_commutator p.property a.property)
    · apply hRC.trans inf_le_right
      apply hSQ.le
      exact commutator_mem_commutator hp a.property
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have haQ : a ∉ pCore 2 F.H := fun hh => hane ((QuotientGroup.eq_one_iff _).mpr hh)
  have hdis : Module.finrank (ZMod 2) (ρ a-1).range = 2 :=
    critical_displacement_two_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn sU c hs htwo a ha haQ
  have hdualdis : Module.finrank (ZMod 2) (ρ.dual a-1).range = 2 := by
    change Module.finrank (ZMod 2) (ρ.dual a-LinearMap.id).range = 2
    rw [←fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_dual,
      fixedCodim_zpowers_eq_displacement_rank]
    exact hdis
  have hPT : P ≤ (T : Subgroup G) := (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
    ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hPnS : P ≤ normalizer (S : Set G) := hPT.trans
    (normalizes_conjugateSpanBy F.U L (T : Subgroup G)
      ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (h.sylow_normalizes_at structural))
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful ⟨e⟩ c hs
  have hAS : c.Uα ≤ S := by
    change c.Uα ≤ conjugateSpanBy F.U L
    rw [←hgU,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨g,hg⟩ : L) le_rfl
  have hcomm : ⁅c.Uα,P⁆ ≤ S := (commutator_mono hAS le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hPnS)
  have hdispS : (ρ.dual a-1).range ≤ sP.imageSpace S :=
    sP.displacement_range_le_imageSpace_of_commutator_le c.Uα S hcomm a ha
  have hdim : Module.finrank (ZMod 2) (sP.imageSpace S) = 2 := by
    have hl := Submodule.finrank_mono hdispS
    have hu := Submodule.finrank_mono hfixed
    omega
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hfixed (hdim.trans hfixdim.symm)).symm,hdim,?_⟩
  let B := (F.Li L 1).subgroupOf F.H
  have hfull : subspaceCommutator ρ ⊤ B = ⊤ := by
    rw [←sU.imageSpace_self,←sU.imageSpace_commutator (F.Li L 1) F.U
      ((F.Li_le L 1).trans inf_le_right) le_rfl,
      commutator_comm,commutator_U_point_of_normal h hn,sU.imageSpace_self]
  have hdfull : fixedCodim ρ.dual B = 6 := by
    rw [fixedCodim_dual_eq_moved_finrank,hfull,finrank_top,hd]
  have hdbot : fixedSpace ρ.dual B = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hh := fixedCodim_add_finrank ρ.dual B
    rw [hdfull,Subspace.dual_finrank_eq,hd] at hh
    omega
  intro w hw
  have hh : w ∈ fixedSpace ρ.dual B := fun a => hw ⟨a,a.property⟩
  simpa only [hdbot,Submodule.mem_bot] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The generating plane in the original outer span quotient

For S = ⟨Uᴸ⟩ and R = ⟨[U,Q]ᴸ⟩, the Frattini identity Φ(S) = V ≤ R
makes the actual S/R elementary abelian. Its conjugation action is induced
by LT, and [S,Q] = R kills the literal Q. The intersection U ∩ R = E
and |U:E| = 4 give the generating plane U/E.

Transfer the point cubic's norm through the original quotient coordinates.
The resulting full movement makes U/E irreducible for L₁. A Sylow-fixed
nonzero vector is cyclic for the plane and then for S/R. These supply the
original inputs to H.6.5 in the central branch of 14.7.24. They also hold
before choosing a centralizer branch. No Core recognition is assumed.

Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
Genuine earlier structural and faithful-classification inputs remain explicit;
their final source discharge stays with qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original LT preserves S = ⟨Uᴸ⟩. -/
theorem original_outer_span_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    L ⊔ (T : Subgroup G) ≤ normalizer (conjugateSpanBy F.U L : Set G) := by
  exact sup_le (le_normalizer_conjugateSpanBy _ _) (normalizes_conjugateSpanBy _ _ _
    ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
    (h.sylow_normalizes_at structural))

/-- The literal U-image in S/R has order four, since its full kernel is E. -/
theorem extraspecial_outer_plane_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (conjugateSpanBy ⁅F.U,Q T L⁆ L).relIndex F.U = 4 := by
  obtain ⟨c,hs,_,_,hEc,_,_,_,_,_,_,_,_,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hU := (extraspecial_source_reduction h hab structural previous he).2.1
  have hmul := relIndex_mul_card_of_le (hinter.symm.le.trans inf_le_left)
  rw [hEc,hU] at hmul
  rw [←inf_relIndex_left,hinter]
  omega

/-- Construct the literal S/R action, with Q in its kernel and U-image a plane. -/
theorem extraspecial_outer_span_binary_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let S := conjugateSpanBy F.U L
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) S R ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace F.U) = 2 := by
  dsimp only
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let J := L ⊔ (T : Subgroup G)
  obtain ⟨c,hs,_,hE,hcard,hEV,hSQ,hRQ,hRS,hPhi,_,_,_,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hSJ : S ≤ J := (original_span_le_core h hab structural).2.trans (pCoreIn_le 2 _)
  have hRS' : R ≤ S := hRS.trans (map_subtype_le _)
  have hVR : V ≤ R := hRQ.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((pCoreIn_le 2 _).trans (original_commutator_span_normalized h structural).1))
  let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (hSJ.trans (original_commutator_span_normalized h structural).1)
  let : Fact (IsPGroup 2 S) := ⟨(isPGroup_pCoreIn 2 _).to_le
    (original_span_le_core h hab structural).2⟩
  let : IsElementaryAbelian 2 (S ⧸ frattini S) := isElementaryAbelian_quotient_frattini
  have hphi : frattini S ≤ (R.subgroupOf S).comap (MonoidHom.id S) := by
    intro x hx
    exact hVR (hPhi ▸ mem_map_of_mem S.subtype hx)
  let q := QuotientGroup.map (frattini S) (R.subgroupOf S) (MonoidHom.id S) hphi
  let : IsElementaryAbelian 2 (S ⧸ R.subgroupOf S) :=
    IsElementaryAbelian.of_surjective q
      (QuotientGroup.map_surjective_of_surjective (frattini S) (R.subgroupOf S)
        (MonoidHom.id S) (QuotientGroup.mk'_surjective _) hphi)
  obtain ⟨ρ,⟨s⟩⟩ := BinaryConjugationSection.exists_elementary_quotient_coordinates J S R
    hSJ (original_outer_span_normalized h structural) hRS'
    (original_commutator_span_normalized h structural).1
  have hi : R.relIndex F.U = 4 :=
    extraspecial_outer_plane_index h hab structural previous faithful he
  refine ⟨Additive (S ⧸ R.subgroupOf S),inferInstance,inferInstance,ρ,s,?_,
    s.imageSpace_finrank_of_index F.U (le_conjugateSpanBy _ _) 2 hi⟩
  intro a ha
  apply MonoidHom.mem_ker.mpr
  ext w
  obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
  apply (show ρ a w = w ↔ ρ a (s.coordinates r).toAdd = (s.coordinates r).toAdd by rw [hr]; rfl).mpr
  apply (s.fixed_coordinate_iff_commutator_mem a r).mpr
  exact hSQ.le (commutator_mem_commutator r.property ha)

omit [Finite G] in
private theorem ExtraspecialOuterSpan_outerSpan_norm_transfer
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    {τ : Representation (ZMod 2) F.H X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ)
    (s₀ : BinaryConjugationSection F.H F.U (F.Vi 1) τ)
    (hVR : V ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (ha : (a : G) ∈ F.H)
    (hn : ∀ x, x + τ ⟨a,ha⟩ x + τ ⟨a,ha⟩ (τ ⟨a,ha⟩ x) = 0)
    (w : W) (hw : w ∈ s.imageSpace F.U) :
    w + ρ a w + ρ a (ρ a w) = 0 := by
  let R := conjugateSpanBy F.U L
  obtain ⟨r,hr,rfl⟩ := (s.mem_imageSpace_iff _ w).mp hw
  let u : F.U := ⟨r,hr⟩
  let cR (x : R) : R := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s.normalized a.property) x).mp x.property⟩
  let cU (x : F.U) : F.U := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s₀.normalized ha) x).mp x.property⟩
  have hnU : ((u * cU u * cU (cU u) : F.U) : G) ∈ F.Vi 1 := by
    apply (s₀.coordinates_eq_one_iff _).mp
    apply Multiplicative.toAdd.injective
    change (s₀.coordinates _).toAdd = 0
    simp only [map_mul, toAdd_mul]
    rw [show (s₀.coordinates (cU u)).toAdd = τ ⟨a,ha⟩ (s₀.coordinates u).toAdd
      from s₀.equivariant ⟨a,ha⟩ u,
      show (s₀.coordinates (cU (cU u))).toAdd = τ ⟨a,ha⟩ (τ ⟨a,ha⟩ (s₀.coordinates u).toAdd) from
        (s₀.equivariant ⟨a,ha⟩ (cU u)).trans
          (congrArg (τ ⟨a,ha⟩) (s₀.equivariant ⟨a,ha⟩ u))]
    exact hn _
  have hnR : s.coordinates (r * cR r * cR (cR r)) = 1 :=
    (s.coordinates_eq_one_iff _).mpr (hVR (F.le_seed 1 hnU))
  have hh := congrArg Multiplicative.toAdd hnR
  simp only [map_mul, toAdd_mul] at hh
  rw [show (s.coordinates (cR r)).toAdd = ρ a (s.coordinates r).toAdd from s.equivariant a r,
    show (s.coordinates (cR (cR r))).toAdd = ρ a (ρ a (s.coordinates r).toAdd) from
      (s.equivariant a (cR r)).trans (congrArg (ρ a) (s.equivariant a r))] at hh
  exact hh

/-- The point cubic has zero norm on the original U/E plane in S/R. -/
theorem extraspecial_outer_plane_cubic_norm
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    ∃ a : (L ⊔ (T : Subgroup G) : Subgroup G), (a : G) ∈ F.Li L 1 ∧
      ∀ w ∈ s.imageSpace F.U, w + ρ a w + ρ a (ρ a w) = 0 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨e⟩ := he
  have he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) := ⟨e⟩
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hnormal := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨τ,⟨s₀⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := exists_star_representation h s₀
  obtain ⟨z,hz,hzp,hfix⟩ := exists_fixedFree_cubic_of_point_normal h structural hnormal s₀ σ hσ
  have hzm : z ∈ star F (F.Li L 1) := hzp ▸ mem_zpowers z
  obtain ⟨a,ha,haz⟩ := hzm
  let aJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 ha).1⟩
  have heq : τ a = σ z := by
    rw [←haz,←hσ]
    rfl
  have hz3 (x) : σ z (σ z (σ z x)) = x := by
    calc _ = σ (z ^ 3) x := by simp [pow_succ,map_mul,Module.End.mul_apply]
         _ = x := by rw [show z ^ 3 = 1 from orderOf_dvd_iff_pow_eq_one.mp (by rw [hz]),map_one]; rfl
  refine ⟨aJ,ha,?_⟩
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  have hVE : V ≤ ⁅F.U,Q T L⁆ := by
    obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hnormal
    exact (extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs).symm.le.trans
      (commutator_mono le_rfl (critical_le_Q_at h structural c))
  apply ExtraspecialOuterSpan_outerSpan_norm_transfer s s₀ (hVE.trans (le_conjugateSpanBy _ _)) aJ a.property
  intro x
  change x + τ a x + τ a (τ a x) = 0
  rw [heq]
  apply hfix
  simp only [map_add,hz3]
  abel
private theorem ExtraspecialOuterSpan_outerSpan_binary_neg {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (w : W) : -w = w := by
  simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) w).symm

/-- The original point residual acts irreducibly on U/E. The norm relation
supplies full movement, so a binary line quotient would be impossible. -/
theorem extraspecial_outer_plane_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    ∃ D : Subrepresentation (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
      D.toSubmodule = s.imageSpace F.U ∧ IsIrreducible D.toRepresentation := by
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace F.U
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem _ (j a)
      ((le_normalizer_conjugateSpanBy V F.H) (F.Li_le L 1 a.property).2) w hw }
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hi := extraspecial_outer_plane_index h hab structural previous faithful he
  have hd : Module.finrank (ZMod 2) D.toSubmodule = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨a,ha,hn⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful he s
  let b : F.Li L 1 := ⟨a,ha⟩
  have hnorm (w : D.toSubmodule) :
      w + D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w) = 0 := by
    apply Subtype.ext
    exact hn w w.property
  have hm : Representation.BinaryOffender.subspaceCommutator D.toRepresentation ⊤ ⊤ = ⊤ := by
    apply top_unique
    intro w _
    have hmove : D.toRepresentation b (D.toRepresentation b w) - D.toRepresentation b w = w := by
      calc _ = -(D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w)) := by
             simp only [sub_eq_add_neg,ExtraspecialOuterSpan_outerSpan_binary_neg]
             exact add_comm _ _
           _ = w := (eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hnorm w)).symm
    exact Submodule.subset_span ⟨b,mem_top b,D.toRepresentation b w,Submodule.mem_top,hmove.symm⟩
  exact ⟨D,rfl,Representation.BinaryOffender.irreducible_of_rank_two_full_movement _ hd hm⟩

omit [Finite G] in
/-- The conjugates of the literal U/E plane generate the entire S/R section. -/
theorem extraspecial_outer_plane_generates
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ)
    (A : Submodule (ZMod 2) W) (hA : s.imageSpace F.U ≤ A)
    (hstable : ∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) : A = ⊤ := by
  let R := conjugateSpanBy F.U L
  let B : Subgroup R := A.toAddSubgroup.toSubgroup.comap s.coordinates
  have hRB : R ≤ B.map R.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨l,hl,e,he,rfl⟩
    let eR : R := ⟨e,le_conjugateSpanBy _ _ he⟩
    let lJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨l,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩
    refine ⟨⟨l*e*l⁻¹,(mem_normalizer_iff.mp (s.normalized lJ.property) e).mp eR.property⟩,?_,rfl⟩
    change (s.coordinates _).toAdd ∈ A
    rw [s.equivariant lJ eR]
    exact hstable ⟨l,hl⟩ _ (hA ((s.mem_imageSpace_iff _ _).mpr ⟨eR,he,rfl⟩))
  apply top_unique
  intro w _
  obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
  obtain ⟨b,hb,hbr⟩ := hRB r.property
  have hbr' : b = r := Subtype.ext hbr
  subst b
  change (s.coordinates r).toAdd ∈ A at hb
  simpa only [hr,toAdd_ofAdd] using hb

open BinaryLinearThree.ParabolicCyclic in
/-- The original section has a Sylow-fixed cyclic seed whose point-parabolic
orbit spans exactly U/E. This supplies the geometric hypotheses of H.6.5
before choosing a matrix marking. -/
theorem extraspecial_outer_cyclic_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
    ∃ w ∈ s.imageSpace F.U, w ≠ 0 ∧
      (∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w) ∧
      orbitSpan τ ⊤ w = ⊤ ∧
      orbitSpan τ (F.H.subgroupOf L) w = s.imageSpace F.U ∧
      Module.finrank (ZMod 2) (orbitSpan τ (F.H.subgroupOf L) w) = 2 := by
  dsimp only
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  let D := s.imageSpace F.U
  let S := (T : Subgroup G).subgroupOf L
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have stable (l : L) (hl : (l : G) ∈ F.H) (w : W) (hw : w ∈ D) : τ l w ∈ D :=
    s.imageSpace_apply_mem _ (inclusion le_sup_left l)
      ((le_normalizer_conjugateSpanBy V F.H) hl) w hw
  let : MulAction S D := {
    smul t w := ⟨τ t w,stable t (F.invariant 1 t.property) w w.property⟩
    one_smul w := by apply Subtype.ext; exact congrArg (fun f => f w.val) τ.map_one
    mul_smul t r w := by apply Subtype.ext; exact congrArg (fun f => f w.val) (τ.map_mul t r) }
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hi := extraspecial_outer_plane_index h hab structural previous faithful he
  have hcard : Nat.card D = 4 := (s.imageSpace_card_eq_relIndex _ (le_conjugateSpanBy _ _)).trans hi
  have hd : Module.finrank (ZMod 2) D = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨w,hw,hw0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := D) (by rw [hcard]; decide)
    (show (0 : D) ∈ MulAction.fixedPoints S D from fun a => Subtype.ext (map_zero (τ a)))
  have hn : (w : W) ≠ 0 := fun hh => hw0 (Subtype.ext hh.symm)
  have hfix : ∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w :=
    fun t ht => congrArg Subtype.val (hw ⟨t,ht⟩)
  let A := orbitSpan τ (F.H.subgroupOf L) w
  have hAD : A ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l,hl,rfl⟩
    exact stable l hl w w.property
  obtain ⟨I,hI,hirr⟩ := extraspecial_outer_plane_irreducible h hab structural previous faithful he s
  let : IsIrreducible I.toRepresentation := hirr
  have hstable (a : F.Li L 1) (v : W) (hv : v ∈ A) :
      ρ (inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) a) v ∈ A :=
    orbitSpan_stable τ (F.H.subgroupOf L) w
      ⟨a,(F.Li_le L 1 a.property).1⟩ (F.Li_le L 1 a.property).2 v hv
  let B : Subrepresentation I.toRepresentation := {
    toSubmodule := A.comap I.toSubmodule.subtype
    apply_mem_toSubmodule a v hv := hstable a v hv }
  have hB : B = ⊤ := (eq_bot_or_eq_top B).resolve_left (by
    intro hb
    have hm : (⟨w,hI ▸ w.property⟩ : I.toSubmodule) ∈ B := mem_orbitSpan τ _ w
    rw [hb] at hm
    exact hn (congrArg Subtype.val hm))
  have hDA : D ≤ A := by
    intro v hv
    have hm : (⟨v,hI ▸ hv⟩ : I.toSubmodule) ∈ B := hB ▸ Submodule.mem_top
    exact hm
  have hplane : A = D := le_antisymm hAD hDA
  have hfull : orbitSpan τ ⊤ w = ⊤ := by
    apply extraspecial_outer_plane_generates s
    · apply hDA.trans
      apply Submodule.span_mono
      rintro v ⟨a,_,ha⟩
      exact ⟨a,mem_top a,ha⟩
    · intro l v hv
      exact orbitSpan_stable τ ⊤ w l (mem_top l) v hv
  exact ⟨w,w.property,hn,hfix,hfull,hplane,by change Module.finrank (ZMod 2) A = 2; rw [hplane]; exact hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The five marked module possibilities for the original S/R

Descend the original LT-action through the actual L/O₂(L) map. The
Sylow-fixed cyclic vector and its point-parabolic plane satisfy the proved
H.6.5 recognition theorem. Thus S/R has one of the five actual module
structures, with the original quotient, parabolic and dual orientation
retained. Their exact L₁-chief counts are one through five.

This is the five-model reduction used in Aschbacher–Smith 14.7.24(1),
printed p.1051, refs/quasithin.pdf. Selecting the Core alternative still
requires the central branch's two-factor count. The earlier source inputs
retain their existing producers and final discharge at qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialOuterRecognition_outerRecognition_descent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
    (hk : (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker) :
    ∃ σ : Representation (ZMod 2) BinaryLinearThree.Group W,
      σ.comp (SpanMarking.qL h) = ρ.comp (inclusion le_sup_left) := by
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  have hcore : L.pCoreIn 2 ≤ Q T L :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  have hkill : (SpanMarking.qL h).ker ≤ τ.ker := by
    rw [SpanMarking.qL_ker]
    intro l hl
    exact hk (hcore hl)
  have hkillU : (SpanMarking.qL h).ker ≤ τ.asGroupHom.ker := by
    intro l hl
    apply Units.ext
    exact hkill hl
  let β := (SpanMarking.qL h).liftOfSurjective (SpanMarking.qL_surjective h) ⟨τ.asGroupHom,hkillU⟩
  let σ : Representation (ZMod 2) BinaryLinearThree.Group W := (Units.coeHom _).comp β
  refine ⟨σ,?_⟩
  apply MonoidHom.ext
  intro l
  exact congrArg Units.val ((SpanMarking.qL h).liftOfRightInverse_comp_apply
    (Function.surjInv (SpanMarking.qL_surjective h))
    (Function.rightInverse_surjInv (SpanMarking.qL_surjective h)) ⟨τ.asGroupHom,hkillU⟩ l)

private theorem ExtraspecialOuterRecognition_outerRecognition_orbit_map
    {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W) (q : A →* B) (P : Subgroup A) (w : W) :
    BinaryLinearThree.ParabolicCyclic.orbitSpan σ (P.map q) w =
      BinaryLinearThree.ParabolicCyclic.orbitSpan (σ.comp q) P w := by
  unfold BinaryLinearThree.ParabolicCyclic.orbitSpan
  congr 1
  ext v
  constructor
  · rintro ⟨b,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨q a,mem_map_of_mem q ha,he⟩


open BinaryLinearThree.ParabolicCyclic in
/-- The original S/R has one of the five actual H.6.5 module structures.
The quotient map, parabolic orientation, natural-to-dual equivalence and
literal conjugation section are retained in the same witness. -/
theorem extraspecial_outer_module_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let S := conjugateSpanBy F.U L
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) S R ρ)
      (e : MulAut BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group W),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      σ.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)) = ρ.comp (inclusion le_sup_left) ∧
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) ∧
      Alternatives σ ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ BinaryLinearThree.ParabolicCyclic.ChiefCounts.HasCount
        (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) n := by
  obtain ⟨W,ha,hm,ρ,s,hker,_⟩ :=
    extraspecial_outer_span_binary_section h hab structural previous faithful he
  obtain ⟨τ,hτ⟩ := ExtraspecialOuterRecognition_outerRecognition_descent h structural ρ hker
  obtain ⟨e,hS,hP,hdual⟩ := SpanMarking.exists_marking h F (h.sylow_normalizes_at structural)
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let σ := τ.comp e.toMonoidHom
  have hσ : σ.comp q = ρ.comp (inclusion le_sup_left) := by
    calc _ = τ.comp (SpanMarking.qL h) := by
           ext l w
           change τ (e (e.symm (SpanMarking.qL h l))) w = _
           rw [e.apply_symm_apply]
           rfl
         _ = _ := hτ
  have hq : Function.Surjective q := e.symm.surjective.comp (SpanMarking.qL_surjective h)
  obtain ⟨w,_,_,hfix,hgen,hplane,hd⟩ :=
    extraspecial_outer_cyclic_seed h hab structural previous faithful he s
  have hfixed : ∀ a ∈ Matrix.PSL3Two.borelSL, σ a w = w := by
    intro a ha
    rw [←hS] at ha
    obtain ⟨l,hl,rfl⟩ := ha
    have hh := congrArg (fun ψ : Representation (ZMod 2) L W => ψ l w) hσ
    exact hh.trans (hfix l hl)
  have hfull : orbitSpan σ ⊤ w = ⊤ := by
    rw [←map_top_of_surjective q hq,ExtraspecialOuterRecognition_outerRecognition_orbit_map,hσ]
    exact hgen
  have hdim : Module.finrank (ZMod 2) (orbitSpan σ Matrix.PSL3Two.lineParabolicSL w) = 2 := by
    rw [←hP,ExtraspecialOuterRecognition_outerRecognition_orbit_map,hσ]
    exact hd
  have hclass := parabolic_seed_alternatives σ w hfixed hfull hdim
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,?_⟩
  rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
  · exact ⟨1,by omega,by omega,hh.2⟩
  · exact ⟨2,by omega,by omega,hh.2⟩
  · exact ⟨3,by omega,by omega,hh.2⟩
  · exact ⟨4,by omega,by omega,hh.2⟩
  · exact ⟨5,by omega,by omega,hh.2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Core recognition in the original central branch

Under [C_H(U),K] ≤ U, compare S/R with P/C_P(U). Their relative
intersection R ∩ P lies in C_P(U); R itself need not lie in P. The
comparison therefore retains precisely this relative kernel. It gives
one noncentral chief plane above the image of C_P(U). The original U/E
is another such plane. The two remaining gaps are central for L₁.

Refining these gaps proves an exact count of two noncentral factors.
The five marked H.6.5 possibilities have distinct counts, so S/R is
actually equivariantly isomorphic to the six-dimensional permutation core,
with the original quotient map and dual parabolic marking retained.

Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
All local recognition premises are proved here; the genuine earlier source
inputs retain their producers and final discharge at qt-d-14775-source.
The central-subgroup deduction is in ExtraspecialCentralCompletion.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Point normality places the original [S,L₁] inside P = O₂(K). -/
theorem extraspecial_outer_commutator_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅conjugateSpanBy F.U L,F.Li L 1⁆ ≤ (K F).pCoreIn 2 := by
  have hn := (extraspecial_source_reduction h hab structural previous he).1
  have hHnA := (normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn
  have hSQ := (original_span_le_core h hab structural).2
  have hAL := (F.Li_le L 1).trans inf_le_left
  have hAQ : F.Li L 1 ≤ normalizer (Q T L : Set G) :=
    (hAL.trans le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hc : ⁅conjugateSpanBy F.U L,F.Li L 1⁆ ≤ F.Li L 1 ⊓ Q T L := le_inf
    (le_normalizer_iff_commutator_le_right.mp ((hSQ.trans (Q_le_H F)).trans hHnA))
    ((commutator_mono hSQ le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hAQ))
  exact (hc.trans (inf_pCoreIn_le_of_le 2 (hAL.trans le_sup_left))).trans_eq
    (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1

private theorem ExtraspecialOuterCore_outerCount_irreducible_plane
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) A X) (hd : Module.finrank (ZMod 2) X = 2)
    (hf : ∀ x, (∀ a, τ a x = x) → x = 0) : τ.IsIrreducible := by
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) X)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun N => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  by_cases ht : N = ⊤
  · exact Or.inr ht
  exfalso
  have hNb : N.toSubmodule ≠ ⊥ := fun hh => hb (Subrepresentation.toSubmodule_injective hh)
  have hNt : N.toSubmodule ≠ ⊤ := fun hh => ht (Subrepresentation.toSubmodule_injective hh)
  have hpos : 0 < Module.finrank (ZMod 2) N.toSubmodule :=
    Nat.pos_of_ne_zero (fun hh => hNb (Submodule.finrank_eq_zero.mp hh))
  have hlt := Submodule.finrank_lt hNt
  have hdim : Module.finrank (ZMod 2) N.toSubmodule = 1 := by omega
  apply hNb
  apply bot_unique
  intro x hx
  exact hf x (fun a => by
    have hh := BinaryParabolicNatural.linear_one_trivial hdim
      (LinearMap.GeneralLinearGroup.toLinearEquiv (N.toRepresentation.asGroupHom a))
    exact congrArg (fun f : N.toSubmodule ≃ₗ[ZMod 2] N.toSubmodule => (f ⟨x,hx⟩ : X)) hh)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The central case has exactly two noncentral L₁-chief factors on the
literal S/R, using both original quotient maps. -/
theorem extraspecial_outer_count_two_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) τ) :
    HasCount (τ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  let : Finite X := Finite.of_surjective (fun x => (s.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let P := (K F).pCoreIn 2
  let PC := P ⊓ centralizer (F.U : Set G)
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hnP : F.H ≤ normalizer (P : Set G) :=
    (H_normalizes_K F).trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (K F)))
  have hnPC : F.H ≤ normalizer (PC : Set G) :=
    (le_inf hnP ((le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let I (B : Subgroup G) (hnB : F.H ≤ normalizer (B : Set G)) : Subrepresentation (τ.comp j) := {
    toSubmodule := s.imageSpace B
    apply_mem_toSubmodule a x hx := s.imageSpace_apply_mem _ (j a)
      (hnB (F.Li_le L 1 a.property).2) x hx }
  let N := I PC hnPC
  let B := I P hnP
  obtain ⟨D,hD,hirr⟩ := extraspecial_outer_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hUPC : F.U ≤ PC := le_inf (span_le_residual_core h hab)
    (le_centralizer_iff_isMulCommutative.mpr hab)
  have hDN : D ≤ N := by
    change D.toSubmodule ≤ s.imageSpace PC
    rw [hD]
    exact s.imageSpace_mono hUPC
  have hNB : N ≤ B := s.imageSpace_mono inf_le_left
  have hcentral₀ : Central D N := by
    have hcomm : ⁅F.Li L 1,S ⊓ PC⁆ ≤ F.U := by
      rw [commutator_comm]
      exact (commutator_mono (inf_le_right.trans inf_le_right) (pointResidual_le F)).trans hc
    intro a x hx
    change τ (j a) x-x ∈ D.toSubmodule
    rw [hD]
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) inf_le_left]
    apply Submodule.subset_span
    refine ⟨j a,a.property,x,?_,rfl⟩
    obtain ⟨r,hr,heq⟩ := (s.mem_imageSpace_iff _ x).mp hx
    exact (s.mem_imageSpace_iff _ x).mpr ⟨r,⟨r.property,hr⟩,heq⟩
  have hcentral₁ : Central B ⊤ := by
    have hcomm : ⁅F.Li L 1,S⁆ ≤ P := by
      rw [commutator_comm]
      exact extraspecial_outer_commutator_core h hab structural previous faithful he
    intro a x _
    change τ (j a) x-x ∈ s.imageSpace P
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,x,Submodule.mem_top,rfl⟩
  have hnoncentral : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful he s
    apply hatom.ne_bot
    apply bot_unique
    intro x hx
    have hfix : τ a x=x := sub_eq_zero.mp (htriv ⟨a,ha⟩ x hx)
    have hh := hn x (hD ▸ hx)
    rw [hfix,hfix] at hh
    have hxx : x+x=0 := by
      calc x+x = (2 : ZMod 2) • x := (two_smul (ZMod 2) x).symm
           _ = 0 := by simp
    change x = 0
    simpa only [hxx,zero_add] using hh
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨Y,ha,hm,ρ,sU,sP,_,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  let : Finite Y := Finite.of_surjective (fun u => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let k : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let J : Subrepresentation (ρ.dual.comp k) := {
    toSubmodule := sP.imageSpace S
    apply_mem_toSubmodule a y hy := sP.imageSpace_apply_mem S (k a)
      ((original_outer_span_normalized h structural)
        ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 a.property).1)) y hy }
  obtain ⟨_,hd,hfree⟩ := extraspecial_core_outer_fixed_plane h hab structural previous faithful ⟨e⟩ sU sP
  let : J.toRepresentation.IsIrreducible := ExtraspecialOuterCore_outerCount_irreducible_plane _ hd (by
    intro w hw
    apply Subtype.ext
    exact hfree w (fun a => congrArg Subtype.val (hw a)))
  have hJmove : ¬ ∀ a y, J.toRepresentation a y = y := by
    intro htriv
    have hz : J.toSubmodule = ⊥ := by
      apply bot_unique
      intro y hy
      exact hfree y (fun a => congrArg Subtype.val (htriv a ⟨y,hy⟩))
    change Module.finrank (ZMod 2) J.toSubmodule = 2 at hd
    rw [hz,finrank_bot] at hd
    contradiction
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful ⟨e⟩
  have hRP : R ⊓ P ≤ PC := le_inf inf_le_right ((inf_le_left.trans hRC).trans inf_le_right)
  obtain ⟨f,hf,hk⟩ := BinaryConjugationSection.exists_relative_intersection_intertwiner
    (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
    ((F.Li_le L 1).trans inf_le_right) s sP inf_le_left hRP
    N B J rfl rfl rfl
  obtain ⟨hcover,hnc⟩ := BinaryConjugationSection.chief_interval_of_surjective_intertwiner
    (X := X) (Y := J.toSubmodule) (τ := τ.comp j) (ν := J.toRepresentation) N B hNB f hf hk hJmove
  have h01 := exists_series_count_join
    (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hnoncentral)
    (exists_central_series D N hDN hcentral₀)
  have h012 := exists_series_count_join h01 (exists_noncentral_chief_series N B hcover hnc)
  simpa only [HasCount,Nat.add_zero,Nat.reduceAdd] using exists_series_count_join h012
    (exists_central_series B ⊤ le_top hcentral₁)
open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Source 14.7.24(1): the actual outer quotient is the marked permutation core. -/
theorem extraspecial_outer_core_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
 :
    let S := conjugateSpanBy F.U L
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) S R ρ)
      (e : MulAut BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group W),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      σ.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)) = ρ.comp (inclusion le_sup_left) ∧
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) ∧
      Nonempty (σ.Equiv BinaryLinearThree.U₂) ∧
      Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
        (BinaryLinearThree.U₂.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)))) ∧
      HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
        (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,_⟩ :=
    extraspecial_outer_module_alternatives h hab structural previous faithful he
  have hcount := extraspecial_outer_count_two_of_central h hab structural previous faithful he hc s
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  have hcore : Nonempty (σ.Equiv BinaryLinearThree.U₂) := by
    rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
    · have := hcount.unique hh.2; omega
    · exact hh.1
    all_goals have := hcount.unique hh.2; omega
  obtain ⟨ec⟩ := hcore
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,⟨ec⟩,?_,hcount⟩
  rw [←hσ]
  exact ⟨restrictEquiv ec q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original central seed from the outer Core module

A nonzero fixed displacement in the marked Core lifts to [S,L₁] ≤ P.
Its coordinates in P/C_P(U) are L₁-fixed, so dual fixed-point vanishing
puts the lift in C_P(U). The cubic norm on U/E shows that it lies outside U.

The fixed-space preimage in S/R, intersected with C_P(U), therefore gives
an actual C ≤ P outside U with [C,L₁] ≤ R and [C,K] ≤ U. All quotient
maps are those of the original flag. ExtraspecialCentralCompletion applies
this seed to obtain the central subgroup without a recognition callback.

Source: Aschbacher–Smith 14.7.24(2), printed p.1051, refs/quasithin.pdf.
The genuine earlier implications retain their producers; their final
source discharge stays with qt-d-14775-source.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialOuterCentralSeed_outerSeed_point_image
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL) :
    ((F.Li L 1).subgroupOf L).map q = actor := by
  have he : (F.Li L 1).subgroupOf L =
      (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
      map_embedded_pResidual,subgroupOf_map_subtype]
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,↓reduceIte]
    change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
    rw [inf_comm]
  rw [he,map_embedded_pResidual,hP]
  rfl

/-- The central branch supplies an actual subgroup outside U in C_P(U),
with the two commutator bounds used in the source central-subgroup argument. -/
theorem extraspecial_outer_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ C : Subgroup G, C ≤ (K F).pCoreIn 2 ∧ ¬ C ≤ F.U ∧
      C ≤ conjugateSpanBy F.U L ∧
      ⁅C,F.Li L 1⁆ ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L ∧ ⁅C,K F⁆ ≤ F.U := by
  obtain ⟨X,ha,hm,τ,s,e,σ,_,hσ,_,hP,_,⟨ec⟩,_,_⟩ :=
    extraspecial_outer_core_of_central h hab structural previous faithful he hc
  let R := conjugateSpanBy F.U L
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hmap := ExtraspecialOuterCentralSeed_outerSeed_point_image q hP
  have hq (a : F.Li L 1) : q ⟨a,(F.Li_le L 1 a.property).1⟩ ∈ actor := by
    rw [←hmap]
    exact ⟨⟨a,(F.Li_le L 1 a.property).1⟩,a.property,rfl⟩
  have hact (a : F.Li L 1) (v : X) :
      ec (τ (j a) v) = BinaryLinearThree.U₂ (q ⟨a,(F.Li_le L 1 a.property).1⟩) (ec v) := by
    have hh := congrArg (fun ψ : Representation (ZMod 2) L X =>
      ψ ⟨a,(F.Li_le L 1 a.property).1⟩ v) hσ
    change σ (q ⟨a,(F.Li_le L 1 a.property).1⟩) v = τ (j a) v at hh
    exact (congrArg ec hh.symm).trans (IntertwiningMap.isIntertwining _ _ ec.toIntertwiningMap _ _)
  obtain ⟨v,w,a,hv,hfix,hdisp⟩ := BinaryLinearThree.core_exists_fixed_displacement
  let v' := ec.symm v
  let w' := ec.symm w
  have hv' : v' ≠ 0 := by
    intro hh
    apply hv
    have := congrArg ec hh
    simpa only [v',ec.apply_symm_apply,map_zero] using this
  have hfixed (b : F.Li L 1) : τ (j b) v' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j b) v') = ec v'
    rw [hact,ec.apply_symm_apply,hfix ⟨_,hq b⟩]
  have ham : (a : BinaryLinearThree.Group) ∈ ((F.Li L 1).subgroupOf L).map q := by
    rw [hmap]
    exact a.property
  obtain ⟨aL,haL,haq⟩ := ham
  let a₁ : F.Li L 1 := ⟨aL,haL⟩
  have hdisplacement : τ (j a₁) w' - w' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j a₁) w' - w') = ec v'
    rw [map_sub,hact,ec.apply_symm_apply,ec.apply_symm_apply]
    change BinaryLinearThree.U₂ (q aL) w - w = v
    rw [haq]
    exact hdisp
  have hvcomm : v' ∈ s.imageSpace ⁅F.Li L 1,R⁆ := by
    rw [s.imageSpace_commutator (F.Li L 1) R
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a₁,a₁.property,w',Submodule.mem_top,hdisplacement.symm⟩
  obtain ⟨x,hxcomm,hxcoord⟩ := (s.mem_imageSpace_iff ⁅F.Li L 1,R⁆ v').mp hvcomm
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hxP : (x : G) ∈ (K F).pCoreIn 2 := by
    apply extraspecial_outer_commutator_core h hab structural previous faithful he
    rwa [commutator_comm]
  obtain ⟨ee⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv ee.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr ee.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv ee).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  let P := (K F).pCoreIn 2
  let PC := P ⊓ centralizer (F.U : Set G)
  obtain ⟨Y,haY,hmY,ρU,sU,t,_,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  obtain ⟨_,_,hfree⟩ := extraspecial_core_outer_fixed_plane h hab structural previous faithful ⟨ee⟩ sU t
  have hxPC : (x : G) ∈ PC := by
    apply (t.coordinates_eq_one_iff ⟨x,hxP⟩).mp
    apply hfree
    intro b
    apply (t.fixed_coordinate_iff_commutator_mem
      (inclusion ((F.Li_le L 1).trans inf_le_right) b) ⟨x,hxP⟩).mpr
    have hxR : ⁅(x : G),(b : G)⁆ ∈ conjugateSpanBy ⁅F.U,Q T L⁆ L := by
      apply (s.fixed_coordinate_iff_commutator_mem (j b) x).mp
      rw [hxcoord]
      exact hfixed b
    refine ⟨?_,(hRC hxR).2⟩
    exact (le_normalizer_iff_commutator_le_left.mp
      (((F.Li_le L 1).trans inf_le_right).trans t.normalized))
      (commutator_mem_commutator hxP b.property)
  have hxU : (x : G) ∉ F.U := by
    intro hx
    obtain ⟨b,hb,hnorm⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful ⟨ee⟩ s
    have him : v' ∈ s.imageSpace F.U :=
      (s.mem_imageSpace_iff _ _).mpr ⟨x,hx,hxcoord⟩
    have hbfix : τ b v' = v' := hfixed ⟨b,hb⟩
    have hh := hnorm v' him
    rw [hbfix,hbfix] at hh
    have htwo : v'+v'=0 := by
      calc v'+v' = (2 : ZMod 2) • v' := (two_smul (ZMod 2) v').symm
           _ = 0 := by simp
    exact hv' (by simpa only [htwo,zero_add] using hh)
  let I := fixedSpace τ ((F.Li L 1).subgroupOf (L ⊔ (T : Subgroup G)))
  let C := s.subspacePreimage I ⊓ PC
  have hxC : (x : G) ∈ C := by
    refine ⟨(s.mem_subspacePreimage I x).mpr ⟨x.property,?_⟩,hxPC⟩
    intro b
    rw [hxcoord]
    exact hfixed ⟨b.val,b.property⟩
  refine ⟨C,inf_le_right.trans inf_le_left,(fun hh => hxU (hh hxC)),
    inf_le_left.trans (s.subspacePreimage_le I),?_,?_⟩
  · rw [commutator_comm]
    apply s.commutator_le_of_imageSpace_fixed (F.Li L 1) C
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
      (inf_le_left.trans (s.subspacePreimage_le I))
    exact (s.imageSpace_mono inf_le_left).trans (s.imageSpace_subspacePreimage I).le
  · exact (commutator_mono (inf_le_right.trans inf_le_right) le_rfl).trans hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Completing the original central-subgroup argument

For the central branch, adjoining U to the constructed seed C gives a
K-invariant subgroup CU of P = O₂(K). Its commutator with P lies in
U ∩ R = E. Since E is proper in U and K is irreducible on U/V₁, that
commutator lies in V₁. Cubic fixed-point lifting then constructs an
element of Z(P) outside U. The existing faithful-branch proof covers the
other case, and the proved center control gives V₁ < Z(P) ≤ Z(K).

An invariant index-two step in Z(P) gives an actual subgroup of order four
containing V₁, central in K and normal in H = KT. The original group,
quotient conventions and every genuine earlier-source premise are retained.

This completes Aschbacher–Smith 14.7.24(2), 14.7.25 and the following
choice of D, printed pp.1051–1052, refs/quasithin.pdf. Maximal-normalizer
control in 14.7.21(1) and the remaining reductions through 14.7.52 are
not asserted. Final earlier-source discharge remains at qt-d-14775-source.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialCentralCompletion_outerCenter_residual_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    IsIrreducible (ρ.comp (inclusion (K_le_H F))) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,_,_,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let q := (residualStarEquiv F).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F)))
  have hq : Function.Surjective q := (residualStarEquiv F).surjective.comp (QuotientGroup.mk'_surjective _)
  have heq : (σ.comp (pResidual 2 (HStar F.H)).subtype).comp q =
      ρ.comp (inclusion (K_le_H F)) := by
    ext k w
    change σ (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k)) w = _
    rw [residualStarEquiv_mk]
    exact congrArg (fun τ : Representation (ZMod 2) F.H W => τ (inclusion (K_le_H F) k) w) hσ
  exact heq ▸ (irreducible_comp_surjective_iff q hq _).mpr hi

omit [Finite G] in
private theorem ExtraspecialCentralCompletion_outerCenter_normalizes_commutator (A B C : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hAC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer ((⁅B,C⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hAB ha),mem_normalizer_iff_map_conj_eq.mp (hAC ha)]

/-- A central-branch seed gives strict enlargement in the residual-core
center, using the proper subgroup E = U ∩ R. -/
theorem extraspecial_core_center_strict_of_outer_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (C : Subgroup G) (hCP : C ≤ (K F).pCoreIn 2) (hCU : ¬ C ≤ F.U)
    (hCA : ⁅C,F.Li L 1⁆ ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L) (hCK : ⁅C,K F⁆ ≤ F.U) :
    F.Vi 1 < (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype := by
  let P := (K F).pCoreIn 2
  let A := F.Li L 1
  let D := C ⊔ F.U
  have hUP : F.U ≤ P := span_le_residual_core h hab
  have hDP : D ≤ P := sup_le hCP hUP
  have hPH : P ≤ F.H := (pCoreIn_le 2 _).trans (K_le_H F)
  have hcore : A.pCoreIn 2 = P :=
    (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  have hPA : P ≤ A := hcore ▸ pCoreIn_le 2 A
  have hAK : A ≤ K F := pointResidual_le F
  have hAH : A ≤ F.H := hAK.trans (K_le_H F)
  have hHnU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hPnU : P ≤ normalizer (F.U : Set G) := hPH.trans hHnU
  have hDK : ⁅D,K F⁆ ≤ F.U := by
    have hn := commutator_commutatorPreimage_le P (K F) F.U hPnU
    have hD : D ≤ commutatorPreimage P (K F) F.U := sup_le
      (le_commutatorPreimage hCP hCK)
      (le_commutatorPreimage hUP (le_normalizer_iff_commutator_le_left.mp ((K_le_H F).trans hHnU)))
    exact (commutator_mono hD le_rfl).trans hn
  have hKnD : K F ≤ normalizer (D : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hDK.trans le_sup_right)
  have hKnP : K F ≤ normalizer (P : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))
  let E := ⁅F.U,Q T L⁆
  obtain ⟨c,hs,_,_,hEc,_,_,_,_,_,_,_,_,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hVE : V ≤ E :=
    (extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs).symm.le.trans
      (commutator_mono le_rfl (critical_le_Q_at h structural c))
  have hPnE : P ≤ normalizer (E : Set G) :=
    (hPA.trans (F.Li_le L 1)).trans (original_commutator_span_normalized h structural).2
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUPcomm : ⁅F.U,P⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro p hp u hu
    apply (s.action_mem_ker_iff ⟨p,hPH hp⟩).mp _ u hu
    apply core_le_action_kernel h s
    have hcoreP : P ≤ F.H.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
    have hrelative : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
      comap_map_eq_self_of_injective F.H.subtype_injective _
    rw [←hrelative]
    exact hcoreP hp
  have hCE : ⁅C,P⁆ ≤ E := by
    change ⁅C,P⁆ ≤ ⁅F.U,Q T L⁆
    rw [←hinter]
    exact le_inf ((commutator_mono le_rfl (pCoreIn_le 2 (K F))).trans hCK)
      ((commutator_mono le_rfl hPA).trans hCA)
  have hPE : ⁅D,P⁆ ≤ E := by
    have hD : D ≤ commutatorPreimage P P E := sup_le
      (le_commutatorPreimage hCP hCE)
      (le_commutatorPreimage hUP (hUPcomm.trans ((F.le_seed 1).trans hVE)))
    exact (commutator_mono hD le_rfl).trans (commutator_commutatorPreimage_le P P E hPnE)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) := by
    apply le_centralizer_iff.mp
    exact (K_le_H F).trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))
  let M := ⁅D,P⁆ ⊔ F.Vi 1
  have hME : M ≤ E := sup_le hPE ((F.le_seed 1).trans hVE)
  have hKnM : K F ≤ normalizer (M : Set G) :=
    (le_inf (ExtraspecialCentralCompletion_outerCenter_normalizes_commutator (K F) D P hKnD hKnP)
      ((le_centralizer_iff.mp hpoint).trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : IsIrreducible (ρ.comp (inclusion (K_le_H F))) :=
    ExtraspecialCentralCompletion_outerCenter_residual_irreducible h hab structural previous he s
  let t := s.restrictActor (K_le_H F) (hUP.trans (pCoreIn_le 2 _))
  have hUnM : ¬ F.U ≤ M := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion (hh.trans hME)) (inclusion_injective _)
    rw [(extraspecial_source_reduction h hab structural previous he).2.1,hEc] at hc
    omega
  have hPM : ⁅D,P⁆ ≤ F.Vi 1 := by
    rw [←t.inf_eq_kernel_of_irreducible M hKnM le_sup_right hUnM]
    exact le_inf (hPE.trans (hinter.symm.le.trans inf_le_left)) le_sup_left
  have hAp : IsPPerfect 2 A := by
    change IsPPerfect 2 (F.Li L 1)
    simp only [InvariantFlag.Li]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)
  have hfix : ¬ D ⊓ centralizer (A : Set G) ≤ F.U := by
    apply cubic_central_layer_lift A D F.U (F.Vi 1) hAp
      (pointResidual_core_quotient_card h structural)
      (hcore.symm ▸ hDP) le_sup_right (fun hh => hCU (le_sup_left.trans hh))
      (hAK.trans hKnD) (hAH.trans hHnU)
      (hpoint.trans (centralizer_le hAK))
      ((commutator_mono le_rfl hAK).trans hDK)
    rwa [hcore]
  have hcent : D ⊓ centralizer (A : Set G) ≤ (center P).map P.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf (inf_le_left.trans hDP) (inf_le_right.trans (centralizer_le hPA))
  have hVZ : F.Vi 1 ≤ (center P).map P.subtype := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact inf_le_right
  apply lt_of_le_not_ge hVZ
  intro hle
  exact hfix (hcent.trans (hle.trans s.kernel_le))

/-- Both original centralizer branches give strict enlargement of V₁ in Z(O₂(K)). -/
theorem extraspecial_core_center_strict
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
 :
    F.Vi 1 < (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype := by
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
      extraspecial_outer_central_seed h hab structural previous faithful he hc
    exact extraspecial_core_center_strict_of_outer_seed h hab structural previous faithful he C hCP hCU hCA hCK
  · obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
      extraspecial_faithful_central_seed h hab structural previous faithful he hc
    exact extraspecial_core_center_strict_of_central_seed h hab structural previous faithful he C hCP hCU hCA hCK

/-- Source 14.7.25, with both cases of 14.7.23 discharged. -/
theorem extraspecial_center_strict
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
 :
    F.Vi 1 < (center (K F)).map (K F).subtype :=
  (extraspecial_core_center_strict h hab structural previous faithful he).trans_le
    (extraspecial_core_center_central d h hab structural previous faithful earlier he)

/-- The original H-normal central subgroup of order four, in both branches. -/
theorem extraspecial_center_four
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
 :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ F.H ≤ normalizer (D : Set G) := by
  have hlt := extraspecial_core_center_strict h hab structural previous faithful he
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZK : Z ≤ (center (K F)).map (K F).subtype :=
    extraspecial_core_center_central d h hab structural previous faithful earlier he
  have hPT : P ≤ (T : Subgroup G) := by
    exact (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hZT : Z ≤ (T : Subgroup G) := (map_subtype_le _).trans hPT
  have hVT : F.Vi 1 ≤ (T : Subgroup G) := hlt.le.trans hZT
  have hHnZ : F.H ≤ normalizer (Z : Set G) :=
    ((H_normalizes_K F).trans
      (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  let V₀ := (F.Vi 1).subgroupOf (T : Subgroup G)
  let Z₀ := Z.subgroupOf (T : Subgroup G)
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (F.invariant 1)
  let : Z₀.Normal := normal_subgroupOf_of_le_normalizer ((F.invariant 1).trans hHnZ)
  have hlt₀ : V₀ < Z₀ := by
    apply lt_of_le_not_ge (subgroupOf_mono _ hlt.le)
    intro hh
    have hm := map_mono (f := (T : Subgroup G).subtype) hh
    rw [map_subgroupOf_eq_of_le hZT,map_subgroupOf_eq_of_le hVT] at hm
    exact hlt.not_ge hm
  obtain ⟨X,hX,hVX,hXZ,hindex⟩ := exists_normal_index_two_step
    (T : Subgroup G) T.isPGroup' V₀ Z₀ hlt₀
  let D := X.map (T : Subgroup G).subtype
  have hVD : F.Vi 1 ≤ D := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hVX
    rwa [map_subgroupOf_eq_of_le hVT] at hh
  have hDZ : D ≤ Z := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hXZ
    rwa [map_subgroupOf_eq_of_le hZT] at hh
  have hcard : Nat.card D = 4 := by
    have hmul := relIndex_mul_card_of_le hVX
    have hVcard : Nat.card V₀ = 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv]
      simpa using F.card 1 (by decide)
    rw [hindex,hVcard] at hmul
    rw [card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hmul.symm
  have hTnD : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    let : X.Normal := hX
    have hh := (map_mono (f := (T : Subgroup G).subtype)
      (show (⊤ : Subgroup (T : Subgroup G)) ≤ normalizer (X : Set (T : Subgroup G)) from
        le_normalizer_of_normal)).trans
      (X.le_normalizer_map (T : Subgroup G).subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨D,hVD,hDZ.trans hZK,hcard,?_⟩
  rw [residual_product]
  apply sup_le _ hTnD
  apply (le_centralizer_iff.mp _).trans (Subgroup.centralizer_le_normalizer _)
  rw [map_center_subtype_eq_inf_centralizer] at hZK
  exact hDZ.trans (hZK.trans inf_le_right)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
