module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
public import Theory.LinearAlgebra.BinaryTwoTransitivity
public import Theory.GroupTheory.Commutator.TwoOrbitSpan
public import Theory.ThreeSubgroups
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
private theorem original_pair_transporter
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
private theorem original_mem_H_of_fixes_point
    (z : G) (hz : F.Vi 1 = zpowers z) {a : G} (h : (MulAut.conj a) z = z) : a ∈ F.H := by
  change a ∈ normalizer (F.Vi 1 : Set G)
  rw [mem_normalizer_iff_map_conj_eq,hz,MonoidHom.map_zpowers]
  exact congrArg zpowers h
omit [Finite G] in
private theorem original_map_U_eq_of_point_eq
    (z : G) (hz : F.Vi 1 = zpowers z) {a b : G}
    (h : (MulAut.conj a) z = (MulAut.conj b) z) :
    F.U.conjBy a = F.U.conjBy b := by
  have hf : (MulAut.conj (b⁻¹*a)) z = z := by
    have hh := congrArg (MulAut.conj b⁻¹) h
    simpa [MulAut.conj_apply,mul_assoc] using hh
  have hn := mem_normalizer_iff_map_conj_eq.mp
    ((le_normalizer_conjugateSpanBy V F.H) (original_mem_H_of_fixes_point z hz hf))
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
      original_map_U_eq_of_point_eq z hz (a := a) (b := 1) (by simpa using hez.symm))
  have hzl : z ≠ (MulAut.conj (l : G)) z := by
    intro hez
    exact he (by simpa only [conjBy_one] using
      original_map_U_eq_of_point_eq z hz (a := l) (b := 1) (by simpa using hez.symm))
  obtain ⟨p,hp,hpz,hpaz⟩ := original_pair_transporter h hzV haz hzV hlz hz1 hazne
    hz1 hlzne hza hzl
  have hpH : p ∈ F.H := original_mem_H_of_fixes_point z hz hpz
  refine ⟨⟨p,hp,hpH⟩,?_⟩
  rw [conjBy_conjBy]
  apply original_map_U_eq_of_point_eq z hz
  simpa only [MulAut.conj_apply,mul_inv_rev,mul_assoc] using hpaz.symm

omit [Finite G] in
private theorem original_L_normalizes_Q : L ≤ normalizer (Q T L : Set G) :=
  le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The original elementary span and its L-closure lie in Q, without Data. -/
theorem original_span_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
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
    rw [←h.centralizer_LT structural]
    exact le_inf (hUT.trans le_sup_right)
      (F.U.le_centralizer.trans (centralizer_le (le_conjugateSpanBy V F.H)))
  exact ⟨hU,conjugateSpanBy_le hU original_L_normalizes_Q⟩

/-- The original commutator span is [S,Q], with both spans literal. -/
theorem original_span_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ⁅conjugateSpanBy F.U L,Q T L⁆ = conjugateSpanBy ⁅F.U,Q T L⁆ L := by
  have hh := commutator_iSup_conjugates F.U L (Q T L)
    (original_span_le_core h hab structural).1 original_L_normalizes_Q
  simpa only [←conjugateSpanBy_eq_iSup_conj] using hh

/-- The two-orbit commutator calculation applies before recognition. -/
theorem original_span_frattini_derived
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
    original_L_normalizes_Q
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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


private theorem normalized_two_image_commutator {D X : Type*} [Group D] [Group X]
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H)) original_L_normalizes_Q ⟨g,hg⟩
  have hnorm : (Q T L).subgroupOf F.H ≤ normalizer (c.Uα.subgroupOf F.H : Set F.H) := by
    apply le_normalizer_iff.mpr
    intro q hq a ha
    exact (mem_normalizer_iff.mp (hQA hq) a).mp ha
  have hk := normalized_two_image_commutator (starMap F)
    ((Q T L).subgroupOf F.H) (c.Uα.subgroupOf F.H) hnorm htwo
  rw [starMap,QuotientGroup.ker_mk'] at hk
  have hfirst := map_mono (f := F.H.subtype) hk
  rw [map_commutator,map_subgroupOf_eq_of_le (Q_le_H F),
    map_subgroupOf_eq_of_le ((critical_le_Q h structural c).trans (Q_le_H F))] at hfirst
  refine ⟨hfirst,?_⟩
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfirst
  rw [map_commutator] at hh
  change ⁅(Q T L).conjBy g⁻¹,c.Uα.conjBy g⁻¹⁆ ≤ (F.H.pCoreIn 2).conjBy g⁻¹ at hh
  have hQi : (Q T L).conjBy g⁻¹ = Q T L :=
    mem_normalizer_iff_map_conj_eq.mp (original_L_normalizes_Q (T := T) (L.inv_mem hg))
  rw [hQi,
    ←hU,conjBy_conjBy,inv_mul_cancel,conjBy_one,
    ←hcore,conjBy_conjBy,inv_mul_cancel,conjBy_one] at hh
  exact hh

/-- The original E=[U,Q] centralizes the reciprocal U, using both point groups. -/
theorem extraspecial_commutator_centralizes_partner
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    rw [←h.centralizer_LT structural]
    exact inf_le_right
  have hrot : ⁅⁅c.Uα,F.U⁆,Q T L⁆ = ⊥ := by
    rw [commutator_comm c.Uα,extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs,
      commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hQV
  have hfirst : ⁅⁅F.U,Q T L⁆,c.Uα⁆ ≤ F.Vi 1 :=
    commutator_commutator_le_of_rotate_of_le_normalizer F.U_le_H (Q_le_H F)
      ((critical_le_Q h structural c).trans (Q_le_H F))
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
    (critical_points_disjoint_of_normal_card_two h hab structural (h.flag_escape F previous) hn s c hs htwo).le_bot)


/-- The original E-span is central in S; the core moves R only inside V. -/
theorem extraspecial_commutator_span_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      mem_normalizer_iff_map_conj_eq.mp (original_L_normalizes_Q hp.1)
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
      (hEU.trans (original_span_le_core h hab structural).1) original_L_normalizes_Q
    rw [←conjugateSpanBy_eq_iSup_conj,←conjugateSpanBy_eq_iSup_conj] at hh
    rw [hh]
    exact conjugateSpanBy_le hmove h.chosen.normalizes

/-- An order-four critical root prevents the second core commutator from vanishing. -/
theorem extraspecial_commutator_span_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  rw [section_action_kernel_eq_core_of_escape h structural (h.flag_escape F previous) s] at hk
  apply hane
  rw [←hba,←map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hk

/-- Original 14.7.19(2): the second commutator span is exactly V. -/
theorem extraspecial_commutator_span_core_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      mem_normalizer_iff_map_conj_eq.mp (original_L_normalizes_Q hl)]
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    exact commutator_mono le_rfl (critical_le_Q h structural c)
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
    (critical_centralizer_indices_of_normal_card_two h hab structural (h.flag_escape F previous) hn s c hs htwo).2
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
