module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.FullDenominator
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.RankEight
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Critical

/-!
# Strict endpoint selection and exchanged-factor transport

The strict F.9 selection retains one endpoint, its literal denominators and
its quadratic actor. The full-denominator branch reuses the shared returned
line action, so both branches may be imported in the final source assembly.
Factor confinement and the geometric alternatives of 14.6.13 remain separate.

Source: Aschbacher--Smith, 14.6.13, printed pp.1031--1032.
-/

set_option linter.style.haveILetI false

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- A genuine critical endpoint selected by the F.9 rank comparison. The
denominators and actor image are literal subgroups, using the same representative. -/
structure SelectedQuadraticEndpoint {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁) where
  endpoint : h.CriticalEndpoint
  left_strict : commutatorPreimage D.UH (endpoint.conjugate D.UH)
    (endpoint.conjugate D.V₁) < D.UH
  strict : commutatorPreimage (endpoint.conjugate D.UH) D.UH D.V₁ < endpoint.conjugate D.UH
  comparison : Nat.log 2 ((commutatorPreimage D.UH (endpoint.conjugate D.UH)
    (endpoint.conjugate D.V₁)).relIndex D.UH) ≤ rank (actorImage D.H (endpoint.conjugate D.UH))
  quadratic : QuadraticMember a.representation (actorImage D.H (endpoint.conjugate D.UH))

/-!
The endpoint is selected before the two exchanged factors are oriented.  The
following lemmas perform the later orientation with the actual element from
`ExchangedFactorSetup.exchanged`.  They are deliberately stated for literal
actor images and `firstSupport`; no abstract support tag is introduced.
-/

omit [Finite G] in
theorem exchange_factor_inverse
    {H1 H2 : Subgroup G} (x : G)
    (hxe : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2) :
    H2.map (MulAut.conj x).toMonoidHom = H1 := by
  rw [← hxe]
  change (H1.conjBy x⁻¹).conjBy x = H1
  exact Subgroup.conjBy_inv' H1 x

omit [Finite G] in
theorem exchange_factor_actor_transport
    {H U Z T H0 H1 H2 : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z)
    (p : ℕ)
    (d : OddNormalizer.ExchangedFactorSetup a T p H0 H1 H2)
    (hTH : T ≤ H) (x : G) (hx : x ∈ T)
    (hxe : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2)
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : B ≤ actorImage H H2) :
    B.map (MulAut.conj (QuotientGroup.mk' (pCore 2 H)
      ⟨x, hTH (hx)⟩)).toMonoidHom ≤ actorImage H H1 := by
  have hH2 : H2 ≤ H := d.second_le.trans d.zero_le
  have he := OddNormalizer.actorImage_conjugate H2 hH2
    (⟨x, hTH hx⟩ : H)
  change actorImage H (H2.map (MulAut.conj x).toMonoidHom) = _ at he
  rw [exchange_factor_inverse x hxe] at he
  calc
    B.map (MulAut.conj (QuotientGroup.mk' (pCore 2 H)
      ⟨x, hTH hx⟩)).toMonoidHom ≤
        (actorImage H H2).map (MulAut.conj (QuotientGroup.mk' (pCore 2 H)
          ⟨x, hTH hx⟩)).toMonoidHom := map_mono hB
    _ = actorImage H H1 := he.symm

omit [Finite G] in
theorem exchange_factor_support_transport
    {H U Z T H0 H1 H2 : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z)
    (p : ℕ) (d : OddNormalizer.ExchangedFactorSetup a T p H0 H1 H2)
    (hTH : T ≤ H) (x : G) (hx : x ∈ T)
    (hxe : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2)
    (P : Subgroup G) (hP : P ≤ OddNormalizer.firstSupport a H2) :
    P.map (MulAut.conj x).toMonoidHom ≤ OddNormalizer.firstSupport a H1 := by
  have hH2 : H2 ≤ H := d.second_le.trans d.zero_le
  have hback := exchange_factor_inverse x hxe
  have hs : (OddNormalizer.firstSupport a H2).map
      (MulAut.conj x).toMonoidHom = OddNormalizer.firstSupport a H1 := by
    unfold OddNormalizer.firstSupport
    rw [OddNormalizer.supportPreimage_conjugate a _ (⟨x, hTH hx⟩ : H),
      moved_map_conjugate]
    rw [← OddNormalizer.actorImage_conjugate H2 hH2 (⟨x, hTH hx⟩ : H), hback]
  calc
    P.map (MulAut.conj x).toMonoidHom ≤
        (OddNormalizer.firstSupport a H2).map
          (MulAut.conj x).toMonoidHom := map_mono hP
    _ = OddNormalizer.firstSupport a H1 := hs

theorem selected_endpoint_exchange_alignment
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    [IsElementaryAbelian 2 D.UH]
    {a : LocalQuotientAction D.H D.UH D.V₁}
    {p : ℕ} {H0 H1 H2 : Subgroup G}
    (d : OddNormalizer.ExchangedFactorSetup a (D.T : Subgroup G) p H0 H1 H2)
    (hTH : (D.T : Subgroup G) ≤ D.H) (x : G) (hx : x ∈ D.T)
    (hxe : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2)
    (hb : 3 ≤ h.b)
    (c : SelectedQuadraticEndpoint h a)
    (hactor : actorImage D.H (c.endpoint.conjugate D.UH) ≤ actorImage D.H H2)
    (hpoint : c.endpoint.conjugate D.V₁ ≤ OddNormalizer.firstSupport a H2) :
    actorImage D.H ((c.endpoint.conjugate D.UH).map
      (MulAut.conj x).toMonoidHom) ≤ actorImage D.H H1 ∧
      (c.endpoint.conjugate D.V₁).map (MulAut.conj x).toMonoidHom ≤
        OddNormalizer.firstSupport a H1 := by
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hA : c.endpoint.conjugate D.UH ≤ D.H :=
    (map_mono hUV).trans (c.endpoint.large_le hb)
  have hactor' := exchange_factor_actor_transport a p d hTH x hx hxe
    (actorImage D.H (c.endpoint.conjugate D.UH)) hactor
  have he := OddNormalizer.actorImage_conjugate (c.endpoint.conjugate D.UH)
    hA (⟨x, hTH hx⟩ : D.H)
  change actorImage D.H ((c.endpoint.conjugate D.UH).map
    (MulAut.conj x).toMonoidHom) = _ at he
  constructor
  · rw [he]
    exact hactor'
  exact exchange_factor_support_transport a p d hTH x hx hxe
    (c.endpoint.conjugate D.V₁) hpoint

/-- The independent recognition input permitted in the endpoint task: only
the actual action and its marked plane, with no endpoint geometry. -/
def FourActionRecognition {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (H1 : Subgroup G) : Prop :=
  Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 →
    ∃ o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2),
      ∃ i, o.plane i = OddNormalizer.firstSupport a H1

/-- Strictness gives the positive denominator rank used in (*) on p.1032. -/
theorem SelectedQuadraticEndpoint.denominator_rank_pos {D : ChapterF.Section09.Setup G}
    {h : D.Hypothesis} [IsElementaryAbelian 2 D.UH]
    {a : LocalQuotientAction D.H D.UH D.V₁} (c : SelectedQuadraticEndpoint h a) :
    0 < Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) := by
  letI : (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).IsFiniteRelIndex D.UH :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  apply Nat.log_pos (by decide)
  have h0 : (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH ≠ 0 := relIndex_ne_zero
  have h1 : (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH ≠ 1 := by
    intro he
    exact c.left_strict.not_ge (relIndex_eq_one.mp he)
  omega

/-- The selected endpoint's strict literal denominator supplies the premise
of the genuine F.9.17 reversal, simultaneously on every H-normalized label. -/
theorem SelectedQuadraticEndpoint.reversal {D : ChapterF.Section09.Setup G}
    {h : D.Hypothesis} [IsElementaryAbelian 2 D.UH]
    {a : LocalQuotientAction D.H D.UH D.V₁} (c : SelectedQuadraticEndpoint h a)
    (hb : 3 ≤ h.b) :
    ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
      D.H ≤ normalizer (A : Set G) →
      j.conjugate (c.endpoint.conjugate A) = A := by
  apply c.endpoint.reverse_labels hb
  intro hc
  have hγH : c.endpoint.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (c.endpoint.large_le hb)
  have hs := c.strict
  rw [critical_denominator_eq h _ hγH, inf_eq_left.mpr hc] at hs
  exact lt_irrefl _ hs

/-! The strict branch as a standalone producer.  Keeping the original
critical pair in the conclusion of the F.9 selection is what lets a consumer
reuse its endpoint representative and its terminal conjugator. -/
theorem selected_of_strict_pair (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V)
    (hbc : 3 ≤ c.path.length)
    (hstrict : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ < c.Ugamma D.Vplus)
    (hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    Nonempty (SelectedQuadraticEndpoint h a) := by
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  letI : IsElementaryAbelian 2 (Source.UH D.H D.Vplus) := ‹IsElementaryAbelian 2 D.UH›
  letI : IsElementaryAbelian 2 (Source.VH D.H D.V) := by
    change IsElementaryAbelian 2 (conjugateSpanBy D.V D.H)
    rw [← hplus]
    exact ‹IsElementaryAbelian 2 D.UH›
  have hlength (c' : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :
      3 ≤ c'.path.length := by
    rw [c'.length_eq]
    rw [← c.length_eq]
    exact hbc
  have geo (c' : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :=
    f9_earlierGeometry D h c' (hlength c') hcomm
  obtain ⟨d,hd,hdγ,_,hcomp,hq⟩ := Reorientation.exists_quadratic_selection
    D.Vplus D.V₁ c s (f9_section_faithful D h s) hbc h.plus_le
    (fun c' => (geo c').Vgamma_H)
    ((conjugateSpanBy_mono h.plus_le le_rfl).trans (geo c).VH_endpoint)
    (geo c).first_kernel (left_denominator_strict D h hplus c hbc) hstrict
    (fun c' => (c'.quadratic_star_on_Utilde D.Vplus D.V₁ s h.plus_le
      (geo c').VH_endpoint).2)
    (fun c' _ hc => f9_fixedCodim_le_twice_rank D h c' (hlength c') s hc)
  have hdlen := hlength d
  obtain ⟨i,hi⟩ := f9_criticalPair_endpoint D h d (by omega)
  have he (A : Subgroup G) : i.conjugate A =
      A.map (MulAut.conj (d.gb : G)).toMonoidHom := by
    change A.map (MulAut.conj i.representative).toMonoidHom = _
    rw [hi]
  refine ⟨⟨i, ?_, ?_, ?_, ?_⟩⟩
  · rw [he D.UH, he D.V₁]
    change Source.DH (Source.UH D.H D.Vplus) (d.Ugamma D.Vplus)
      (d.Aone D.V₁) < Source.UH D.H D.Vplus
    exact hd
  · rw [he D.UH]
    change Source.Dgamma (d.Ugamma D.Vplus) (Source.UH D.H D.Vplus) D.V₁ <
      d.Ugamma D.Vplus
    exact hdγ
  · rw [he D.UH, he D.V₁]
    change Reorientation.denominatorRank D.Vplus D.V₁ d ≤
      rank (Source.starImage D.H (d.Ugamma D.Vplus))
    exact hcomp
  · rw [he D.UH]
    change QuadraticMember a.representation
      (Source.starImage D.H (d.Ugamma D.Vplus))
    exact hq

/-- Select an endpoint without losing its conjugator or strict denominator.
This is the F.9 selection stage, before the factor geometry of 14.6.13. -/
theorem full_or_selected (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁)
    (hb : 3 ≤ h.b) (ho : Odd h.b)
    (hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    (∃ i : h.CriticalEndpoint, ∃ t : ReturnedLineAction D.H D.UH D.V₁,
      t.g = i.representative⁻¹) ∨ Nonempty (SelectedQuadraticEndpoint h a) := by
  have hdist : 3 ≤ criticalDistance D.L (D.T : Subgroup G) D.H D.V ∧
      Odd (criticalDistance D.L (D.T : Subgroup G) D.H D.V) := by
    rw [f9_criticalDistance_eq D h]
    exact ⟨hb,ho⟩
  obtain ⟨c,hbc,_⟩ := f9_criticalPair_bounds D h hdist
  have hlength (c' : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :
      3 ≤ c'.path.length := by rw [c'.length_eq]; exact hdist.1
  have geo (c' : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :=
    f9_earlierGeometry D h c' (hlength c') hcomm
  by_cases hs : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ < c.Ugamma D.Vplus
  · let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
    letI : IsElementaryAbelian 2 (Source.UH D.H D.Vplus) := ‹IsElementaryAbelian 2 D.UH›
    letI : IsElementaryAbelian 2 (Source.VH D.H D.V) := by
      change IsElementaryAbelian 2 (conjugateSpanBy D.V D.H)
      rw [←hplus]
      exact ‹IsElementaryAbelian 2 D.UH›
    obtain ⟨d,hd,hdγ,_,hcomp,hq⟩ := Reorientation.exists_quadratic_selection
      D.Vplus D.V₁ c s (f9_section_faithful D h s) hbc h.plus_le
      (fun c' => (geo c').Vgamma_H)
      ((conjugateSpanBy_mono h.plus_le le_rfl).trans (geo c).VH_endpoint)
      (geo c).first_kernel (left_denominator_strict D h hplus c hbc) hs
      (fun c' => (c'.quadratic_star_on_Utilde D.Vplus D.V₁ s h.plus_le
        (geo c').VH_endpoint).2)
      (fun c' _ hc => f9_fixedCodim_le_twice_rank D h c' (hlength c') s hc)
    obtain ⟨i,hi⟩ := f9_criticalPair_endpoint D h d (by have := hlength d; omega)
    have he (A : Subgroup G) : i.conjugate A = A.map (MulAut.conj (d.gb : G)).toMonoidHom := by
      change A.map (MulAut.conj i.representative).toMonoidHom = _
      rw [hi]
    refine Or.inr ⟨⟨i,?_,?_,?_,?_⟩⟩
    · rw [he D.UH, he D.V₁]
      change Source.DH (Source.UH D.H D.Vplus) (d.Ugamma D.Vplus)
        (d.Aone D.V₁) < Source.UH D.H D.Vplus
      exact hd
    · rw [he D.UH]
      change Source.Dgamma (d.Ugamma D.Vplus) (Source.UH D.H D.Vplus) D.V₁ <
        d.Ugamma D.Vplus
      exact hdγ
    · rw [he D.UH, he D.V₁]
      change Reorientation.denominatorRank D.Vplus D.V₁ d ≤
        rank (Source.starImage D.H (d.Ugamma D.Vplus))
      exact hcomp
    · rw [he D.UH]
      change QuadraticMember a.representation
        (Source.starImage D.H (d.Ugamma D.Vplus))
      exact hq
  · have hf := eq_of_le_of_not_lt (commutatorPreimage_le (c.Ugamma D.Vplus) D.UH D.V₁) hs
    obtain ⟨t,ht⟩ := returned_line_of_full D h hplus c hbc hcomm hf
    obtain ⟨i,hi⟩ := f9_criticalPair_endpoint D h c (by omega)
    exact Or.inl ⟨i,t,ht.trans (congrArg Inv.inv hi).symm⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hH

/-- The original rank-two prefix supplies either the inverse-endpoint line
action or a genuine strict quadratic endpoint. Both conjugators leave Mc.
The factor geometry and the two alternatives of 14.6.13 remain to be proved. -/
theorem source_rankTwo_endpoint_selection :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    (∃ t : ReturnedLineAction D.H D.UH D.V₁, t.g ∉ Mc) ∨
      (∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  letI : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  change (∃ t : ReturnedLineAction D.H D.UH D.V₁, t.g ∉ Mc) ∨
    (∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc)
  obtain ⟨hb,ho,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hout := source_rankTwo_critical_not_mem_Mc hG T hempty hM hunique hmany hcard e hab H hH
  rcases full_or_selected D h rfl a hb ho
      (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab) with
    ⟨i,t,ht⟩ | hselected
  · refine Or.inl ⟨t,?_⟩
    rw [ht,inv_mem_iff]
    exact hout i
  · obtain ⟨c⟩ := hselected
    exact Or.inr ⟨c,hout c.endpoint⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
