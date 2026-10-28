module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointNormality
public import Theory.Representation.BinaryConjugationSection.DisplacementBound

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem conjugate_centralizer' (A : Subgroup G) (g : G) :
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
private theorem partner_normalized (c : CriticalPath (L := L) F) :
    centralizer (c.Zα : Set G) ≤ normalizer (c.Uα : Set G) := by
  have hn : conjugate F.H c.conjugator = normalizer (c.Zα : Set G) :=
    map_equiv_normalizer_eq (F.Vi 1) (MulAut.conj c.conjugator⁻¹)
  have hh := (map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom)
    (le_normalizer_conjugateSpanBy V F.H)).trans (le_normalizer_map _)
  change conjugate F.H c.conjugator ≤ normalizer (c.Uα : Set G) at hh
  exact (Subgroup.centralizer_le_normalizer _).trans (hn ▸ hh)

private theorem critical_commutator_le_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : ⁅F.U,c.Uα⁆ ≤ F.U ⊓ c.Uα := by
  exact le_inf (le_normalizer_iff_commutator_le_left.mp
    (((critical_le_Q h structural c).trans (Q_le_H F)).trans
      (le_normalizer_conjugateSpanBy V F.H)))
    (le_normalizer_iff_commutator_le_right.mp (G2Source.normalizes_partner h c))

private theorem critical_point_le_span_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) : c.Zα ≤ F.U := by
  rw [←critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha]
  exact (commutator_mono inf_le_left le_rfl).trans
    ((critical_commutator_le_intersection h structural c).trans inf_le_left)

/-- The full U-centralizer moves the reciprocal span only inside its actual U-centralizer. -/
theorem centralizer_critical_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅centralizer (F.U : Set G),c.Uα⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
  have hZU := critical_point_le_span_of_normal_card_two h hab structural hescape hn s c hs ha
  exact le_inf (le_normalizer_iff_commutator_le_right.mp
    ((centralizer_le hZU).trans (partner_normalized c)))
    (le_normalizer_iff_commutator_le_left.mp
      (((critical_le_Q h structural c).trans (Q_le_H F)).trans
        (s.normalized.trans (normalizer_le_normalizer_centralizer _))))

/-- The reciprocal U-centralizer has the same index four as the original one. -/
theorem reciprocal_centralizer_index_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (c.Uα ⊓ centralizer (F.U : Set G)).relIndex c.Uα = 4 := by
  have hAH := (critical_le_Q h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q h structural r.path).trans (Q_le_H F))]
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
  rw [conjugate_inf,r.base_U,conjugate_centralizer',r.tip_U] at hm
  exact hm.trans hi

/-- The reciprocal centralizer has order 32 and at most four cosets modulo U.
The order-eight critical commutator is retained inside the intersection. -/
theorem extraspecial_reciprocal_centralizer_size
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  have hescape := h.flag_escape F previous
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
    have hi := critical_commutator_le_intersection h structural c
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (h.flag_escape F previous) hn sU c hs htwo
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      (h.flag_escape F previous) hn sU c hs htwo
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
    (((critical_le_Q h structural c).trans (Q_le_H F)).trans hNN)
  have hE : ⁅N,c.Uα⁆ ≤ E :=
    (commutator_mono (s.kernel_le.trans hB) le_rfl).trans hc
  exact (le_inf hE hN).trans (hEN.le.trans inf_le_left)

/-- Original-group application of the centralizer-series estimate in
14.7.20(2). The actual Heisenberg residual supplies point normality,
the selected reciprocal path, and all displacement bounds. -/
theorem extraspecial_centralizer_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      (h.flag_escape F previous) hn sU c hs htwo,?_⟩
  intro B N hB hUN W aW mW ρ s a ha
  refine ⟨extraspecial_centralizer_section_displacement
    h hab structural previous hex hcard hexp c hs hB hUN s a ha,?_⟩
  intro hr
  exact (extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr).2.2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
