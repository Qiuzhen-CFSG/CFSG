module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration
public import Theory.Representation.BinaryOffender.FixedLineHyperplane

/-!
# A fixed-line alternative on the original opposite action

The cross-commutator bound [Wᵍ,W] ≤ V gives the literal filtration
U/V₁ → W/V₁ → V/V₁ → 0. Its middle term is a hyperplane and its last
term is a fixed line. Common-center displacement duality therefore bounds
fixed codimension by rank(A*)+1 without asserting that S₂/V₁ is fixed.
The existing chief count makes the cubic ratio strictly less than two.

The Chapter 12 application combines this with the whole-action lower
bound. The cross-commutator premise remains an ambient source obligation;
G.2.3's weaker bound into S₂ does not discharge it.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement ENNReal
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- On the literal quotient, a cross-commutator in V gives a cubic actor and its exact index budget. -/
theorem binary_opposite_cubic_of_cross_commutator
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hc : ⁅conjugate (D.W g) g,D.W g⁆ ≤ D.V)
    (hn : ((conjugate (D.W g) g).subgroupOf D.H).map (projection h) ≠ ⊥) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    IsCubic (representation h) E ∧ fixedCodim (representation h) E ≤ rank E + 1 := by
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  let c := conjugationSection h
  obtain ⟨he,_⟩ := binary_opposite_image h b g hgL hgN
  obtain ⟨hI,_,hnorm,hindex,_⟩ := binary_source_inputs h b h.U_normal_in_T.1 g hgL hgN
  obtain ⟨hAU,_,_,hAV,hVE⟩ := binary_opposite_commutator_filtration h b g hgL hgN
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hVS : D.V ≤ D.S g := by
    obtain ⟨_,_,_,_,_,_,_,hES,_⟩ :=
      D.binary_source_clauses_three_to_seven h b h.U_normal_in_T.1 h.frattini_U_le_point
        g hgL hgN hI (binarySourceCoreEquiv h b h.U_normal_in_T.1 g hgL hgN) hnorm hindex
    exact hVE.trans hES
  have hVW : D.V ≤ D.W g := le_inf hVU hVS
  have hline : Module.finrank (ZMod 2) (c.imageSpace D.V) = 1 := by
    apply c.imageSpace_finrank_of_index D.V hVU 1
    have hi := (D.V₁.subgroupOf D.V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h.point_le).toEquiv,b.point_card,b.card_V] at hi
    change 2 * D.V₁.relIndex D.V = 4 at hi
    norm_num
    omega
  have hhyper := c.imageSpace_codimension_of_index (D.W g) inf_le_left
    (h.point_le.trans hVW) 1 (by simpa using hindex)
  apply cubic_bound_of_fixed_line_hyperplane (representation h) E ⟨hn,he⟩
    (c.imageSpace (D.W g)) (c.imageSpace D.V) hline hhyper
  · intro a ha v
    obtain ⟨a,ha,rfl⟩ := ha
    exact c.displacement_range_le_imageSpace_of_commutator_le _ _ hAU a ha ⟨v,rfl⟩
  · intro a ha v hv
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff (D.W g) v).mp hv
    let w : D.U := (⟨(a:G)*u*(a:G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized a.property) u).mp u.property⟩ : D.U)*u⁻¹
    apply (c.mem_imageSpace_iff D.V _).mpr
    refine ⟨w,hc (commutator_mem_commutator ha hu),?_⟩
    change (c.coordinates (_ * u⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    change (c.coordinates ⟨(a:G)*u*(a:G)⁻¹,_⟩).toAdd + -(c.coordinates u).toAdd = _
    rw [c.equivariant]
    exact (sub_eq_add_neg _ _).symm
  · intro v hv a
    obtain ⟨a',ha',heq⟩ := a.property
    change representation h (a : Actor h) v = v
    rw [←heq]
    exact c.fixed_on_imageSpace_of_commutator_le _ _ (hAV.le.trans bot_le) a' ha' v hv


/-- Strict rank growth turns the fixed-line budget into the required strict cubic bound. -/
theorem binary_opposite_strict_cubic_of_cross_commutator
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hc : ⁅conjugate (D.W g) g,D.W g⁆ ≤ D.V)
    (hm : 1 < rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h))) :
    cubicRatio (representation h) < 2 := by
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  have hn : E ≠ ⊥ := by
    intro hh
    change 1 < rank E at hm
    simp only [hh,Representation.BinaryOffender.rank_bot] at hm
    omega
  obtain ⟨he,_⟩ := binary_opposite_image h b g hgL hgN
  obtain ⟨hcu,hcodim⟩ := binary_opposite_cubic_of_cross_commutator h b g hgL hgN hc hn
  have hsmall : fixedCodim (representation h) E < 2 * rank E := by
    change 1 < rank E at hm
    change fixedCodim (representation h) E ≤ rank E + 1 at hcodim
    omega
  have hr : actionRatio (representation h) E < 2 := by
    have hpos := (show IsElementaryTwo E from ⟨hn,he⟩).rank_pos
    have hzero : (rank E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
    rw [actionRatio, ENNReal.div_lt_iff (Or.inl hzero) (Or.inl (by simp))]
    exact_mod_cast hsmall
  exact (iInf_le_of_le E (iInf_le_of_le ⟨⟨hn,he⟩,hcu⟩ le_rfl)).trans_lt hr

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
