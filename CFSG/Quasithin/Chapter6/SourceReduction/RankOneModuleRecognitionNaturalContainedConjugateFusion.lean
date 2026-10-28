module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionCorank
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry

/-!
# Symmetry, common fixed lines, and conjugate fusion

The rank bound and s(G,B)=n make both action coranks equal to n under
mutual normalization. Thus the literal induced automizers are offenders.
Natural offender geometry identifies C_B(A)=[B,A]=Z_S. Counting identifies
C_A(B) with the same line, and hence B∩A=Z_S. Applying the geometry after
inverse conjugation places Z_S^(g⁻¹) in the L-orbit of Z_S. With Lean's
left-conjugation convention the correcting transporter is g*l. Finally
the normalizer factorization and the TI property produce a conjugator in
C_G(Z_S).

This proves the deductions of 6.1.11 from explicit local inputs, not the
construction of those inputs. No conclusion of 6.1.15 or 6.1.27 is used.
Source: Aschbacher--Smith, printed p.670 (PDF p.687).
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- Equal action coranks on both members of the pair give an actual offender
in the faithful automizer representation, with its literal induced subgroup. -/
theorem conjugate_offender_of_mutual_normalization (B : Subgroup G)
    [IsElementaryAbelian 2 B] {n : ℕ}
    (hs : ChapterE.globalS B = n) (hbound : ElementaryActionRankBound B n)
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ normalizer (B : Set G))
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G))
    (hmut : B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)) :
    IsOffender (ChapterE.automizerRepresentation B)
      (ChapterE.inducedAutomizer B (B.map (MulAut.conj g).toMonoidHom)) := by
  let : IsElementaryAbelian 2 (B.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hforward := conjugate_action_corank_eq_of_rank_bound B hs hbound g hg hnon
  have hback := conjugate_action_corank_eq_of_rank_bound B hs hbound g⁻¹
    (fusion_inverse_normalizes hmut) (fusion_inverse_noncentralizing hnon)
  have hfixed : ChapterE.subgroupCorank B
      (B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)) = n := by
    simpa only [inv_inv] using (fusion_pullback_corank B g⁻¹).trans hback
  refine ⟨⟨?_, ChapterE.inducedAutomizer_elementary _ _ hg⟩, ?_⟩
  · exact fun he => hnon ((ChapterE.inducedAutomizer_eq_bot_iff hg).mp he)
  · rw [ChapterE.fixedCodim_inducedAutomizer _ _ hg,
      ChapterE.rank_inducedAutomizer _ _ hg, hfixed, hforward]

/-- The two centralizers and the intersection are the same distinguished
line. This is the symmetry and counting step in 6.1.11. -/
theorem mutual_conjugate_line_geometry
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hbound : ElementaryActionRankBound (layer L V) n)
    (hgeometry : letI := h.layer_elementary;
      NaturalOffenderFixedLines (T : Subgroup G) L (layer L V) (ZS (T : Subgroup G) L V))
    (g : G) (hg : (layer L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G))
    (hmut : layer L V ≤ normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G)) :
    let B := layer L V
    let A := B.map (MulAut.conj g).toMonoidHom
    let Z := ZS (T : Subgroup G) L V
    B ⊓ centralizer (A : Set G) = Z ∧
      A ⊓ centralizer (B : Set G) = Z ∧ ⁅B, A⁆ = Z ∧ B ⊓ A = Z ∧
      ∃ l ∈ L, Z.map (MulAut.conj g⁻¹).toMonoidHom =
        Z.map (MulAut.conj l).toMonoidHom := by
  let := h.layer_elementary
  let B := layer L V
  let A := B.map (MulAut.conj g).toMonoidHom
  let Z := ZS (T : Subgroup G) L V
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAN : A ≤ normalizer (B : Set G) := hg.trans h.sylow_normalizes_layer
  have hoff := conjugate_offender_of_mutual_normalization B hs hbound g hAN hnon hmut
  obtain ⟨hfix, hcomm⟩ := (hgeometry A inferInstance hAN hoff).2 hg
  have hZB : Z ≤ B := inf_le_left
  have hZA : Z ≤ A := hcomm.symm.le.trans
    (le_normalizer_iff_commutator_le_right.mp hmut)
  have hZC : Z ≤ A ⊓ centralizer (B : Set G) :=
    le_inf hZA (hZB.trans B.le_centralizer)
  have hcA := conjugate_action_corank_eq_of_rank_bound B hs hbound g hAN hnon
  have hcardA : Nat.card A = 2 ^ (n * 2) :=
    (card_map_of_injective (MulAut.conj g).injective).trans hnatural.card
  have hcC := card_eq_pow_of_half_corank inf_le_left hcardA hcA
  have hcZ : Nat.card Z = 2 ^ n :=
    (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  have hcentral : A ⊓ centralizer (B : Set G) = Z :=
    (eq_of_le_of_card_ge hZC (by rw [hcZ, hcC])).symm
  have hinter : B ⊓ A = Z := by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans B.le_centralizer)).trans_eq hcentral
    · exact le_inf hZB hZA
  have hInvN := fusion_inverse_normalizes hmut
  have hInvNon := fusion_inverse_noncentralizing hnon
  have hInvMut : B ≤ normalizer (B.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAN
    rwa [fusion_map_conj_inverse, map_equiv_normalizer_eq] at hh
  have hInvOff := conjugate_offender_of_mutual_normalization B hs hbound g⁻¹
    hInvN hInvNon hInvMut
  obtain ⟨l, hl, hline⟩ :=
    (hgeometry (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (IsElementaryAbelian.map _) hInvN hInvOff).1
  refine ⟨hfix, hcentral, hcomm, hinter, l, hl, ?_⟩
  rw [← fusion_pullback_centralizer, hcentral] at hline
  exact hline

/-- Source 6.1.11's fusion deduction from the local offender geometry and
6.1.9(5). The factor in M normalizes B by the nonzero-line TI argument. -/
theorem mutualConjugateFusion_of_local_inputs
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hbound : ElementaryActionRankBound (layer L V) n)
    (hgeometry : letI := h.layer_elementary;
      NaturalOffenderFixedLines (T : Subgroup G) L (layer L V) (ZS (T : Subgroup G) L V))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L V)) :
    MutualConjugateFusion (T : Subgroup G) (layer L V) (ZS (T : Subgroup G) L V) := by
  intro g hg hnon hmut
  obtain ⟨_, _, _, _, l, hl, hline⟩ :=
    mutual_conjugate_line_geometry h hnatural hs hbound hgeometry g hg hnon hmut
  have hd : g * l ∈ normalizer (ZS (T : Subgroup G) L V : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := congrArg (fun U : Subgroup G => U.map (MulAut.conj g).toMonoidHom) hline
    have hback := fusion_map_conj_inverse (ZS (T : Subgroup G) L V) g⁻¹
    simp only [inv_inv] at hback
    rw [hback, fusion_map_conj_mul] at he
    exact he.symm
  obtain ⟨c, hc, m, hm, he⟩ := hfactor (g * l) hd
  have hmB : m ∈ normalizer (layer L V : Set G) :=
    inf_normalizer_le_of_trivial_intersections hE.ti h.ZS_ne_bot inf_le_left hm
  have hLN : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  have hlB : (layer L V).map (MulAut.conj l).toMonoidHom = layer L V :=
    mem_normalizer_iff_map_conj_eq.mp (hLN hl)
  have hmB' : (layer L V).map (MulAut.conj m).toMonoidHom = layer L V :=
    mem_normalizer_iff_map_conj_eq.mp hmB
  refine ⟨c, hc, ?_⟩
  calc
    (layer L V).map (MulAut.conj g).toMonoidHom =
        (layer L V).map (MulAut.conj (g * l)).toMonoidHom := by
      rw [← fusion_map_conj_mul, hlB]
    _ = (layer L V).map (MulAut.conj (c * m)).toMonoidHom := by rw [he]
    _ = (layer L V).map (MulAut.conj c).toMonoidHom := by
      rw [← fusion_map_conj_mul, hmB']

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
