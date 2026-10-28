module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.LinearThree.Invariants
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.QuotientActions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.LinearThree

/-!
# Separating central and noncentral PSL₃ rows

Every inner involution is two-central and fixes a solvable root centralizer.
The field, graph, and graph-field residuals are nonsolvable, except for the
small graph endpoint PSL₂(2)′ and the excluded PSL₃(4) graph-field endpoint.
Solvability is preserved through the actual central kernels and the O³
modification, so isomorphic modified residuals cannot join the two kinds of
rows. At PSL₃(2), both two-valuations are zero; instead the graph residual has a
factor of three, absent from the root centralizer. The order formula excludes
the O³ modification there, and central two-group kernels preserve this divisor.

The existing universal outer-centralizer table remains an explicit earlier
source input. Its field PSL₃′, graph PSL₂′, graph-field PSU₃, and E₉ rows
are all retained, on actual fixed-subgroup carriers. Inner Sylow-centrality
is proved from matrices; no pair-separation or centrality-transfer premise
is assumed. The argument works with all central covers and needs no
additional 16.1.2 covering clause. Supplying the earlier table remains the
responsibility of the final Lie-family/source assembly.

Source: Aschbacher–Smith, 16.1.2–4, printed pp.1170–1172, and
16.5.5–6(4), printed p.1197 of the combined manuscript of 1 March 2004.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.LinearThree
open Matrix.PSL3Even.ResidualComparison
open SylowSymmetry.ReverseDelta.Comparison.LieFamilies

variable (F : Type*) [Field F] [Finite F] {n : ℕ}
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Comparison on a specified central quotient model, retaining all central kernels. -/
theorem separation_of_quotient_model [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hn : 1 ≤ n) (hn2 : n ≠ 2)
    (hF : Nat.card F = 2 ^ n) (e : (L ⧸ center L) ≃* PSL(3,F))
    (rows : LinearThreeInvolutionRows F n)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (quotientModelAction_order e u).trans hu2
  have hb2 : orderOf b = 2 :=
    (quotientModelAction_order e v).trans hv2
  have ha : IsTwoCentralIn (MulAut.innerSubgroup PSL(3,F)) a :=
    (quotientModelAction_twoCentral_iff e _).mpr hu
  have hai : ∃ x, a = MulAut.conj x := by
    obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp ha).2.1
    exact ⟨x, hx.symm⟩
  have hbo : ¬ ∃ x, b = MulAut.conj x := by
    intro h
    exact hv ((quotientModelAction_twoCentral_iff e _).mp (inner_twoCentral F hn hF b hb2 h))
  obtain ⟨ei⟩ := inner_fixed_equiv_root F hn hF a ha2 hai
  have haiS : Group.IsSolvable a.fixedSubgroup := by
    let := root_centralizer_solvable F hn hF
    exact Group.isSolvable_of_surjective (f := ei.symm.toMonoidHom) ei.symm.surjective
  have hXu : involutionTwoResidual L u.val ≤ L :=
    (involutionTwoResidual_le L u.val).trans inf_le_left
  have hXv : involutionTwoResidual L v.val ≤ L :=
    (involutionTwoResidual_le L v.val).trans inf_le_left
  have huS : Group.IsSolvable (involutionTwoResidual L u.val) := by
    apply (SylowSymmetry.ReverseDelta.Comparison.centralImage_solvable_iff hXu).mp
    let := haiS
    exact Group.isSolvable_of_surjective
      (f := (quotientResidualEquiv hodd e u).symm.toMonoidHom)
      (quotientResidualEquiv hodd e u).symm.surjective
  rintro ⟨d⟩
  have hvS : Group.IsSolvable (involutionTwoResidual L v.val) := by
    apply (modified_solvable_iff v.val).mp
    let := (modified_solvable_iff u.val).mpr huS
    exact Group.isSolvable_of_surjective (f := d.toMonoidHom) d.surjective
  have hbS : Group.IsSolvable (pResidual 2 b.fixedSubgroup) := by
    let := (SylowSymmetry.ReverseDelta.Comparison.centralImage_solvable_iff hXv).mpr hvS
    exact Group.isSolvable_of_surjective
      (f := (quotientResidualEquiv hodd e v).toMonoidHom)
      (quotientResidualEquiv hodd e v).surjective
  let := hbS
  rcases rows.outer_residual b hb2 hbo with hf | hg | hgf | hsmall
  · obtain ⟨m, _, _, ⟨eo⟩⟩ := hf
    exact psl_three_commutator_not_solvable (BinaryGaloisField m)
      (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
  · obtain ⟨eo⟩ := hg
    by_cases hnlarge : 2 ≤ n
    · exact binary_psl_two_commutator_not_solvable hnlarge
        (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
    · have hn1 : n = 1 := by omega
      have hnot : ¬ HasEvenLinearThreeType L :=
        not_even_type_of_binary_quotient_model F (by simpa only [hn1, pow_one] using hF) e
      have hmu : modifiedCentralizerResidual L u.val = involutionTwoResidual L u.val := by
        simp only [modifiedCentralizerResidual, if_neg hnot]
      have hmv : modifiedCentralizerResidual L v.val = involutionTwoResidual L v.val := by
        simp only [modifiedCentralizerResidual, if_neg hnot]
      have heq : Nat.card (involutionTwoResidual L u.val) =
          Nat.card (involutionTwoResidual L v.val) := by
        rw [← hmu, ← hmv, Nat.card_congr d.toEquiv]
      have hout : 3 ∣ Nat.card
          (SylowSymmetry.ReverseDelta.centralImage L (involutionTwoResidual L v.val)) := by
        rw [Nat.card_congr (quotientResidualEquiv hodd e v).toEquiv,
          Nat.card_congr eo.toEquiv]
        exact three_dvd_binary_psl_two_commutator hn
      have hres := (SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.odd_prime_dvd_centralImage_iff
        hodd hXv Nat.prime_three (by decide)).mp hout
      rw [← heq] at hres
      have hthree := (SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.odd_prime_dvd_centralImage_iff
        hodd hXu Nat.prime_three (by decide)).mpr hres
      rw [Nat.card_congr (quotientResidualEquiv hodd e u).toEquiv] at hthree
      have hfix : 3 ∣ Nat.card a.fixedSubgroup :=
        hthree.trans (card_subgroup_dvd_card (pResidual 2 a.fixedSubgroup))
      rw [Nat.card_congr ei.toEquiv] at hfix
      exact root_centralizer_small F (Or.inl hn1) hF hfix
  · obtain ⟨m, hm, hnm, J, hJ, _, hfixed, ⟨eo⟩⟩ := hgf
    exact unitary_not_solvable J hm (by rw [hF, hnm, mul_comm 2 m, pow_mul]) hfixed hJ
      (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
  · exact hn2 hsmall.1

omit F [Field F] [Finite F] in
/-- The intrinsic PSL₃ branch of residual separation in 16.5.6(4).
Only the universal earlier outer-centralizer table remains an explicit input. -/
theorem separation [IsQuasisimple L] (rows : LinearThreeInvolutionTable)
    (hodd : pPrimeCore 2 L = ⊥)
    (_hLie : IsEvenTypeLieComponent L)
    (_hBender : ¬ ClassificationModels.IsBenderModel (L ⧸ center L))
    (_hA6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    {n : ℕ} (hn : 1 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hfour : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (u v : normalizer (L : Set G))
    (_huAmbient : orderOf u.val = 2) (_hvAmbient : orderOf v.val = 2)
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  have hn2 : n ≠ 2 := by
    intro hn2
    exact hfour (by norm_num [hn2] at hmodel ⊢; exact hmodel)
  obtain ⟨F, hfield, hfinite, hF, ⟨c⟩⟩ := hmodel
  exact separation_of_quotient_model F hodd hn hn2 hF c (rows F n hn hF)
    u v hu2 hv2 hu hv

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.LinearThree
