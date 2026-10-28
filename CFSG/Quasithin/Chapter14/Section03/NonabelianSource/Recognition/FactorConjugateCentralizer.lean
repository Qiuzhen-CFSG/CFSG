module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockCore
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorNormalizerSylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorMovement

/-!
# A Sylow conjugate of the original factor centralizer

The centralizer C=C_G(A) is a two-group normalized by RQ. The existing
Sylow description of N_G(A) therefore gives C≤RQ. Since T normalizes
R and Q, every T-conjugate of C remains in RQ and hence in N_G(A).

The chosen factor meets U in an eight-group, larger than the seed
four-group, so the original factor-movement theorem supplies t∈T
moving A. If Cᵗ≤C, then Aᵗ≤R∩C≤K∩C=A. Equal cardinalities would
force Aᵗ=A, a contradiction. This requires no strict enlargement of A.

Source: Aschbacher--Smith, the opening argument of Lemma 14.3.20,
printed p.997. The literal centralizer and right-conjugation convention
are preserved for the automorphism-group application.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_factor_conjugate_centralizer_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let C := centralizer (A : Set G)
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    C≤R⊔Q ∧ ∃ t∈(T : Subgroup G),
      conjugate C t≤normalizer (A : Set G) ∧ ¬conjugate C t≤C := by
  intro C R Q
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let S := R⊔Q
  let NG := normalizer (A : Set G)
  have hSN : S≤NG := (sup_le_sup (pCoreIn_le 2 _) le_rfl).trans hAN
  have hCp : IsPGroup 2 C := (factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8).2
  have hCN : C≤NG := _root_.centralizer_le_normalizer A
  have hSC : S≤normalizer (C : Set G) :=
    hSN.trans (normalizer_le_normalizer_centralizer A)
  obtain ⟨_,_,P,hP⟩ := factor_normalizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN
  change (P : Subgroup NG).map NG.subtype=S at hP
  have hPC : (P : Subgroup NG)≤normalizer (C.subgroupOf NG : Set NG) := by
    intro p hp
    apply le_normalizer_comap NG.subtype
    apply hSC
    rw [←hP]
    exact mem_map_of_mem NG.subtype hp
  have hCS : C≤S := by
    have hh := hCp.comap_subtype.le_sylow_of_normalized P hPC
    intro c hc
    rw [←hP]
    exact mem_map_of_mem NG.subtype
      (hh (show (⟨c,hCN hc⟩ : NG)∈C.subgroupOf NG from hc))
  have hTR : (T : Subgroup G)≤normalizer (R : Set G) := by
    have hcore := (parabolic_residual_core_structure_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).2.2.1
    change (T : Subgroup G)≤normalizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 : Set G)
    rw [←hcore]
    exact h.sylow_normalizes_L.trans
      (normalizer_le_normalizer_characteristic_image (sourceResidual M Mc)
        (pCore 2 (sourceResidual M Mc)))
  have hTQ : (T : Subgroup G)≤normalizer (Q : Set G) :=
    (F.invariant 1).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  have hTS : (T : Subgroup G)≤normalizer (S : Set G) :=
    (le_inf hTR hTQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hx : ∃ x:G,x∈A⊓F.U ∧ x∉rankTwoSeed T M := by
    by_contra hbad
    have hsmall : A⊓F.U≤rankTwoSeed T M := by
      intro x hx
      by_contra hxV
      exact hbad ⟨x,hx,hxV⟩
    have hc := card_le_of_le hsmall
    have hVc : Nat.card (rankTwoSeed T M)=4 := by
      simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
    rw [hc8,hVc] at hc
    omega
  obtain ⟨x,hxA,hxV⟩ := hx
  have hn := elementary_factor_not_sylow_normalized_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hVA x hxA.1 hxA.2 hxV
  have ht : ∃ t:G,t∈(T : Subgroup G) ∧ t∉NG := by
    by_contra hbad
    apply hn
    intro t ht
    by_contra htN
    exact hbad ⟨t,ht,htN⟩
  obtain ⟨t,ht,htN⟩ := ht
  refine ⟨hCS,t,ht,(conjugate_le_of_normalizes hCS t (hTS ht)).trans hSN,?_⟩
  intro hCt
  let N := F.H⊓NG
  let Y := (pResidual 2 N).map N.subtype
  let K := sourceResidual M Mc⊔Y
  have hRK : R≤K := le_sup_left.trans
    (factor_generated_residual_geometry_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hVA hAc hc8 hAN).2.2.1
  have hKC : K⊓C=A := (source_factor_block_core_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hAR hVA hAc hc8 hAN).2.1
  have hAtC : conjugate A t≤C :=
    (map_mono (f:=(MulAut.conj t⁻¹).toMonoidHom) A.le_centralizer).trans hCt
  have hAtA : conjugate A t≤A :=
    (le_inf ((conjugate_le_of_normalizes hAR t (hTR ht)).trans hRK) hAtC).trans hKC.le
  have hcc : Nat.card (conjugate A t)=Nat.card A :=
    card_map_of_injective (MulAut.conj t⁻¹).injective
  exact htN ((conjugate_eq_iff A t).mp (eq_of_le_of_card_ge hAtA (by rw [hcc])))

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
