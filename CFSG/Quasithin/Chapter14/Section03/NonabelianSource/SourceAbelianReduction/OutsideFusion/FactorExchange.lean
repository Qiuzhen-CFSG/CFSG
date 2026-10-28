module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugacySolvable
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorNormalizerSylow

/-!
# Exchange by the specified outside actor

The two maximal elementary factors of the original parabolic core are exchanged
by every element of T outside RQ. The factor normalizer calculation applies to
each of the original factors, so this concerns the specified actor, rather than
an existentially chosen conjugator. An involution of R fixed by that actor lies
in both factors and hence in the original seed.

Source: Aschbacher--Smith 14.3.21(2), printed p.998, using 14.3.18--19.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

private theorem conjugate_factor_eq_of_not_normalizing
    (R A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ R) (hc : Nat.card A = Nat.card B)
    (hmax : ∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ R → E ≤ A ∨ E ≤ B)
    (t : G) (htR : t ∈ normalizer (R : Set G))
    (htA : t ∉ normalizer (A : Set G)) : conjugate A t = B := by
  let : IsElementaryAbelian 2 (conjugate A t) :=
    IsElementaryAbelian.map (MulAut.conj t⁻¹).toMonoidHom
  have hct : conjugate A t ≤ R := conjugate_le_of_normalizes hAR t htR
  have hcc : Nat.card (conjugate A t) = Nat.card A :=
    card_map_of_injective (MulAut.conj t⁻¹).injective
  rcases hmax (conjugate A t) inferInstance hct with ha | hb
  · exact (htA ((conjugate_eq_iff A t).mp
      (eq_of_le_of_card_ge ha (by rw [hcc])))).elim
  · exact eq_of_le_of_card_ge hb (by rw [hcc,hc])

/-- The actual outside element exchanges the two original elementary factors.
Every square-one element of its centralizer in R lies in V. -/
theorem source_outside_factor_exchange_of_solvable
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
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (t : G) (htT : t ∈ (T : Subgroup G))
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    (T : Subgroup G) ≤ normalizer (R : Set G) ∧
    ∃ A B : Subgroup G,
      A ≤ R ∧ B ≤ R ∧ rankTwoSeed T M ≤ A ∧ rankTwoSeed T M ≤ B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = rankTwoSeed T M ∧ A ⊔ B = R ∧ Nat.card R = 64 ∧
      R ≤ normalizer (A : Set G) ∧ R ≤ normalizer (B : Set G) ∧
      conjugate A t = B ∧ conjugate B t = A ∧
      (∀ x ∈ R, x ^ 2 = 1 → Commute x t → x ∈ rankTwoSeed T M) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hjoin,hRc,hAN,hBN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  let := hEA
  let := hEB
  obtain ⟨hAU,hBU⟩ := elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB hEA hEB hmax
  have hTA := (factor_automizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hAU hAN).1
  have hTB := (factor_automizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    B hBR hVB hBc hBU hBN).1
  have htA : t ∉ normalizer (A : Set G) := fun hn => htout (hTA ▸ ⟨htT,hn⟩)
  have htB : t ∉ normalizer (B : Set G) := fun hn => htout (hTB ▸ ⟨htT,hn⟩)
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1 := by
    rw [← F.U.map_subtype_commutator]
    exact (map_mono (f := F.U.subtype) (commutator_le_frattini_of_isPGroup (p := 2))).trans hPhi.le
  have hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := fun u hu =>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u,hu⟩ : F.U))
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨_,_,_,_,hIG,hIN,_,_,_,_,_,_,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hab := conjugate_factor_eq_of_not_normalizing R A B hAR (hAc.trans hBc.symm)
    hmax t (hTR htT) htA
  have hba := conjugate_factor_eq_of_not_normalizing R B A hBR (hBc.trans hAc.symm)
    (fun E hE hER => (hmax E hE hER).symm) t (hTR htT) htB
  refine ⟨hTR,A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hjoin,hRc,
    (pCoreIn_le 2 _).trans (le_sup_left.trans hAN),
    (pCoreIn_le 2 _).trans (le_sup_left.trans hBN),hab,hba,?_⟩
  intro x hx hx2 hxt
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hfix : t⁻¹ * x * t = x := by rw [← hxt.inv_right.eq]; simp
  have hmap (D : Subgroup G) (hxD : x ∈ D) : x ∈ conjugate D t :=
    ⟨x,hxD,by change t⁻¹ * x * (t⁻¹)⁻¹ = x; simpa only [inv_inv] using hfix⟩
  apply hi.le
  rcases hmax (zpowers x) inferInstance (zpowers_le.mpr hx) with ha | hb
  · have hxA := ha (mem_zpowers x)
    exact ⟨hxA,hab ▸ hmap A hxA⟩
  · have hxB := hb (mem_zpowers x)
    exact ⟨hba ▸ hmap B hxB,hxB⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
