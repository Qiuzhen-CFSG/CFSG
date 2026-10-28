module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension

/-!
# Residual and span deductions before the temporary replacement

The genuine product `G_E = Y_E T_E C_G(E)` makes the conjugates of
`P_c = O₂(M_c) ∩ G_E` equal to its `Y_E`-conjugates. If the separate local
action calculation gives `Y_E = [Y_E,P_c]`, this closure is `Y_E P_c`.
Residual perfection of `Y_E` and the two-group quotient identify its
two-residual and prove relative normality in the original `G_E`.

Normality then propagates `V = [V,Y_E]` to `V_E`. The source product and
the abelianness from 15.3.50 also identify its centralizer span and place it
in the original two-core. The commutator identity for `P_c` is an explicit
remaining prerequisite; these deductions do not prove that action calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed p.1153, PDF p.1170, first two paragraphs.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G]

/-- The two-core containment in the fixed Sylow subgroup puts `P_c` in `T_E`. -/
theorem linePc_le_lineT (Mc T E : Subgroup G)
    (hcore : twoCoreAmbient Mc ≤ T) : linePc Mc E ≤ lineT T E :=
  inf_le_inf_right _ hcore

/-- The intersection defining `P_c` is invariant under `M_c ∩ G_E`. -/
theorem linePc_normalizer (Mc E : Subgroup G) :
    Mc ⊓ lineNormalizer E ≤ normalizer (linePc Mc E : Set G) := by
  have hn : ((twoCoreAmbient Mc).subgroupOf Mc).Normal := by
    change ((pCore 2 Mc).map Mc.subtype |>.comap Mc.subtype).Normal
    rw [comap_map_eq_self_of_injective Mc.subtype_injective]
    infer_instance
  have hMc := (normal_subgroupOf_iff_le_normalizer
    (show twoCoreAmbient Mc ≤ Mc from map_subtype_le _)).mp hn
  exact (le_inf (inf_le_left.trans hMc)
    (inf_le_right.trans (lineNormalizer E).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The product in 15.3.66(6) reduces the conjugates of `P_c` to its `Y_E`-conjugates. -/
theorem linePc_span_eq (Mc Y T E : Subgroup G)
    (hTMc : T ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G)) :
    conjugateSpanBy (linePc Mc E) (lineNormalizer E) =
      conjugateSpanBy (linePc Mc E) (lineY Y E) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨g, hg, p, hp, rfl⟩
    change g ∈ (lineNormalizer E : Set G) at hg
    rw [hprod] at hg
    obtain ⟨a, ⟨y, hy, t, ht, rfl⟩, c, hc, rfl⟩ := hg
    have htc : t * c ∈ Mc ⊓ lineNormalizer E :=
      ⟨Mc.mul_mem (hTMc ht.1) (hCMc hc),
        (lineNormalizer E).mul_mem ht.2 (Subgroup.centralizer_le_normalizer _ hc)⟩
    have hp' : (t * c) * p * (t * c)⁻¹ ∈ linePc Mc E :=
      ((linePc_normalizer Mc E htc) p).mp hp
    apply Subgroup.subset_closure
    refine ⟨y, hy, (t * c) * p * (t * c)⁻¹, hp', ?_⟩
    group
  · exact conjugateSpanBy_mono le_rfl ((lineY_le Y E).trans inf_le_right)

/-- The nontrivial-action calculation makes the normal closure equal to `Y_E P_c`. -/
theorem linePc_span_eq_join (Mc Y T E : Subgroup G)
    (hTMc : T ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G))
    (hcomm : lineY Y E = ⁅lineY Y E, linePc Mc E⁆) :
    conjugateSpanBy (linePc Mc E) (lineNormalizer E) = lineY Y E ⊔ linePc Mc E := by
  rw [linePc_span_eq Mc Y T E hTMc hCMc hprod]
  apply le_antisymm
  · exact conjugateSpanBy_le le_sup_right
      (le_sup_left.trans (lineY Y E ⊔ linePc Mc E).le_normalizer)
  · refine sup_le ?_ (le_conjugateSpanBy _ _)
    calc
      lineY Y E = ⁅lineY Y E, linePc Mc E⁆ := hcomm
      _ ≤ ⁅lineY Y E, conjugateSpanBy (linePc Mc E) (lineY Y E)⁆ :=
        commutator_mono le_rfl (le_conjugateSpanBy _ _)
      _ ≤ conjugateSpanBy (linePc Mc E) (lineY Y E) :=
        le_normalizer_iff_commutator_le_right.mp (le_normalizer_conjugateSpanBy _ _)

/-- Once the action calculation supplies the commutator identity, the two-residual of the original normal closure is exactly `Y_E`. -/
theorem lineY_eq_residual_span [Finite G] (Mc Y T E : Subgroup G)
    (hTMc : T ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hcore : twoCoreAmbient Mc ≤ T) (hTY : T ≤ normalizer (Y : Set G))
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G))
    (hcomm : lineY Y E = ⁅lineY Y E, linePc Mc E⁆) :
    lineY Y E = twoResidualAmbient (conjugateSpanBy (linePc Mc E) (lineNormalizer E)) := by
  rw [linePc_span_eq_join Mc Y T E hTMc hCMc hprod hcomm]
  exact (SectionsFiveToSeven.twoResidualIn_sup_twoGroup_eq
    (Y ⊓ lineNormalizer E) (linePc Mc E)
    ((isPGroup_pCoreIn 2 Mc).to_le inf_le_left)
    ((linePc_le_lineT Mc T E hcore).trans (lineT_le_normalizer_lineY Y T E hTY))).symm

/-- The residual identification proves normality in the original `G_E`. -/
theorem lineY_normal_of_commutator [Finite G] (Mc Y T E : Subgroup G)
    (hTMc : T ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hcore : twoCoreAmbient Mc ≤ T) (hTY : T ≤ normalizer (Y : Set G))
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G))
    (hcomm : lineY Y E = ⁅lineY Y E, linePc Mc E⁆) :
    ((lineY Y E).subgroupOf (lineNormalizer E)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mpr
  rw [lineY_eq_residual_span Mc Y T E hTMc hCMc hcore hTY hprod hcomm]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image _ (MulAut.conj g).toMonoidHom _
    (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ _ hg))

/-- Relative normality of `Y_E` propagates `V = [V,Y_E]` to every conjugate generator. -/
theorem lineV_eq_commutator (V Y E : Subgroup G)
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hV : V = ⁅V, lineY Y E⁆) : lineV V E = ⁅lineV V E, lineY Y E⁆ := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨g, hg, v, hv, rfl⟩
    have hmap := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom) hV
    have hyMap : (lineY Y E).map (MulAut.conj g).toMonoidHom = lineY Y E :=
      mem_normalizer_iff_map_conj_eq.mp (hY hg)
    rw [map_commutator, hyMap] at hmap
    have hconj : V.map (MulAut.conj g).toMonoidHom ≤ lineV V E := by
      rintro _ ⟨w, hw, rfl⟩
      exact Subgroup.subset_closure ⟨g, hg, w, hw, rfl⟩
    exact (commutator_mono hconj le_rfl) (hmap ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
  · exact le_normalizer_iff_commutator_le_left.mp
      (((lineY_le Y E).trans inf_le_right).trans (le_normalizer_conjugateSpanBy V _))

/-- The source product and 15.3.50 give the centralizer span, its elementary abelianness, and its containment in `Q_E`. -/
theorem lineV_span_and_elementary (M Mc Y T V E : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V Mc)]
    (hEV : E ≤ V) (hMV : M ≤ normalizer (V : Set G))
    (hYM : Y ≤ M) (hTM : T ≤ M) (hCMc : lineC E ≤ Mc)
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G)) :
    lineV V E = conjugateSpanBy V (lineC E) ∧
      lineV V E ≤ conjugateSpanBy V Mc ∧
      IsElementaryAbelian 2 (lineV V E) ∧ lineV V E ≤ lineQ E := by
  have hAM : lineY Y E ⊔ lineT T E ≤ M :=
    sup_le ((lineY_le Y E).trans (inf_le_left.trans hYM)) (inf_le_left.trans hTM)
  have hfactor : ∀ g ∈ lineNormalizer E, ∃ a ∈ lineY Y E ⊔ lineT T E,
      ∃ c ∈ lineC E, g = a * c := by
    intro g hg
    change g ∈ (lineNormalizer E : Set G) at hg
    rw [hprod] at hg
    obtain ⟨a, ⟨y, hy, t, ht, rfl⟩, c, hc, he⟩ := hg
    exact ⟨y * t, mul_mem (mem_sup_left hy) (mem_sup_right ht), c, hc, he.symm⟩
  let : IsMulCommutative (lineV V E) :=
    lineV_abelian_of_factorization V E M Mc _ hMV hAM hCMc hfactor
  exact ⟨lineV_eq_centralizerSpan_of_factorization V E _ (hAM.trans hMV) hfactor,
    lineV_le_localSpan_of_factorization V E M Mc _ hMV hAM hCMc hfactor,
    lineV_elementary_of_abelian V E, lineV_le_lineQ_of_abelian V E hEV⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
