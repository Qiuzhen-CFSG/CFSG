module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneApplication
public import Theory.GroupTheory.TwoElementaryFactorNormalizer
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The A₅ plane-normalization step

A conjugate pair containing V₂ has seed intersection of order at least
four. If the seeds commute, the original seed-centralizer equality makes
the whole modules commute. Otherwise the seeds are the two elementary
subgroups of index two in their join. The conjugate module preserves
that join and its own seed, so it preserves the other seed as well.
The proved global seed-normalizer control then normalizes V. This is the
plane-normalization conclusion of13.5.11 required by13.5.13.
Source: Aschbacher–Smith13.5.11–13, printed pp.918–919.
-/
public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem index_two_of_shared_four (A B E : Subgroup G)
    [IsElementaryAbelian 2 A] (hEB : E ≤ B) (hEA : E ≤ A)
    (hE : Nat.card E = 4) (hB : Nat.card B = 8)
    (hn : ⁅A,B⁆ ≠ ⊥) : A.relIndex B = 2 := by
  have hc := (E.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv,hE,hB] at hc
  have hi : E.relIndex B = 2 := by change 4 * E.relIndex B = 8 at hc; omega
  have hd : A.relIndex B ∣ 2 := hi ▸ relIndex_dvd_of_le_left B hEA
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
  · have hBA := relIndex_eq_one.mp he
    exact (hn (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hBA.trans (le_centralizer A))))).elim
  · exact he

private theorem preserves_join_of_cross_commutator (P A B : Subgroup G)
    (hPB : P ≤ normalizer (B : Set G)) (hc : ⁅P,A⁆ ≤ B) :
    P ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup]
    apply sup_le
    · rintro y ⟨a,ha,rfl⟩
      have hm : ⁅g,a⁆ * a ∈ A ⊔ B :=
        (A ⊔ B).mul_mem (mem_sup_right (hc (commutator_mem_commutator hg ha))) (mem_sup_left ha)
      change g * a * g⁻¹ ∈ A ⊔ B
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
    · rw [mem_normalizer_iff_map_conj_eq.mp (hPB hg)]
      exact le_sup_right
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

/-- The original conjugate containing the source plane normalizes V. -/
theorem source_plane_normalizes {g : G} (hg : g ∈ H)
    (hplane : V₂ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let f := (MulAut.conj g).toMonoidHom
  let A := V₃
  let B := V₃.map f
  let P := V.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le d.third_le
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map f
  have hAcore : A = V ⊓ D.QH :=
    (LocalGeometry.seed_eq_intersection_core hf d.third_index hU).symm
  have hQconj : D.QH.map f = D.QH :=
    mem_normalizer_iff_map_conj_eq.mp (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH hg)
  have hBcore : B = P ⊓ D.QH := by
    change A.map f = P ⊓ D.QH
    rw [hAcore,map_inf _ _ _ (MulAut.conj g).injective,hQconj]
  have hAQ : A ≤ D.QH := hAcore.le.trans inf_le_right
  have hBQ : B ≤ D.QH := hBcore.le.trans inf_le_right
  have hBP : B ≤ P := map_mono d.third_le
  have hPH : P ≤ H := by
    have hh := map_mono (f := f) hf.V_le_H
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg))
  have hAB : ⁅A,B⁆ ≤ V₁ :=
    (commutator_mono (le_conjugateSpanBy _ _) hBQ).trans hf.commutator_UH_QH_le_point
  have hZB : V₁ ≤ B := by
    have hz : V₁.map f = V₁ := mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (hf.H_centralizes hg))
    exact hz ▸ map_mono d.third_strict.le
  have hBNV : B ≤ normalizer (V : Set G) := hBQ.trans (hf.QH_le_T.trans hf.T_normalizes_V)
  by_cases hab : ⁅A,B⁆ = ⊥
  · have hBC : B ≤ centralizer (A : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hab)
    have hBV : B ≤ centralizer (V : Set G) := by
      intro x hx
      exact (centralizer_third d.flag V₃ d.third_le d.third_card d.third_invariant).le
        ⟨hBNV hx,hBC hx⟩
    have hVB : V ≤ normalizer (B : Set G) :=
      (le_centralizer_iff.mp hBV).trans (Subgroup.centralizer_le_normalizer _)
    have hVN : V ≤ normalizer (P : Set G) := by
      have hn := map_mono (f := f) (d.seed_normalizer hA312)
      rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq] at hn
      exact hVB.trans hn
    -- The same centralizer equality on the conjugate module gives actual commutation.
    have hc := map_mono (f := f) (show normalizer (V : Set G) ⊓ centralizer (A : Set G) ≤
        centralizer (V : Set G) from (centralizer_third d.flag V₃ d.third_le d.third_card d.third_invariant).le)
    rw [map_inf _ _ _ (MulAut.conj g).injective,map_equiv_normalizer_eq,
      map_centralizer_equiv,map_centralizer_equiv] at hc
    change normalizer (P : Set G) ⊓ centralizer (B : Set G) ≤ centralizer (P : Set G) at hc
    exact ((le_centralizer_iff.mp ((le_inf hVN (le_centralizer_iff.mp hBV)).trans hc))).trans
      (Subgroup.centralizer_le_normalizer _)
  · have hANB : A ≤ normalizer (B : Set G) :=
      le_normalizer_iff_commutator_le_right.mpr (hAB.trans hZB)
    have hBNA : B ≤ normalizer (A : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr (hAB.trans d.third_strict.le)
    have hEA : V₂ ≤ A := d.plane_le_third
    have hEB : V₂ ≤ B := (le_inf (hplane.trans inf_le_right) (hEA.trans hAQ)).trans hBcore.ge
    have hBcard : Nat.card B = 8 := (card_map_of_injective (MulAut.conj g).injective).trans d.third_card
    have hiA : A.relIndex (A ⊔ B) = 2 := by
      rw [sup_comm,relIndex_sup_of_normalizes B A hANB]
      exact index_two_of_shared_four A B V₂ hEB hEA d.flag.two_card hBcard hab
    have hiB : B.relIndex (A ⊔ B) = 2 := by
      rw [relIndex_sup_of_normalizes A B hBNA]
      apply index_two_of_shared_four B A V₂ hEA hEB d.flag.two_card d.third_card
      rwa [commutator_comm]
    have hPJ : P ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
      apply preserves_join_of_cross_commutator P A B
      · exact ((le_centralizer P).trans (centralizer_le hBP)).trans (Subgroup.centralizer_le_normalizer _)
      · have hQV : ⁅V,D.QH⁆ ≤ V :=
          le_normalizer_iff_commutator_le_left.mp (hf.QH_le_T.trans hf.T_normalizes_V)
        have hQP : ⁅P,D.QH⁆ ≤ P := by
          have hh := map_mono (f := f) hQV
          rwa [map_commutator,hQconj] at hh
        have hPQ : ⁅P,D.QH⁆ ≤ D.QH :=
          le_normalizer_iff_commutator_le_right.mp
            (hPH.trans (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)))
        exact (commutator_mono le_rfl hAQ).trans ((le_inf hQP hPQ).trans hBcore.ge)
    have hPBN : P ≤ normalizer (B : Set G) :=
      ((le_centralizer P).trans (centralizer_le hBP)).trans (Subgroup.centralizer_le_normalizer _)
    have hnJ : ¬ IsMulCommutative (B ⊔ A : Subgroup G) := by
      intro hc
      let := hc
      apply hab
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (le_sup_right.trans ((le_centralizer (B ⊔ A)).trans (centralizer_le (show B ≤ B ⊔ A from le_sup_left))))
    have hPA := (le_inf (by simpa only [sup_comm] using hPJ) hPBN).trans
      (normalizes_second_elementary_factor B A inferInstance inferInstance
        (by simpa only [sup_comm] using hiB) (by simpa only [sup_comm] using hiA) hnJ)
    exact hPA.trans (d.seed_normalizer hA312)

end CFSG.Quasithin.Chapter13.Section05.A5Source
