module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCriticalSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoG2Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoOrientation

/-!
# Native reduced comparisons from the original A5 pair

The genuine original F.1.1 graph supplies its critical pair and first edge.
The original A5 markings exclude the commuting branch. The intrinsic
noncommuting bound and the proved source recognition then give a native
linear or symplectic comparison, or the field-four G2 comparison in one
of the two original orientations.

No normalized Borel, reduced catalogue, model marking or source selector is
assumed. This endpoint retains the full reduced Borel and both actual
inclusion maps. Original restoration and application to a particular
outside pair remain separate steps.
Source: DGS Theorem A and Chapters7--15; Aschbacher--Smith F.1.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- Actual native comparisons from unchanged F.1.1 and original A5 marks,
without any Borel normalization or catalogue premise. -/
theorem a5_pair_native_comparisons_from_source
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃*
      alternatingGroup (Fin 5))) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((∃ point : Bool,
          Nonempty (Iso (reducedAmalgam ![K,R] S) (LinearNative.amalgam F point))) ∨
       (∃ point : Bool,
          Nonempty (Iso (reducedAmalgam ![K,R] S) (SymplecticNative.amalgam F point))))) ∨
    (∃ short : Bool,
      Nonempty (Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam (GaloisField 2 2) short))) ∨
    (∃ short : Bool,
      Nonempty (Iso (reducedAmalgam ![R,K] S) (G2Native.amalgam (GaloisField 2 2) short))) := by
  let F := reducedFamily ![K,R] S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨v,w,hc⟩ := reduced_criticalPair h
  have hne : ⁅Z F v,Z F w⁆ ≠ ⊥ := a5_pair_critical_not_commuting h a hc
  rcases reduced_intrinsic_noncommuting_bound h hc hne with hb | hb
  · exact .inl (small_comparison_of_critical_bOne h hc hne hb)
  · have hbF : b F = 2 := hb
    have hwv : w ≠ v := by
      intro he
      have hd : (graph F).dist v w = b F := hc.1
      rw [he,SimpleGraph.dist_self] at hd
      omega
    obtain ⟨m,hvm,hd⟩ := exists_predecessor F (reduced_triple h).generate w v hwv
    rw [SimpleGraph.dist_comm (u := w) (v := m),
      SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hd
    obtain ⟨g,hv,hm⟩ := incident_common_translate F hvm.2
    have htype : m.type = !v.type := Bool.eq_not_of_ne hvm.1.symm
    rw [htype] at hm
    have hv₀ : g⁻¹ • v = base F v.type := by
      simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hv.symm
    have hm₀ : g⁻¹ • m = base F (!v.type) := by
      simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hm.symm
    have hc₀ := CommutingNontrivial.criticalPair_translate F hc g⁻¹
    rw [hv₀] at hc₀
    have hne₀ : ⁅Z F (base F v.type),Z F (g⁻¹ • w)⁆ ≠ ⊥ :=
      a5_pair_critical_not_commuting h a hc₀
    have hd₀ : (graph F).dist (base F (!v.type)) (g⁻¹ • w) + 1 = b F := by
      rw [←hm₀,Subgroup.CosetGeometry.RankTwo.dist_smul]
      exact hd
    have hβw : (graph F).Adj (base F (!v.type)) (g⁻¹ • w) :=
      SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
    cases hvtype : v.type
    · rw [hvtype] at hc₀ hne₀ hβw
      exact .inr (.inl (h.a5_bTwo_reduced_g2_comparison a hc₀ hne₀ hb hβw))
    · rw [hvtype] at hc₀ hne₀ hβw
      obtain ⟨w',hc',hne',hβw'⟩ :=
        CriticalReorientation.original_noncommuting_critical_swap K R S hc₀ hne₀ hβw
      have a' : ∀ i, Nonempty ((![R,K] i ⧸ pCore 2 (![R,K] i)) ≃*
          alternatingGroup (Fin 5)) := by
        intro i
        fin_cases i
        · exact a 1
        · exact a 0
      have hb' : b (reducedFamily ![R,K] S) = 2 := (pair_b_swap K R S).trans hb
      exact .inr (.inr (h.swap.a5_bTwo_reduced_g2_comparison a' hc' hne' hb' hβw'))

end CFSG.Quasithin.ChapterF.Source
