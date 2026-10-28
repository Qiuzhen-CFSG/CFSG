module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBOneSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport

/-!
# Critical selection for the original alternating-five pair

The genuine F.1.1 graph supplies a critical pair. A first-edge conjugator
places that pair at one of the two original base vertices, retaining its
actual vertex type and the whole reduced overlap. The intrinsic distance-one
source already proves both original core equalities and containments.

Every remaining source pair is therefore either a noncommuting distance-two
path or a commuting distance-three path with nonzero intersection
displacement. The original pair and its single normalized Borel are retained;
no reduced comparison or unproved classification input is assumed. The two
remaining source branches are exposed explicitly, rather than asserted to
imply containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction

variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- Internally select the literal original critical source path. Apart from
the already proved containment conclusion, only the two genuine remaining
source branches survive. The chosen alpha type is not prescribed. -/
theorem a5_pair_original_critical_selection
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃*
      alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G)) :
    ((∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧
      (∀ i, S ≤ ![K,R] i)) ∨
    ∃ (i : Bool) (w : Vertex (reducedFamily ![K,R] S)),
      IsCriticalPair (reducedFamily ![K,R] S)
        (base (reducedFamily ![K,R] S) i) w ∧
      (graph (reducedFamily ![K,R] S)).dist
        (base (reducedFamily ![K,R] S) (!i)) w + 1 =
          b (reducedFamily ![K,R] S) ∧
      ((b (reducedFamily ![K,R] S) = 2 ∧
          (graph (reducedFamily ![K,R] S)).Adj
            (base (reducedFamily ![K,R] S) (!i)) w ∧
          ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
            Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥) ∨
        (b (reducedFamily ![K,R] S) = 3 ∧
          ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
            Z (reducedFamily ![K,R] S) w⁆ = ⊥ ∧
          ⁅V (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) (!i)) 1 ⊓
              Q (reducedFamily ![K,R] S) w,
            V (reducedFamily ![K,R] S) w 1⁆ ≠ ⊥)) := by
  let F := reducedFamily ![K,R] S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨v, w, hc⟩ := reduced_criticalPair h
  have hpos : 0 < b F := source_b_positive (reduced_triple h)
  have hwv : w ≠ v := by
    intro he
    have hd : (graph F).dist v w = b F := hc.1
    rw [he, SimpleGraph.dist_self] at hd
    omega
  obtain ⟨m, hvm, hd⟩ := exists_predecessor F (reduced_triple h).generate w v hwv
  rw [SimpleGraph.dist_comm (u := w) (v := m),
    SimpleGraph.dist_comm (u := w) (v := v), hc.1] at hd
  obtain ⟨g, hv, hm⟩ := incident_common_translate F hvm.2
  have htype : m.type = !v.type := Bool.eq_not_of_ne hvm.1.symm
  rw [htype] at hm
  have hv₀ : g⁻¹ • v = base F v.type := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hv.symm
  have hm₀ : g⁻¹ • m = base F (!v.type) := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hm.symm
  have hc₀ := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  rw [hv₀] at hc₀
  have hd₀ : (graph F).dist (base F (!v.type)) (g⁻¹ • w) + 1 = b F := by
    rw [← hm₀, Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  have he₀ : (graph F).Adj (base F v.type) (base F (!v.type)) :=
    ⟨by change v.type ≠ !v.type; cases v.type <;> decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩
  by_cases hcomm : ⁅Z F (base F v.type), Z F (g⁻¹ • w)⁆ = ⊥
  · obtain ⟨hb, hdisp⟩ := a5_pair_commuting_critical_remaining h a hc₀ he₀ hd₀ hcomm
    exact .inr ⟨v.type, g⁻¹ • w, hc₀, hd₀, .inr ⟨hb, hcomm, hdisp⟩⟩
  · rcases reduced_intrinsic_noncommuting_bound h hc₀ hcomm with hb | hb
    · exact .inl (a5_pair_core_and_containment_of_critical_bOne h a hnorm hc₀ hcomm hb)
    · have hbF : b F = 2 := hb
      have hew : (graph F).Adj (base F (!v.type)) (g⁻¹ • w) :=
        SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
      exact .inr ⟨v.type, g⁻¹ • w, hc₀, hd₀, .inl ⟨hb, hew, hcomm⟩⟩

end CFSG.Quasithin.ChapterF.Source
