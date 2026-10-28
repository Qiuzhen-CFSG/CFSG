module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood
public import Theory.GroupTheory.Commutator.CentralizingDisplacement

/-!
# Normality and the centralizer obstruction for the nontrivial displacement

Local generation and central displacement make each neighbor commutator normal
in L at the final vertex. Local transitivity puts it in every neighboring
center. The resulting full radius-one commutator centralizes each conjugate
core span. Restriction of an actual Sylow embedding then transfers the 6.5
core-span obstruction to the centralizer of this commutator.

Source: DGS, *Groups and Graphs* (1985), proof of 8.1(i), p.133.
Normality is relative to L at the final vertex, never to the neighbor group.
Local generation and displacement are explicit inputs, still to be discharged
from 5.1 and 5.9 in the Chapter 8 assembly.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Maximality of a Sylow image restricts to every intermediate subgroup. -/
private theorem sylow_image_restricts {p : ℕ} {Q W C : Subgroup G}
    (hQW : Q ≤ W) (hWC : W ≤ C)
    (hS : ∃ T : Sylow p C, (T : Subgroup C).map C.subtype = Q) :
    ∃ T : Sylow p W, (T : Subgroup W).map W.subtype = Q := by
  obtain ⟨T, hT⟩ := hS
  have hTW : (T : Subgroup C) ≤ W.subgroupOf C := by
    intro x hx
    exact hQW (hT ▸ mem_map_of_mem C.subtype hx)
  let f : W →* C := inclusion hWC
  have hTrange : (T : Subgroup C) ≤ f.range := by
    intro x hx
    exact ⟨⟨x, hTW hx⟩, rfl⟩
  refine ⟨T.comapOfInjective f (inclusion_injective _) hTrange, ?_⟩
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hT ▸ mem_map_of_mem C.subtype hy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hT.symm ▸ hx
    exact ⟨⟨y, hQW (hT ▸ mem_map_of_mem C.subtype hy)⟩, hy, rfl⟩

/-- Normality and the central core-span conclusion in the proof of 8.1(i).
The local Sylows and their actual embeddings are retained. Local generation
(8.1(g), from 5.1) and displacement modulo Q (from 5.9) are explicit inputs
here; neither the normality conclusion nor containment in a center is assumed. -/
theorem radius_one_commutator_normality [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hQU : ∀ v, Q F v ≤ U F v)
    (hSyl : ∀ w, ∃ T : Sylow 2 (U F w),
      (T : Subgroup (U F w)).map (U F w).subtype = Q F w)
    (beta a' : Vertex F) (hd : (graph F).dist beta a' + 1 ≤ b F) (hb : 3 ≤ b F)
    (L : Subgroup G) (hQL : Q F a' ≤ L)
    (htrans : ∀ x y : (graph F).neighborSet a', ∃ g ∈ L, g • x.val = y.val)
    (hlocal : ∀ w : (graph F).neighborSet a',
      ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ →
      ∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G),
        V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G)).map
          (stabilizer F a' ⊓ stabilizer F w.val).subtype = L ∧
        ⁅(T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G)).map
          (stabilizer F a' ⊓ stabilizer F w.val).subtype, V F beta 1 ⊓ Q F a'⁆ ≤ Q F w.val) :
    ((⁅V F beta 1 ⊓ Q F a', V F a' 1⁆).subgroupOf L).Normal ∧
      (∀ w : (graph F).neighborSet a', ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≤ Z F w.val) ∧
      (∀ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≤ conjugateSpanBy (Q F w.val) L ⊓
          centralizer (conjugateSpanBy (Q F w.val) L : Set G)) ∧
      ∀ w : (graph F).neighborSet a', Q F w.val ≤ L →
        (¬ ∃ T : Sylow 2 (conjugateSpanBy (Q F w.val) L),
          (T : Subgroup (conjugateSpanBy (Q F w.val) L)).map
            (conjugateSpanBy (Q F w.val) L).subtype = Q F w.val) →
        ¬ ∃ T : Sylow 2 ↥(L ⊓ centralizer ((⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ : Subgroup G) : Set G) : Subgroup G),
          (T : Subgroup ↥(L ⊓ centralizer ((⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ : Subgroup G) : Set G) : Subgroup G)).map
            (L ⊓ centralizer ((⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ : Subgroup G) : Set G)).subtype = Q F w.val := by
  let := V_isMulCommutative_of_two_mul_lt_b F hgen hZ hSyl beta 1 (by omega)
  have hVL : V F a' 1 ≤ L :=
    (V_le_Q_of_dist_add_lt_b F hgen hZ a' a' 1 (by simp; omega) (hSyl a')).trans hQL
  have hnorm := (radius_one_mutual_normalization F hgen beta a' hd).2
  have hAZ (w : (graph F).neighborSet a') :
      V F beta 1 ⊓ Q F a' ≤ normalizer (Z F w.val : Set G) :=
    (inf_le_right.trans ((hQU a').trans
      ((ballKernel_one_le_edge F w.property).trans inf_le_right))).trans
        (stabilizer_normalizes_Z F w.val)
  have hc := radius_one_commutator_normalized_and_central_in_core_spans
    L (V F beta 1) (V F beta 1 ⊓ Q F a') (Z F a')
    (fun w : (graph F).neighborSet a' => Z F w.val)
    (fun w : (graph F).neighborSet a' => Q F w.val)
    inf_le_left (fun w => (Z_neighbor_le_V F w.property).trans hVL)
    (fun w => (Z_neighbor_le_V F w.property).trans hnorm) hAZ
    (fun w hw => by
      obtain ⟨T, hTgen, hTQ⟩ := hlocal w hw
      refine ⟨(T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G)).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype, hTgen, ?_, ?_⟩
      · exact ((map_subtype_le _).trans inf_le_right).trans (stabilizer_normalizes_Z F w.val)
      · exact hTQ.trans (le_centralizer_iff.mp (Z_centralizes_Q F w.val (hZ w.val))))
    (fun x y => by
      obtain ⟨g, hg, hxy⟩ := htrans x y
      exact ⟨g, hg, (Z_translate F g x.val).symm.trans (congrArg (Z F) hxy)⟩)
    ((Z_le_V F a' 1).trans hVL)
    ((Z_centralizes_Q F a' (hZ a')).trans (centralizer_le inf_le_right))
    (fun w => (hZ w.val).trans (map_subtype_le _))
    (fun w => Z_centralizes_Q F w.val (hZ w.val))
  rw [← V_one_eq_sup_neighbors] at hc
  have hHL : ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≤ L :=
    (le_normalizer_iff_commutator_le_right.mp
      ((inf_le_right.trans (Q_le_stabilizer F a')).trans
        (stabilizer_normalizes_V F a' 1))).trans hVL
  refine ⟨(normal_subgroupOf_iff_le_normalizer hHL).mpr hc.1,
    (fun w => hc.2.1.trans (iInf_le _ w)), hc.2.2, ?_⟩
  intro w hQw hobs hT
  apply hobs
  exact sylow_image_restricts (le_conjugateSpanBy (Q F w.val) L)
    (le_inf (conjugateSpanBy_le_self hQw)
      (le_centralizer_iff.mp ((hc.2.2 w).trans inf_le_right))) hT

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
