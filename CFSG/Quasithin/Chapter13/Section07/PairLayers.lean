module

public import CFSG.Quasithin.Chapter13.Section07.ChosenConjugator
public import CFSG.Quasithin.Chapter13.Section07.TranspositionImage
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# The original elementary intersection and central layer in 13.7.10

Disjoint source points give disjoint Frattini bounds, so the intersection
of V_H with its chosen conjugate is elementary abelian. The two seed
hyperplanes generate V, forcing that intersection into Q and H_C.
Both spans normalize the point plane V₁V₁ᵍ; the commutator bound from each
span then makes their intersection central modulo that plane.

The final consumer constructs the actual source conjugator. It takes only
F.9 applicability, the earlier abelian seed-span, and the contrary nonabelian
full span. The remaining S₃ quotient and E_H intersection equalities are
separate conclusions of the original source argument.
Source: Aschbacher–Smith, 13.7.10(3),(7), printed pp.941–942.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

omit d [Finite G] in
private theorem normalizes_join_of_commutator (A Z W : Subgroup G)
    (hAZ : A ≤ normalizer (Z : Set G)) (hc : ⁅A,W⁆ ≤ Z) :
    A ≤ normalizer ((Z ⊔ W : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have hm : (Z ⊔ W).map (MulAut.conj a).toMonoidHom ≤ Z ⊔ W := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨z,hz,rfl⟩
      exact mem_sup_left ((mem_normalizer_iff.mp (hAZ ha) z).mp hz)
    · rintro _ ⟨w,hw,rfl⟩
      have he : a*w*a⁻¹ = ⁅a,w⁆ * w := by simp only [commutatorElement_def]; group
      change a*w*a⁻¹ ∈ Z ⊔ W
      rw [he]
      exact mul_mem (mem_sup_left (hc (commutator_mem_commutator ha hw))) (mem_sup_right hw)
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

omit d in
/-- The two literal point subgroups are disjoint for the source choice. -/
theorem chosen_points_disjoint
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (g : G) (hout : ¬ conjugate V₁ g ≤ Section08.Source.UH H V₃) :
    Disjoint V₁ (conjugate V₁ g) := by
  apply disjoint_iff.mpr
  apply inf_eq_bot_of_card_two_of_ne _ _ h.point_card
    ((card_map_of_injective (MulAut.conj g⁻¹).injective).trans h.point_card)
  intro he
  change V₁ = conjugate V₁ g at he
  apply hout
  rw [← he]
  exact h.point_lt.le.trans (le_conjugateSpanBy V₃ H)

/-- The original intersection Z_I is elementary and lies in Q∩H_C. -/
theorem chosen_intersection_elementary_core
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃) :
    IsElementaryAbelian 2 (Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G) : Subgroup G) ∧
    Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G) ≤
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ⊓
        (H ⊓ centralizer (Section08.Source.UH H V₃ : Set G)) := by
  have hVHc : Section08.Source.VH H V ≤ centralizer (V₃ : Set G) :=
    (VH_centralizes_UH d h hU).trans (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V₃ H)))
  have hVHgC : conjugate (Section08.Source.VH H V) (g : G) ≤
      centralizer (conjugate V₃ (g : G) : Set G) :=
    (map_mono hVHc).trans (map_centralizer_le_centralizer_image _ _)
  have hZC : Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G) ≤
      centralizer (V : Set G) := by
    apply le_centralizer_iff.mp
    apply hspan.trans
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_left.trans hVHc)
    · exact (map_mono h.point_lt.le).trans (le_centralizer_iff.mp (inf_le_right.trans hVHgC))
  have hp : IsPGroup 2 (Section08.Source.VH H V) :=
    (pCore_isPGroup.map H.subtype).to_le (VH_le_core d h hU)
  refine ⟨conjugate_intersection_elementary hp (frattini_VH_le_point d h hU) (g : G)⁻¹
    (chosen_points_disjoint h (g : G) hout), ?_⟩
  refine le_inf ?_ (inf_le_left.trans (VH_centralizes_UH d h hU))
  have hsc : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := h.sylow_centralizer
  rw [← hsc]
  exact le_inf (inf_le_left.trans ((VH_le_core d h hU).trans h.QH_le_T)) hZC

/-- The same generated pair centralizes its intersection modulo V₁V₁ᵍ. -/
theorem chosen_intersection_central_layer
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1) :
    ⁅Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G),
      Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g : G)⁆ ≤
      V₁ ⊔ conjugate V₁ (g : G) := by
  let A := Section08.Source.VH H V
  let Z := V₁ ⊔ conjugate V₁ (g : G)
  have hV1V : V₁ ≤ V := h.point_lt.le.trans h.plus_le
  have hVV : conjugate V (g : G) = V := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V : Set G)).inv_mem (d.normalizes_V g.property))
  have hW : conjugate V₁ (g : G) ≤ V := (map_mono hV1V).trans hVV.le
  have hAZ : A ≤ normalizer (Z : Set G) := normalizes_join_of_commutator A V₁ _
    (h.VH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    (by rw [commutator_comm]; exact (commutator_mono hW le_rfl).trans (commutator_V_VH_le_point d h hU))
  have hZg : conjugate Z (g : G) = Z := by
    change (V₁ ⊔ conjugate V₁ (g : G)).map (MulAut.conj (g : G)⁻¹).toMonoidHom = Z
    rw [Subgroup.map_sup]
    change conjugate V₁ (g : G) ⊔ conjugate (conjugate V₁ (g : G)) (g : G) = Z
    have htwice : conjugate (conjugate V₁ (g : G)) (g : G) = V₁ :=
      h.conjugate_twice_eq_of_square (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
        (h.square_mem_local_of_core_quotient_square g hs)
    rw [htwice, sup_comm]
  have hAgZ : conjugate A (g : G) ≤ normalizer (Z : Set G) := by
    have hm := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hAZ
    rw [map_normalizer_eq_of_bijective Z (MulAut.conj (g : G)⁻¹).bijective] at hm
    exact hZg ▸ hm
  have hAA : ⁅A,A⁆ ≤ Z := (commutator_VH_le_point d h hU).trans le_sup_left
  have hBB : ⁅conjugate A (g : G),conjugate A (g : G)⁆ ≤ Z := by
    have hm := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) (commutator_VH_le_point d h hU)
    rw [map_commutator] at hm
    exact hm.trans le_sup_right
  exact intersection_commutator_sup_le hAA hBB (sup_le hAZ hAgZ)

/-- The literal source pair, with its witness and all layer premises constructed. -/
theorem exists_source_pair_layers
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      IsElementaryAbelian 2 (Section08.Source.VH H V ⊓
        conjugate (Section08.Source.VH H V) (g : G) : Subgroup G) ∧
      (Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G) ≤
        (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ⊓
          (H ⊓ centralizer (Section08.Source.UH H V₃ : Set G))) ∧
      ⁅Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G),
        Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g : G)⁆ ≤
        V₁ ⊔ conjugate V₁ (g : G) := by
  obtain ⟨g, hs, hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g : G) hspan hU hV
  obtain ⟨hel,hcore⟩ := chosen_intersection_elementary_core d h hU
    (inclusion le_sup_left g) hspan hout
  exact ⟨g,hs,hel,hcore,chosen_intersection_central_layer d h hU (inclusion le_sup_left g) hs⟩

end CFSG.Quasithin.Chapter13.Section07
