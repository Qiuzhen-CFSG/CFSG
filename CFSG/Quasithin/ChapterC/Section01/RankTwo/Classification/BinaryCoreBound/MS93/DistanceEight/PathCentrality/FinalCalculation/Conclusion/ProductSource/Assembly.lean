module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.SelectedBounds

/-!
# Saturating the selected product in MS93 (4.4)

The two selected commutators are nonzero and have trivial intersection,
by their proved containment in the separated source edges. Their join
therefore has order at least four. The literal terminal product contains
this join and has order at most four; they coincide and have order four.
This identifies the product with the printed backward edge, and places
it in U_alpha intersect Q_(alpha').

The source choices remain an explicit input pending their constructor.
The forward-edge application retains only the local natural-kernel
comparison, with the edge order discharged by the selected product and
actual edge transport. Neither this conditional application nor a
SelectedPair projection is claimed to construct the missing choices.
Final discharge stays with qt-c01-ms93-conclusion-selected-product.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), printed p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource

private theorem fill_four_group {G : Type*} [Group G] (A B K : Subgroup G)
    [Finite K] (hAK : A ≤ K) (hBK : B ≤ K) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hdis : A ⊓ B = ⊥) (hK : Nat.card K ≤ 4) :
    Nat.card K = 4 ∧ K = A ⊔ B := by
  let J := A ⊔ B
  have hJK : J ≤ K := sup_le hAK hBK
  let : Finite J := Finite.of_injective (inclusion hJK) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAK) (inclusion_injective _)
  have hAJ : A ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  have hpos : 1 < Nat.card A := (one_lt_card_iff_ne_bot _).mpr hA
  have hlt : Nat.card A < Nat.card J := by
    by_contra! h
    have heq : A = J := eq_of_le_of_card_ge hAJ h
    apply hB
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf (heq ▸ hBJ) le_rfl
  obtain ⟨k, hk⟩ := card_dvd_of_le hAJ
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  have hfour : 4 ≤ Nat.card J := by nlinarith
  have heq : J = K := eq_of_le_of_card_ge hJK (hK.trans hfour)
  refine ⟨?_, heq.symm⟩
  rw [heq] at hfour
  omega

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace SelectedPair
variable {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a} (p : SelectedPair e)
include p

/-- The source intersection clause separates the actual Ri subgroups. -/
theorem commutators_inf_eq_bot (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R) :
    selectedCommutator e p.left.delta ⊓ selectedCommutator e p.right.delta = ⊥ := by
  have hl := p.left.commutator_le_edge_inf_kernel common hb hlocal
  have hr := p.right.commutator_le_edge_inf_kernel common hb hlocal
  apply le_bot_iff.mp
  rw [← p.separated]
  exact le_inf
    (le_inf (inf_le_left.trans (hl.trans inf_le_left))
      (inf_le_right.trans (hr.trans inf_le_left)))
    (inf_le_left.trans (hl.trans inf_le_right))

/-- In particular the source's two Ri are genuinely distinct. -/
theorem commutators_ne (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    selectedCommutator e p.left.delta ≠ selectedCommutator e p.right.delta := by
  intro heq
  have h := p.commutators_inf_eq_bot common hb hlocal
  rw [← heq, inf_idem] at h
  exact p.left.commutator_ne_bot common hb sections h

/-- Two disjoint nonzero selected commutators fill the order-at-most-four
terminal product. This proves both saturation and its order. -/
theorem card_and_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    Nat.card (terminalProduct e) = 4 ∧
      terminalProduct e = selectedCommutator e p.left.delta ⊔
        selectedCommutator e p.right.delta := by
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hadj : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hU := (terminalProduct_le_backward_edge hb e).trans
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) _ _ hc hadj)
  let : Finite (U R (e.walk.getVert (geometry.b R))) :=
    Nat.finite_of_card_ne_zero (by rw [common.natural.card_at _ hc]; decide)
  let : Finite (terminalProduct e) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  exact fill_four_group _ _ _ p.left.commutator_le_product p.right.commutator_le_product
    (p.left.commutator_ne_bot common hb sections) (p.right.commutator_ne_bot common hb sections)
    (p.commutators_inf_eq_bot common hb hlocal) (terminalProduct_card_le_four common hb e)

/-- The order estimate, with only the actual source choices still explicit. -/
theorem terminalProduct_card (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    Nat.card (terminalProduct e) = 4 :=
  (p.card_and_product common hb hlocal sections).1

/-- The subgroup join just obtained is the source's literal setwise
product: both Ri lie in the same elementary abelian Z_alpha. -/
theorem terminalProduct_eq_mul (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    (↑(terminalProduct e) : Set (FreeAmalgam R)) =
      (↑(selectedCommutator e p.left.delta) : Set (FreeAmalgam R)) *
        (↑(selectedCommutator e p.right.delta) : Set (FreeAmalgam R)) := by
  have ha := ExtendedPath.center_color e
  have hbound (s : SelectedVertex e) : selectedCommutator e s.delta ≤ Z R a :=
    (s.commutator_le_chosen_edge common hb hlocal).trans
      ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (LocalCommutator.moduleFacts common) _ _ ha s.adjacent_center).trans (U_le_Z R _))
  let := Z_elementary_of_positive R geometry a ha (by
    rw [geometry.distance_constant a ha]
    change 0 < geometry.b R
    omega)
  have hZZ : Z R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  rw [(p.card_and_product common hb hlocal sections).2]
  exact coe_mul_of_left_le_normalizer_right _ _
    (((hbound p.left).trans (hZZ.trans (centralizer_le (hbound p.right)))).trans
      (Subgroup.centralizer_le_normalizer _))

/-- Exact application of the printed predecessor-edge identification. -/
theorem terminalProduct_eq_backward_edge (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    terminalProduct e = edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) :=
  terminalProduct_eq_backward_edge_of_card common hb e
    (p.terminalProduct_card common hb hlocal sections)

/-- The two incident-edge bounds place the entire saturated product in
the source natural intersection, without assuming that intersection identity. -/
theorem terminalProduct_le_natural_kernel (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    terminalProduct e ≤ U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R)) := by
  rw [(p.card_and_product common hb hlocal sections).2]
  have hbound (s : SelectedVertex e) : selectedCommutator e s.delta ≤
      U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R)) :=
    (s.commutator_le_edge_inf_kernel common hb hlocal).trans (inf_le_inf_right _
      (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (LocalCommutator.moduleFacts common) _ _ (ExtendedPath.center_color e)
        s.adjacent_center))
  exact sup_le (hbound p.left) (hbound p.right)

/-- The source local natural-kernel comparison suffices for the first edge.
Its order-four input is supplied here by actual edge transport. -/
theorem terminalProduct_eq_first_edge_of_kernel_comparison
    (common : CommonFacts R source geometry) (hb : 8 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    (hkernel : Nat.card (edgeCommutator R a (e.walk.getVert 5)) = 4 →
      U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R)) ≤
        edgeCommutator R a (e.walk.getVert 5)) :
    terminalProduct e = edgeCommutator R a (e.walk.getVert 5) := by
  have hb6 : 6 < geometry.b R := by omega
  have hcard := p.terminalProduct_card common hb6 hlocal sections
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hback : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hfirst : Adjacent R a (e.walk.getVert 5) := by
    simpa only [e.center_eq] using path_adjacent e 4 (by omega)
  have hE : Nat.card (edgeCommutator R a (e.walk.getVert 5)) = 4 := by
    apply edge_card_at_all hc (ExtendedPath.center_color e) hback hfirst
    rw [← terminalProduct_eq_backward_edge_of_card common hb6 e hcard]
    exact hcard
  let : Finite (edgeCommutator R a (e.walk.getVert 5)) :=
    Nat.finite_of_card_ne_zero (by rw [hE]; decide)
  exact eq_of_le_of_card_ge
    ((p.terminalProduct_le_natural_kernel common hb6 hlocal sections).trans (hkernel hE))
    (by rw [hE, hcard])

end SelectedPair
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
