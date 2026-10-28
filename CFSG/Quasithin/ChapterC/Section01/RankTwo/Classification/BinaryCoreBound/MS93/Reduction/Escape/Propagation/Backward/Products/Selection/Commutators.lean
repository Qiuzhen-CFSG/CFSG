module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Commutator

/-!
# The line determined by a failed backward-span bound

Every radius generator in W(t) has its Z_d-commutator in the displacement
at t. This extends the checked critical-generator comparison to the whole
span, using critical minimality for the central generator. Locality then
puts the commutator in U_d. Since d is close to the endpoint, it centralizes
the endpoint Z-layer. The local pencil comparison identifies a nonzero
such commutator with the intersection line.

A plane split as a natural line and a central line has a unique natural
intersection. This is the precise independence argument used when changing
the generating edge on printed p.887.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The comparison with the starting displacement holds for the entire
reverse-moving span, without assuming the span lies in Q_d. -/
theorem backwardSpan_commutator_le_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (d t : Vertex R) (hd : Before p.a p.a' d 4) (hat : Adjacent R p.a t) :
    ⁅backwardSpan geometry p.a t, Z R d⁆ ≤ edgeDisplacement p.a t := by
  have hb₂ : 2 < geometry.b R := by omega
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hEQ : edgeDisplacement p.a t ≤ Z R p.a :=
    (Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)
  have hnorm : Q R p.a ≤ normalizer (edgeDisplacement p.a t : Set (FreeAmalgam R)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.a p.color_a))).trans (centralizer_le hEQ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hspan : backwardSpan geometry p.a t ≤
      commutatorPreimage (Q R p.a) (Z R d) (edgeDisplacement p.a t) := by
    apply iSup_le
    intro e
    apply iSup_le
    intro het
    apply iSup_le
    intro hea
    have hec : color R e = false :=
      (color_eq_of_dist_even R e p.a (hea.1.symm ▸ (by decide : Even 2))).trans p.color_a
    have hVe : V R e ≤ Q R p.a := V_le_Q_of_dist_add_two_lt hec (by rw [hea.1]; exact hb)
    apply (V_le_iff hec _).mpr
    intro f hfc hfe
    have hZf : Z R f ≤ V R e := le_iSup_of_le f (le_iSup_of_le hfe le_rfl)
    apply le_commutatorPreimage (hZf.trans hVe)
    by_cases hzero : (cosetGraph R).dist f e = 0
    · have hEq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst f
      have hZd : Z R d ≤ Q R e := by
        apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
        rw [geometry.distance_constant d hdc]
        change (cosetGraph R).dist d e < geometry.b R
        have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := p.a) (w := e)
        have hpath := hd.2
        rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := d)] at hpath
        rw [SimpleGraph.dist_comm (u := p.a) (v := e), hea.1] at htri
        omega
      exact (commutator_mono le_rfl hZd).trans
        ((geometry.centralizes e hec).le.trans bot_le)
    · have heven : Even ((cosetGraph R).dist f e) := by
        obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist f e
        rw [← hw, walk_even_iff_color_eq, hfc, hec]
      rw [Nat.even_iff] at heven
      exact backward_critical_commutator_le_edge source p hb₂ control d t e f hd hat het hea
        (by omega)
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)

private theorem eq_of_le_order_two {G : Type*} [Group G]
    (A B : Subgroup G) (hAB : A ≤ B) (hB : Nat.card B = 2) (hA : A ≠ ⊥) : A = B := by
  let : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; decide)
  let : Finite A := Finite.of_injective (inclusion hAB) (inclusion_injective _)
  have hcard : 1 < Nat.card A := (one_lt_card_iff_ne_bot A).mpr hA
  exact eq_of_le_of_card_ge hAB (by rw [hB]; omega)

/-- Locality, the edge comparison and the actual endpoint fixed plane
identify a nontrivial commutator with the intersection line. -/
theorem commutator_eq_edgeLine (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : PencilFacts p β)
    (v t : Vertex R) (hvc : color R v = false)
    (hnear : (cosetGraph R).dist v p.a' < geometry.b R)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (W : Subgroup (FreeAmalgam R)) (hlocal : W ≤ stabilizer R v)
    (hcomm : ⁅W, Z R v⁆ ≤ edgeDisplacement p.a t) (hbad : ¬ W ≤ Q R v) :
    ⁅W, Z R v⁆ = edgeLine p β t := by
  have hnatural := local_commutator_le_natural source v hvc W hlocal
  have hQ : Z R v ≤ Q R p.a' := by
    apply Z_le_Q_of_dist_lt R v (geometry.exists_critical v hvc)
    rw [geometry.distance_constant v hvc]
    exact hnear
  have hcentral : ⁅W, Z R v⁆ ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) :=
    ((hnatural.trans (U_le_Z v)).trans hQ).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a' p.end_color)))
  have hfixed : ⁅W, Z R v⁆ ≤ edgeDisplacement p.a β := by
    rw [← pencil.fixed_plane]
    exact le_inf (hcomm.trans (Initial.edge_le_natural source p.a t p.color_a hat)) hcentral
  have hline : ⁅W, Z R v⁆ ≤ edgeLine p β t :=
    le_inf hcomm (hfixed.trans (edge_le_Z p hb control edge p.a β p.color_a hβ.endpoint_adjacent))
  apply eq_of_le_order_two _ _ hline (pencil.line_card t hat hgen)
  intro hzero
  apply hbad
  apply (le_Q_iff_commutator_le_center source modules v hvc W hlocal).mpr
  rw [hzero]
  exact bot_le

private theorem sup_inf_eq_of_central_disjoint {G : Type*} [Group G]
    (A K U : Subgroup G) (hA : A ≤ U) (hK : K ≤ centralizer (U : Set G))
    (hdis : U ⊓ K = ⊥) : (A ⊔ K) ⊓ U = A := by
  apply le_antisymm _ (le_inf le_sup_left hA)
  intro x hx
  have hnorm : K ≤ normalizer (A : Set G) :=
    (hK.trans (centralizer_le hA)).trans (Subgroup.centralizer_le_normalizer _)
  have hprod : x ∈ (A : Set G) * (K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A K hnorm]
    exact hx.1
  obtain ⟨a, ha, k, hk, rfl⟩ := hprod
  have hkU : k ∈ U := by
    have hh := U.mul_mem (U.inv_mem (hA ha)) hx.2
    simpa only [inv_mul_cancel_left] using hh
  have hkone : k = 1 := by
    have hh : k ∈ U ⊓ K := ⟨hkU, hk⟩
    rw [hdis, mem_bot] at hh
    exact hh
  change a * k ∈ A
  rw [hkone, mul_one]
  exact ha

omit [Finite M] in
/-- A natural line supplemented by a central subgroup is uniquely
recovered by intersecting their join with the natural group. -/
theorem join_inf_natural_eq (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (v : Vertex R) (hvc : color R v = false)
    (A K : Subgroup (FreeAmalgam R)) (hA : A ≤ U R v) (hK : K ≤ localCenter v) :
    (A ⊔ K) ⊓ U R v = A := by
  apply sup_inf_eq_of_central_disjoint A K (U R v) hA
  · exact (hK.trans ((le_localCenter_iff v _).mp le_rfl).2).trans
      (centralizer_le ((U_le_Z v).trans (Z_le_stabilizer R v)))
  · apply le_bot_iff.mp
    rw [← Rigidity.U_inf_localCenter_eq_bot modules v hvc]
    exact inf_le_inf_left _ hK

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
