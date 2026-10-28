module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality

/-!
# Noncritical normalization in the backward selection

Let c--e be the given critical path and d a vertex at distance two from c.
If Z_d lies in Q_(e-2), then it acts inside G_e. Consequently [Z_d,Z_e]
lies in K = U_e intersect Q_c. The genuine binary natural marking gives
|U_e| = 8; critical reversal makes K proper, so |K| is at most four.
The critical line D = [Z_c,Z_e] has order two and lies in K intersect Z_c.

Put T = [[Z_d,Q_c],Z_e]. If T lies in Z_c, the required normalization
follows directly. Otherwise D and T generate K, proving
[Z_d,Z_e] <= T Z_c from the actual path and natural-module data.
Source (2.1)(vi) now normalizes [Z_d,Q_c] Z_c. Transporting only the vertex
d within its actual G_c-orbit supplies the missing containment implication
in `exists_backwardWitness_of_outside`; the final theorem applies that
selection to construct the full outside-B_c backward witness.

Only the independent critical-line order calculation is used from
`CriticalCase.Inequality`, not its later claim (3). No natural-section,
trapped-radius, centrality, or b = 8 conclusion is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.1), claim (2), printed p.891; (2.1)(vi), pp.855--856;
and the binary natural-module calculation of (3.5), pp.869--870.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase

private theorem normalizes_join_of_commutator_le {G : Type*} [Group G]
    (A B C : Subgroup G) (hBC : B ≤ normalizer C) (hcomm : ⁅A,B⁆ ≤ C) :
    B ≤ normalizer (A ⊔ C : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hm : (A ⊔ C).map (MulAut.conj b).toMonoidHom ≤ A ⊔ C := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨a, ha, rfl⟩
      have hc : ⁅b,a⁆ ∈ C := by
        rw [commutator_comm] at hcomm
        exact hcomm (commutator_mem_commutator hb ha)
      have hh := (A ⊔ C).mul_mem (mem_sup_right hc) (mem_sup_left ha)
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · exact (mem_normalizer_iff_map_conj_eq.mp (hBC hb)).le.trans le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj b).toMonoidHom hx)

private theorem small_join_eq {G : Type*} [Group G]
    (D T K : Subgroup G) [Finite K] (hDK : D ≤ K) (hTK : T ≤ K)
    (hD : Nat.card D = 2) (hK : Nat.card K ≤ 4) (hne : ¬ T ≤ D) :
    D ⊔ T = K := by
  have hJK : D ⊔ T ≤ K := sup_le hDK hTK
  let : Finite (D ⊔ T : Subgroup G) :=
    Finite.of_injective (inclusion hJK) (inclusion_injective _)
  have hlt : 2 < Nat.card (D ⊔ T : Subgroup G) := by
    by_contra! hh
    have he : D = D ⊔ T := eq_of_le_of_card_ge le_sup_left (by omega)
    exact hne (he ▸ le_sup_right)
  have hdvd : 2 ∣ Nat.card (D ⊔ T : Subgroup G) := hD ▸ card_dvd_of_le le_sup_left
  apply eq_of_le_of_card_ge hJK
  omega

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem critical_natural_kernel_card_le_four
    (common : CommonFacts R source geometry) {c e : Vertex R}
    (p : CriticalPath R geometry c e) :
    Nat.card (U R e ⊓ Q R c : Subgroup (FreeAmalgam R)) ≤ 4 := by
  let s := naturalStructure common
  have hU : Nat.card (U R e) = 8 := common.natural.card_at e p.end_color
  let : Finite (U R e) := Nat.finite_of_card_ne_zero (by omega)
  have hnot : ¬ U R e ≤ Q R c := by
    intro h
    have hi := s.critical_Z_index_eq_U geometry e p.end_color c
      (p.reverse common).critical
    rw [relIndex_eq_one.mpr h] at hi
    exact (p.reverse common).critical.2 (relIndex_eq_one.mp hi)
  have hlt : Nat.card (U R e ⊓ Q R c : Subgroup (FreeAmalgam R)) < 8 := by
    by_contra! h
    have he : U R e ⊓ Q R c = U R e := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnot (he ▸ inf_le_right)
  have hdiv := card_dvd_of_le (show U R e ⊓ Q R c ≤ U R e from inf_le_left)
  rw [hU] at hdiv
  have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  omega

private theorem normalizes_displacement_of_kernel_containment
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {d c e : Vertex R} (hdc : color R d = false)
    (hd : (cosetGraph R).dist d c = 2) (p : CriticalPath R geometry c e)
    (hcontained : Z R d ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    Z R e ≤ normalizer (⁅Z R d, Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
  let E := ⁅Z R d, Q R c⁆
  let T := ⁅E, Z R e⁆
  let K := U R e ⊓ Q R c
  let D := ⁅Z R c, Z R e⁆
  have hBG : Z R e ≤ stabilizer R c := p.endpoint_Z_le_start_stabilizer (by omega)
  have hBN : Z R e ≤ normalizer (Z R c) := hBG.trans (Z_normalized R c)
  have hAQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
    rw [geometry.distance_constant d hdc, hd]
    exact lt_trans (by decide : 2 < 4) hb
  have hEA : E ≤ Z R d := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_stabilizer_of_dist_two R c d p.start_color
      (by rw [SimpleGraph.dist_comm]; exact hd)).trans (Z_normalized R d))
  have hv : color R (p.walk.getVert (p.walk.length - 2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven := geometry.even c p.start_color
    rw [← p.critical.1, ← p.shortest, Nat.even_iff] at heven
    rw [Nat.even_iff]
    have hl := p.length_eq_b
    omega
  have hvd : (cosetGraph R).dist (p.walk.getVert (p.walk.length - 2)) e = 2 := by
    rw [p.dist_end]
    have hl := p.length_eq_b
    omega
  have hAG : Z R d ≤ stabilizer R e :=
    hcontained.trans (Q_le_stabilizer_of_dist_two R _ e hv hvd)
  have hHU : ⁅Z R d, Z R e⁆ ≤ U R e := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hAG).trans
      (Escape.Initial.Z_commutator_stabilizer source e p.end_color).le
  have hHQ : ⁅Z R d, Z R e⁆ ≤ Q R c :=
    (commutator_mono hAQ le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hBG.trans (Q_normalized R c)))
  have hHK : ⁅Z R d, Z R e⁆ ≤ K := le_inf hHU hHQ
  have hDC : D ≤ Z R c := le_normalizer_iff_commutator_le_left.mp hBN
  have hDU : D ≤ U R e := by
    rw [show D = ⁅Z R e, Z R c⁆ from commutator_comm _ _]
    exact (commutator_mono le_rfl
      ((p.reverse common).endpoint_Z_le_start_stabilizer (by omega))).trans
        (Escape.Initial.Z_commutator_stabilizer source e p.end_color).le
  have hDK : D ≤ K := le_inf hDU (hDC.trans
    (Z_le_Q_of_dist_lt R c (geometry.exists_critical c p.start_color) (by
      rw [geometry.distance_constant c p.start_color]
      change (cosetGraph R).dist c c < geometry.b R
      simpa using (show 0 < geometry.b R by omega))))
  have hTK : T ≤ K := (commutator_mono hEA le_rfl).trans hHK
  by_cases ht : T ≤ Z R c
  · exact normalizes_join_of_commutator_le E (Z R e) (Z R c) hBN ht
  · have hU := common.natural.card_at e p.end_color
    let : Finite (U R e) := Nat.finite_of_card_ne_zero (by omega)
    let : Finite K := Finite.of_injective (inclusion (show K ≤ U R e from inf_le_left))
      (inclusion_injective _)
    have he : D ⊔ T = K := small_join_eq D T K hDK hTK
      (critical_commutator_card common p) (critical_natural_kernel_card_le_four common p)
      (fun h => ht (h.trans hDC))
    have hbound : ⁅Z R d, Z R e⁆ ≤ T ⊔ Z R c :=
      hHK.trans (he.ge.trans (sup_le (hDC.trans le_sup_right) le_sup_left))
    exact (source_2_1_vi R source geometry c p.start_color
      (by rw [geometry.distance_constant c p.start_color]; change 0 < geometry.b R; omega)
      p.critical d (by rw [SimpleGraph.dist_comm]; exact hd) hAQ hbound).2

/-- Containment at the penultimate M-vertex forces normalization of the
actual displacement of any conjugate in the G_c-orbit. -/
theorem normalizes_displacement_of_containment
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (p : CriticalPath R geometry c e)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hcontained : Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    Z R e ≤ normalizer (⁅Z R (act R g a), Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
  have hfix : act R g c = c := hg
  apply normalizes_displacement_of_kernel_containment common hb
    ((action_preserves_color R g a).trans ha) ?_ p hcontained
  rw [← hfix, dist_act]
  exact hd

/-- Claim (2) outside B_c, with the noncritical-normalization premise of
`exists_backwardWitness_of_outside` discharged on its actual conjugate. -/
theorem exists_backwardWitness_of_displacement_outside_B
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (p : CriticalPath R geometry c e)
    (hout : ¬ ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    Nonempty (BackwardWitness R geometry a c) := by
  exact exists_backwardWitness_of_outside common hb ha hd p hout
    (fun _ hg h => normalizes_displacement_of_containment common hb ha hd p hg h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
