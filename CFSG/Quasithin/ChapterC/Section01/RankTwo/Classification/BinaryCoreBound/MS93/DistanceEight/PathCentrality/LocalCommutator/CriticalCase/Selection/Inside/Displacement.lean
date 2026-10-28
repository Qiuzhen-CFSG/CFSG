module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Conjugates

/-!
# The order-two displacement of the escaping span

Any subgroup of <Z_a^{G_c}> trapped in Q_(e-2) has displacement by Z_e of
order at most two modulo Z_c. Adjoin Z_c to that subgroup. Its commutator
with Z_e lies both in U_e and Q_c, so its order is at most four: equality
with the natural eight-group would contradict the critical pair. Its
intersection with Z_c contains the nontrivial critical commutator, leaving
quotient order at most two. Restricting back to the original subgroup gives
the bound without assuming it contains Z_c.

The final theorem applies this bound to the literal escaping span W used in
(1.6). Neither a trapped radius group nor a later centrality result is used.
The natural-module recognition and splitting remain separate obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (2), p.891,
and the invocation of (1.6), printed pp.845--847.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The order-two displacement bound for any part of the source span
trapped in the penultimate M-kernel. No trapping of the whole radius group is used. -/
theorem trapped_displacement_index_le_two [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ localZSpan R a c)
    (htrap : A ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    (Z R c).relIndex ⁅A, Z R e⁆ ≤ 2 := by
  let d := p.walk.getVert (p.walk.length - 2)
  have hlen := p.length_eq_b
  have hdcolor : color R d = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven : Even p.walk.length := by
      rw [p.shortest, p.critical.1]
      exact geometry.even c p.start_color
    rw [Nat.even_iff] at heven ⊢
    omega
  have hde : (cosetGraph R).dist d e = 2 := by
    dsimp [d]
    rw [p.dist_end]
    omega
  have hZtrap : Z R c ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c p.start_color)
    rw [geometry.distance_constant c p.start_color]
    dsimp [d]
    rw [p.dist_start (Nat.sub_le _ _), p.length_eq_b]
    change geometry.b R - 2 < geometry.b R
    omega
  let J := A ⊔ Z R c
  let D := ⁅J, Z R e⁆
  have hJspan : J ≤ localZSpan R a c :=
    sup_le hA (center_Z_le_span p.start_color hd)
  have hJend : J ≤ stabilizer R e :=
    (sup_le htrap hZtrap).trans (Q_le_stabilizer_of_dist_two R d e hdcolor hde)
  have hDQ : D ≤ Q R c := by
    apply le_trans (commutator_mono hJspan le_rfl)
    exact (le_normalizer_iff_commutator_le_left.mp
      ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (localZSpan_normalized R a c))).trans
        (localZSpan_le_Q R p.start_color hd.le (by omega))
  have hDU : D ≤ U R e := by
    dsimp [D]
    rw [commutator_comm]
    exact (commutator_mono le_rfl hJend).trans
      (Escape.Initial.Z_commutator_stabilizer source e p.end_color).le
  let : Finite (U R e) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at e p.end_color]; decide)
  let : Finite D := Finite.of_injective (inclusion hDU) (inclusion_injective _)
  have hsmall : Nat.card D ≤ 4 := by
    have hdvd := card_dvd_of_le hDU
    rw [common.natural.card_at e p.end_color] at hdvd
    have hne : Nat.card D ≠ 8 := by
      intro hcard
      have heq : D = U R e := eq_of_le_of_card_ge hDU
        (by rw [common.natural.card_at e p.end_color, hcard])
      have hUQ : U R e ≤ Q R c := heq ▸ hDQ
      apply p.critical.2
      rw [← common.natural.centralizer e p.end_color]
      exact le_inf (source.critical_Z_le_stabilizer geometry c p.start_color e p.critical).1
        ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c p.start_color)).trans
          (centralizer_le hUQ))
    have hv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    omega
  have hCD : ⁅Z R c, Z R e⁆ ≤ D := commutator_mono le_sup_right le_rfl
  have hCZ : ⁅Z R c, Z R e⁆ ≤ Z R c :=
    le_normalizer_iff_commutator_le_left.mp
      ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R c))
  let : Finite (⁅Z R c, Z R e⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hCD) (inclusion_injective _)
  let : Finite ↥(Z R c ⊓ D) :=
    Finite.of_injective (inclusion (show Z R c ⊓ D ≤ D from inf_le_right)) (inclusion_injective _)
  let C := (Z R c).subgroupOf D
  have hC : 2 ≤ Nat.card C := by
    have hn := (one_lt_card_iff_ne_bot _).mpr
      (common.critical_noncommutation c p.start_color e p.critical)
    have hc := card_le_of_le (le_inf hCZ hCD)
    have hi : Nat.card C = Nat.card ↥(Z R c ⊓ D) := by
      have hh := Nat.card_congr
        (subgroupOfEquivOfLe (show Z R c ⊓ D ≤ D from inf_le_right)).toEquiv
      simpa only [inf_subgroupOf_right, C] using hh
    rw [hi]
    omega
  have hindex : (Z R c).relIndex D ≤ 2 := by
    change C.index ≤ 2
    have hm := C.index_mul_card
    nlinarith
  exact (relIndex_le_of_le_right (commutator_mono le_sup_left le_rfl)
    (show (Z R c).relIndex D ≠ 0 from ((Z R c).subgroupOf D).index_ne_zero_of_finite)).trans hindex

/-- The exact small displacement supplied to the source (1.6) argument. -/
theorem escapingSpan_displacement_index_le_two [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (htrap : escapingSpan a c e x ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2 :=
  trapped_displacement_index_le_two common hb hd p _
    (escapingSpan_le_localZSpan a c e x) htrap

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
