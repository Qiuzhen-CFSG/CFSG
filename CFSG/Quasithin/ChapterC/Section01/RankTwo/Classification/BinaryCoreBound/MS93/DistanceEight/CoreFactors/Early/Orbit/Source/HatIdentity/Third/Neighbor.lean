module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Endpoint

/-!
# The full edge action of a neighboring vertex kernel

At a moving pair, the preceding H of order four is exactly the displacement
of the neighboring Z under the vertex kernel. Its common fixed subgroup is
the incident edge hyperplane. Evaluation outside that hyperplane identifies
the faithful action index with displacement order, hence with four. The
kernel therefore covers the complete edge quotient at the other vertex.
The terminal application preserves every vertex of the original SourcePath.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), the natural-module
inference after the first display on printed p.898, using (4.4)--(4.5.1).
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Neighbor
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem eq_of_index_two {G : Type*} [Group G] {N F U : Subgroup G}
    (hNF : N ≤ F) (hFU : F ≤ U) (hi : N.relIndex U = 2) (hne : F ≠ U) : F = N := by
  have hm := relIndex_mul_relIndex N F U hNF hFU
  rw [hi] at hm
  have hdiv : F.relIndex U ∣ 2 := ⟨N.relIndex F, by simpa only [Nat.mul_comm] using hm.symm⟩
  have hidx : F.relIndex U = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
    (fun h => hne (le_antisymm hFU (relIndex_eq_one.mp h)))
  rw [hidx] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hNF

private theorem fixed_eq_edge (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {d s : Vertex R} (hd : color R d = false) (hds : Adjacent R d s)
    {P : Subgroup (FreeAmalgam R)} (hP : P ≤ Q R s) (hn : ¬ P ≤ Q R d) :
    Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) = Z R s := by
  have heq := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (LocalCommutator.moduleFacts common) d s hd hds
  apply eq_of_index_two
    (show Z R s ≤ Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) from
      heq ▸ le_inf inf_le_left (inf_le_right.trans (centralizer_le hP))) inf_le_left
    (earlier.edge_Z_index d s hd hds)
  intro h
  apply hn
  rw [← common.centralizer d s hd hds]
  refine le_inf hP (le_centralizer_iff.mp ?_)
  exact (show Z R d ≤ Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) from h.ge).trans inf_le_right

private theorem product_eq_of_large_image {G : Type*} [Group G]
    {D Q S : Subgroup G} (hD : D ≤ S) (hQ : Q ≤ S)
    (hn : S ≤ normalizer (Q : Set G)) (hi : Q.relIndex S = 4)
    (himage : 2 < Q.relIndex D) :
    (D : Set G) * (Q : Set G) = (S : Set G) := by
  let A := D.subgroupOf S
  let K := Q.subgroupOf S
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  have hidx : K.relIndex A = 4 := by
    have hKi : K.index = 4 := hi
    have hdvd : K.relIndex A ∣ 4 := hKi ▸ K.relIndex_dvd_index_of_normal A
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hgt : 2 < K.relIndex A := by rwa [relIndex_subgroupOf hD]
    omega
  have hm := relIndex_mul_index (show K ≤ A ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hidx, show K.index = 4 from hi] at hm
  have he : A ⊔ K = ⊤ := index_eq_one.mp (by omega)
  have hj : D ⊔ Q = S := by
    have hh := congrArg (Subgroup.map S.subtype) he
    simpa only [A, K, Subgroup.map_sup, map_subgroupOf_eq_of_le hD,
      map_subgroupOf_eq_of_le hQ, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [← coe_mul_of_left_le_normalizer_right _ _ (hD.trans hn), hj]

/-- At a moving pair the other vertex kernel has the full incident
four-group as its image, with the actual ordered product retained. -/
theorem moving_kernel_product (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : c ∈ Escape.movingNeighbors geometry a) :
    (Q R a : Set (FreeAmalgam R)) * (Q R c : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQa := Q_le_adjacent_h R ht hat
  have hQt : Q R t ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hdisp : ⁅Z R c, Q R a⁆ = H R a := by
    apply le_antisymm
    · exact (commutator_mono le_rfl hQa).trans
        (moving_edge_displacement_eq_H common earlier hc ha hct hat hmove).le
    · exact Orbit.H_le_displacement common earlier ha hmove
  have hHcard : Nat.card (H R a) = 4 :=
    Nat.le_antisymm (H_card_le_four common earlier ha) (First.Layer.H_card_lower common earlier a ha)
  have hn : ¬ Q R a ≤ Q R c := by
    intro h
    have hz : H R a = ⊥ := le_bot_iff.mp
      (hdisp.ge.trans ((commutator_mono le_rfl h).trans (Z_centralizes_Q R c hc).le))
    rw [hz, card_bot] at hHcard
    omega
  have hfixed := fixed_eq_edge common earlier hc hct hQa hn
  have hE : ⁅Z R c, Q R a⁆ ≤ Z R t :=
    (commutator_mono le_rfl hQa).trans
      (commutator_le_of_normalized_index_two _ _ _
        (Escape.EdgeTransfer.edge_Z_le c t hc hct) (earlier.edge_Z_index c t hc hct)
        (hQt.trans (Z_normalized R c))
        ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t)))
  have hsmall : ⁅Z R c, Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
    rw [← hfixed] at hE
    exact hE.trans inf_le_right
  let := geometry.Z_elementary (by have := common.large_distance; omega) c hc
  have hi := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R c) (Q R a) (hQa.trans (hQt.trans (Z_normalized R c))) hsmall
    (by rw [hfixed]; exact earlier.edge_Z_index c t hc hct)
  have hk : (centralizer (Z R c : Set (FreeAmalgam R))).subgroupOf (Q R a) =
      (Q R c).subgroupOf (Q R a) := by
    ext x
    change (x : FreeAmalgam R) ∈ centralizer (Z R c : Set (FreeAmalgam R)) ↔
      (x : FreeAmalgam R) ∈ Q R c
    constructor
    · intro hx
      rw [← common.centralizer c t hc hct]
      exact ⟨hQa x.property, hx⟩
    · intro hx
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R c hc)) hx
  have hindex : (Q R c).relIndex (Q R a) = 4 := by
    change ((Q R c).subgroupOf (Q R a)).index = 4
    rw [← hk]
    change (centralizer (Z R c : Set (FreeAmalgam R))).relIndex (Q R a) = 4
    rw [hi, hdisp, hHcard]
  exact product_eq_of_large_image hQa (Q_le_adjacent_h R ht hct)
    (hQt.trans (Q_normalized R c)) (earlier.edge_Q_index c t hc hct)
    (by rw [hindex]; decide)

/-- Literal forward point-radical input at each interior source edge. -/
theorem forward_kernel_product (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi10 : i ≤ 10) :
    (Q R (p.walk.getVert i) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert (i + 2)) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert (i + 1)) : Set (FreeAmalgam R)) := by
  apply moving_kernel_product common earlier (p.even_color hi (by omega))
    (p.even_color (hi.add (by decide : Even 2)) (by omega))
    (p.adjacent (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · exact (p.moving_neighbors source common earlier hi hi2 (by omega)).2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Neighbor
