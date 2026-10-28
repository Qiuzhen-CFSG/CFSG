module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.SourceLines
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed.Failure

/-!
# The opposite hat identity from the genuine natural commutator bound

The two original incident parabolics give different quotient lines. Removing
local fixed summands preserves their commutator obstruction. A nonzero extra
line together with the central plane fills the natural eight-group, placing
it in the opposite moving layer and forcing the first-hat identity there.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.898.
The original markings and natural quotient are retained throughout.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Opposite
open PathCentrality NormalizerTransfer Preliminary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem H_le_moving (c : Vertex R) : H R c ≤ Vcirc R c :=
  le_normalizer_iff_commutator_le_left.mp ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (Vcirc_normalized c))

private theorem fixed_le_incident (common : CommonFacts R source geometry)
    {d c v : Vertex R} (hd : color R d = false) (hc : color R c = false)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v) :
    Z R d ⊓ centralizer (stabilizer R d : Set (FreeAmalgam R)) ≤ Z R c := by
  apply le_trans _ (Escape.EdgeTransfer.edge_Z_le c v hc hcv)
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (LocalCommutator.moduleFacts common) d v hd hdv]
  exact inf_le_inf_left _ (centralizer_le (fun _ hx => hx.2 d (adjacent_symm R hdv)))

private theorem hat_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {d c v : Vertex R}
    (hd : color R d = false) (hc : color R c = false)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v)
    (hm : d ∈ Escape.movingNeighbors geometry c) :
    ⁅hatV R c d, stabilizer R c⁆ ≤ Vcirc R c := by
  have hQ := (hatV_commutator_le_H common earlier hd hc hdv hcv hm).trans (H_le_moving c)
  have hL : ⁅hatV R c d, Ltilde R c⁆ ≤ Vcirc R c :=
    commutator_mono (hatV_le_radius R (by rw [SimpleGraph.dist_comm, hm.1])) le_rfl
  have hpre : stabilizer R c ≤ commutatorPreimage (stabilizer R c) (hatV R c d) (Vcirc R c) := by
    conv_lhs => rw [← source.local_generation c hc]
    exact sup_le
      (le_commutatorPreimage (Ltilde_le_stabilizer c) (by rwa [commutator_comm]))
      (le_commutatorPreimage (fun _ hx => hx.1) (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Vcirc_normalized c))

/-- The marked quotient-line obstruction still detects movement after
removing the fixed part of the distant Z-layer and the middle Q-kernel. -/
theorem natural_commutator_not_le_B (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d u v : Vertex R}
    (ha : color R a = false) (hc : color R c = false) (hd : color R d = false)
    (hau : Adjacent R a u) (hcu : Adjacent R c u)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v)
    (hma : a ∈ Escape.movingNeighbors geometry c)
    (hmd : d ∈ Escape.movingNeighbors geometry c)
    (hne : Z R u ≠ Z R v) : ¬ ⁅U R d, Q R a⁆ ≤ B R c (geometry.Z_normal c) := by
  intro hsmall
  obtain ⟨s⟩ := earlier.natural_section c hc
  apply SourceLines.not_neighbor_commutator_le_B common earlier ha hc hd hau hcu hdv hcv hma hmd hne s
  have hQa : Q R a ≤ stabilizer R c := Q_le_stabilizer_of_dist_two R a c ha (by rw [SimpleGraph.dist_comm]; exact hma.1)
  have hBc := Escape.Propagation.Rigidity.B_normalized common.large_distance c hc
  have hZB := Escape.EdgeTransfer.Z_le_B common.large_distance c hc
  have hZd : Z R d ≤ stabilizer R c :=
    (Z_le_localZSpan R d c).trans ((hatV_le_radius R (by rw [SimpleGraph.dist_comm,hmd.1])).trans s.local_group)
  have hfixed := fixed_le_incident common hd hc hdv hcv
  have hfixedcomm : ⁅Z R d ⊓ centralizer (stabilizer R d : Set (FreeAmalgam R)), Q R a⁆ ≤ B R c (geometry.Z_normal c) :=
    (commutator_mono hfixed le_rfl).trans
      ((le_normalizer_iff_commutator_le_left.mp (hQa.trans (Z_normalized R c))).trans hZB)
  have hZacom : ⁅Z R d, Q R a⁆ ≤ B R c (geometry.Z_normal c) := by
    have hp : Z R d ≤ commutatorPreimage (stabilizer R c) (Q R a) (B R c (geometry.Z_normal c)) := by
      rw [(LocalCommutator.naturalStructure common).decomposition_at d hd]
      exact sup_le (le_commutatorPreimage ((U_le_Z R d).trans hZd) hsmall)
        (le_commutatorPreimage (inf_le_left.trans hZd) hfixedcomm)
    exact (commutator_mono hp le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hBc)
  have hZccom : ⁅Z R d, Q R c⁆ ≤ B R c (geometry.Z_normal c) :=
    ((commutator_mono (Z_le_localZSpan R d c) le_rfl).trans
      (hatV_commutator_le_H common earlier hd hc hdv hcv hmd)).trans
      ((H_le_Z_of_central common hc (earlier.centrality c hc)).trans hZB)
  have hp : Q R u ≤ commutatorPreimage (stabilizer R c) (Z R d) (B R c (geometry.Z_normal c)) := by
    have hprod := Neighbor.moving_kernel_product common earlier hc ha hcu hau hma
    intro x hx
    have hx' : x ∈ (Q R c : Set (FreeAmalgam R)) * (Q R a : Set (FreeAmalgam R)) := hprod.symm ▸ hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    exact (commutatorPreimage _ _ _).mul_mem
      (le_commutatorPreimage (show Q R c ≤ stabilizer R c from fun _ hx => hx.1) (by rwa [commutator_comm]) hy)
      (le_commutatorPreimage hQa (by rwa [commutator_comm]) hz)
  rw [commutator_comm]
  exact (commutator_mono hp le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hBc)

/-- A bounded distant natural commutator forces the opposite natural
subgroup into the actual moving layer. -/
theorem natural_le_moving (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d u v : Vertex R}
    (ha : color R a = false) (hc : color R c = false) (hd : color R d = false)
    (hau : Adjacent R a u) (hcu : Adjacent R c u)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v)
    (hma : a ∈ Escape.movingNeighbors geometry c)
    (hmd : d ∈ Escape.movingNeighbors geometry c)
    (hne : Z R u ≠ Z R v) (hsmall : ⁅U R d, Q R a⁆ ≤ U R a) :
    U R a ≤ Vcirc R c := by
  let J := U R a ⊓ Vcirc R c
  have hHJ : H R c ≤ J := le_inf (Orbit.H_le_neighbor_U common earlier hc hma) (H_le_moving c)
  have hKJ : ⁅U R d, Q R a⁆ ≤ J := le_inf hsmall
    ((commutator_mono ((U_le_Z R d).trans (Z_le_localZSpan R d c))
      (Q_le_stabilizer_of_dist_two R a c ha (by rw [SimpleGraph.dist_comm]; exact hma.1))).trans
        (hat_commutator common earlier hd hc hdv hcv hmd))
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  let : Finite J := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have he : J = U R a := by
    apply eq_of_le_of_card_ge inf_le_left
    by_contra! hlt
    rw [common.natural.card_at a ha] at hlt
    have hdiv := Nat.mem_divisors.mpr
      ⟨(common.natural.card_at a ha) ▸ card_dvd_of_le (show J ≤ U R a from inf_le_left), (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    have hcard : Nat.card J ≤ 4 := by
      change Nat.card J = 1 ∨ Nat.card J = 2 ∨ Nat.card J = 4 ∨ Nat.card J = 8 at hdiv
      dsimp only [J] at hdiv ⊢
      omega
    have hj : H R c = J := eq_of_le_of_card_ge hHJ (hcard.trans (First.Layer.H_card_lower common earlier c hc))
    exact natural_commutator_not_le_B common earlier ha hc hd hau hcu hdv hcv hma hmd hne
      (hKJ.trans (hj ▸ (H_le_Z_of_central common hc (earlier.centrality c hc)).trans
        (Escape.EdgeTransfer.Z_le_B common.large_distance c hc)))
  exact he ▸ (show J ≤ Vcirc R c from inf_le_right)

/-- The same marked commutator bound closes the opposite hat identity. -/
theorem hat_eq_of_natural_bound (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d u v : Vertex R}
    (ha : color R a = false) (hc : color R c = false) (hd : color R d = false)
    (hau : Adjacent R a u) (hcu : Adjacent R c u)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v)
    (hma : a ∈ Escape.movingNeighbors geometry c)
    (hmd : d ∈ Escape.movingNeighbors geometry c)
    (hne : Z R u ≠ Z R v) (hsmall : ⁅U R d, Q R a⁆ ≤ U R a) :
    hatV R c a = Vcirc R c ⊔ Z R c := by
  apply le_antisymm
  · rw [hatV_eq_conjugatesIn]
    apply iSup_le
    intro g
    have hseed : Z R a ≤ Vcirc R c ⊔ Z R c := by
      rw [(LocalCommutator.naturalStructure common).decomposition_at a ha]
      exact sup_le ((natural_le_moving common earlier ha hc hd hau hcu hdv hcv hma hmd hne hsmall).trans le_sup_left)
        ((fixed_le_incident common ha hc hau hcu).trans le_sup_right)
    have hn := (normalizer_inf_normalizer_le_normalizer_sup (Vcirc R c) (Z R c))
      ⟨Vcirc_normalized c ((stabilizer R c).inv_mem g.property), Z_normalized R c ((stabilizer R c).inv_mem g.property)⟩
    exact (map_mono hseed).trans (mem_normalizer_iff_map_conj_eq.mp hn).le
  · exact sup_le (moving_le_hatV source earlier hc hma) (Z_le_hatV hc hma.1)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Opposite
