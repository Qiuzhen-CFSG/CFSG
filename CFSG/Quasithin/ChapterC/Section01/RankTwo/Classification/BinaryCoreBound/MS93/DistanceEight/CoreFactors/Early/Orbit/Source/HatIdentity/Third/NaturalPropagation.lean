module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Endpoint

/-!
# Natural-subgroup propagation in the contrary D argument

The local closure of D contains the preceding natural eight-group. A failed
third containment also supplies the distant central plane by its endpoint
displacement. Two distinct incident planes generate the natural subgroup at
the fourth vertex. The small D commutator then propagates to this subgroup.
Every geometric input of the terminal theorem is derived on the original
source path. No final hat identity is assumed or asserted.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), first display p.898.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third
open PathCentrality NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem normal_span_le {G : Type*} [Group G] {A P K : Subgroup G}
    (hA : A ≤ K) (hn : P ≤ normalizer K) : conjugatesIn A P ≤ K := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hn (P.inv_mem g.property))).le

/-- A nonzero preceding H forces the entire natural subgroup into the local span. -/
theorem U_le_full_span [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (D : Subgroup (FreeAmalgam R)) (hHD : H R b ≤ D) :
    U R a ≤ conjugatesIn D (stabilizer R a) := by
  let J := conjugatesIn D (stabilizer R a)
  have hHJ : H R b ≤ J := hHD.trans (Escape.Initial.Natural.conjugatesIn_contains _ _)
  have hHU := Orbit.H_le_neighbor_U common earlier hb hmove
  have hn : stabilizer R a ≤ normalizer (J ⊓ U R a : Subgroup (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (conjugatesIn_normalized D (stabilizer R a) hg),
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a hg)]
  rcases natural_subgroup_dichotomy common ha (J ⊓ U R a) inf_le_right hn with hz | he
  · have hzero : H R b = ⊥ := le_bot_iff.mp ((le_inf hHJ hHU).trans hz.le)
    have hlo := First.Layer.H_card_lower common earlier b hb
    rw [hzero, card_bot] at hlo
    omega
  · exact he ▸ (show J ⊓ U R a ≤ J from inf_le_left)

/-- Two distinct incident central planes generate the natural eight-group. -/
theorem U_eq_neighbor_H_sup [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {c d e s t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (he : color R e = false) (hcs : Adjacent R c s) (hds : Adjacent R d s)
    (het : Adjacent R e t) (hdt : Adjacent R d t)
    (hcd : d ∈ Escape.movingNeighbors geometry c)
    (hed : d ∈ Escape.movingNeighbors geometry e)
    (hne : Z R s ≠ Z R t) : U R d = H R c ⊔ H R e := by
  have hCU := Orbit.H_le_neighbor_U common earlier hc hcd
  have hEU := Orbit.H_le_neighbor_U common earlier he hed
  have hHU : H R c ⊔ H R e ≤ U R d := sup_le hCU hEU
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at d hd]; decide)
  let : Finite (H R c ⊔ H R e : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hHU) (inclusion_injective _)
  let : Finite (H R c) := Finite.of_injective (inclusion hCU) (inclusion_injective _)
  let : Finite (H R e) := Finite.of_injective (inclusion hEU) (inclusion_injective _)
  have hneq : H R c ≠ H R e := by
    intro hsame
    have hbound : H R c ≤ U R d ⊓ Z R s ⊓ Z R t :=
      le_inf (le_inf hCU (H_le_edge_Z common earlier hc hcs))
        (hsame ▸ H_le_edge_Z common earlier he het)
    let : Finite (U R d ⊓ Z R s ⊓ Z R t : Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion (inf_le_left.trans inf_le_left)) (inclusion_injective _)
    have hcard := (card_le_of_le hbound).trans
      (edge_natural_intersection_card_le_two common earlier hd hds hdt hne)
    have hlo := First.Layer.H_card_lower common earlier c hc
    omega
  apply (eq_of_le_of_card_ge hHU ?_).symm
  by_contra! hh
  rw [common.natural.card_at d hd] at hh
  have hdiv := Nat.mem_divisors.mpr
    ⟨(common.natural.card_at d hd) ▸ card_dvd_of_le hHU, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsmall : Nat.card (H R c ⊔ H R e : Subgroup (FreeAmalgam R)) ≤ 4 := by omega
  have hC := eq_of_le_of_card_ge (show H R c ≤ H R c ⊔ H R e from le_sup_left)
    (hsmall.trans (First.Layer.H_card_lower common earlier c hc))
  have hE := eq_of_le_of_card_ge (show H R e ≤ H R c ⊔ H R e from le_sup_right)
    (hsmall.trans (First.Layer.H_card_lower common earlier e he))
  exact hneq (hC.trans hE.symm)

/-- The span commutator estimate propagates to its full local closure. -/
theorem full_span_commutator_le_U [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b : Vertex R} (hb : color R b = false)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (D : Subgroup (FreeAmalgam R)) (hD : D ≤ Q R a)
    (hsmall : ⁅D, Q R a⁆ ≤ H R b) :
    ⁅conjugatesIn D (stabilizer R a), Q R a⁆ ≤ U R a := by
  rw [Escape.PairingControl.commutator_conjugatesIn _ _ _ hD (Q_normalized R a)]
  exact normal_span_le (hsmall.trans (Orbit.H_le_neighbor_U common earlier hb hmove))
    (U_normalized a)

/-- The second line of the contrary case on the original path: both
planes at the fourth vertex belong to the full span of D. -/
theorem forward_failed_containment_natural_bound [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hD : normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 6)))
    (hsmall : ⁅normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)), Q R (p.walk.getVert i)⁆ ≤ H R (p.walk.getVert (i - 2)))
    (hnot : ¬ (normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))) :
    U R (p.walk.getVert (i + 4)) ≤ conjugatesIn
        (normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
          (p.walk.getVert (i - 1))) (stabilizer R (p.walk.getVert i)) ∧
      ⁅U R (p.walk.getVert (i + 4)), Q R (p.walk.getVert i)⁆ ≤
        U R (p.walk.getVert i) := by
  let D := normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
    (p.walk.getVert (i - 1))
  let J := conjugatesIn D (stabilizer R (p.walk.getVert i))
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hic : Even (i + 2) := hi.add (by decide)
  have hid : Even (i + 4) := hi.add (by decide)
  have hie : Even (i + 6) := hi.add (by decide)
  have hba : p.walk.getVert i ∈ Escape.movingNeighbors geometry (p.walk.getVert (i - 2)) := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  have hHD : H R (p.walk.getVert (i - 2)) ≤ D :=
    (H_le_fixedSeed common earlier (p.even_color hib (by omega))).trans (fixedSeed_le_span _ _ _)
  have hUa : U R (p.walk.getVert i) ≤ J := U_le_full_span common earlier
    (p.even_color hi (by omega)) (p.even_color hib (by omega)) hba D hHD
  have hHc : H R (p.walk.getVert (i + 2)) ≤ J :=
    (Orbit.H_le_neighbor_U common earlier (p.even_color hic (by omega)) (by
      simpa only [Nat.add_sub_cancel] using
        (p.moving_neighbors source common earlier hic (by omega) (by omega)).1)).trans hUa
  have hHe : H R (p.walk.getVert (i + 6)) ≤ J := by
    rw [← forward_failed_containment_commutator common earlier p hi hi4 hi6 hD hnot]
    apply (commutator_mono (Escape.Initial.Natural.conjugatesIn_contains D _) ?_).trans
      (le_normalizer_iff_commutator_le_left.mp (conjugatesIn_normalized D (stabilizer R (p.walk.getVert i))))
    exact le_sup_right.trans (forward_generation common earlier p
      (firstFactsOnPath source common earlier p) hi (by omega) hi6).le
  have hUd : U R (p.walk.getVert (i + 4)) ≤ J := by
    rw [U_eq_neighbor_H_sup common earlier
      (c := p.walk.getVert (i + 2)) (e := p.walk.getVert (i + 6))
      (s := p.walk.getVert (i + 3)) (t := p.walk.getVert (i + 5))
      (p.even_color hic (by omega)) (p.even_color hid (by omega))
      (p.even_color hie (by omega))]
    · exact sup_le hHc hHe
    · simpa only [Nat.add_assoc] using p.adjacent (i := i + 2) (by omega)
    · exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 3) (by omega))
    · exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega))
    · simpa only [Nat.add_assoc] using p.adjacent (i := i + 4) (by omega)
    · simpa only [Nat.add_assoc] using
        (p.moving_neighbors source common earlier hic (by omega) (by omega)).2
    · simpa only [show i + 6 - 2 = i + 4 by omega] using
        (p.moving_neighbors source common earlier hie (by omega) (by omega)).1
    · simpa only [show i + 4 - 1 = i + 3 by omega, Nat.add_assoc] using
        p.edge_Z_ne (i + 4) hid (by omega) (by omega)
  refine ⟨hUd, (commutator_mono hUd le_rfl).trans ?_⟩
  exact full_span_commutator_le_U common earlier (p.even_color hib (by omega)) hba D
    (span_le_Q earlier (p.even_color hib (by omega)) hba.1) hsmall

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third
