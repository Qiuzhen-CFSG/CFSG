module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.PairedSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Sharpening.OrderFour
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# The terminal fixed-line contradiction for edge containment

For a finite two-group acting on a group of order eight with displacement
of order four, a nontrivial second displacement is the unique fixed line.
Nilpotent saturation and the strict commutator-order decrease prove this
without a finite free amalgam or an unmarked matrix representation.

The actual paired critical path supplies a line in U_alpha central in the
opposite local stabilizer. If Z_alpha intersects the opposite Z-layer with
index two, its edge displacement lies in that opposite Z-layer. A nontrivial
second displacement would then be both in its natural subgroup and locally
central, contradicting the marked natural decomposition. Thus the original
edge displacement lies in Z_beta.

The intersection-index hypothesis remains explicit. Its derivation from the
abelian spans is a separate obligation; this module does not assert (4.6.4)
unconditionally. The edge displacement order four used here is already
proved from InitialFacts, without using edge containment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the final contradiction in (4.6.4), printed p.902. This binary
argument replaces the final displayed fixed-space calculation by its
intrinsic finite-group proof.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Terminal

private theorem commutator_ne_self {G : Type*} [Group G]
    (T A : Subgroup G) [Finite T] (hp : IsPGroup 2 T)
    (hAT : A ≤ T) (hne : A ≠ ⊥) : ⁅A,T⁆ ≠ A := by
  intro heq
  let A₀ := A.subgroupOf T
  have hc : ⁅A₀,(⊤ : Subgroup T)⁆ = A₀ := by
    apply map_injective T.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hAT,
      ← MonoidHom.range_eq_map, range_subtype, heq]
  have hz := le_normal_of_quotient_isPGroup_of_eq_commutator
    A₀ ⊤ ⊥ (hp.to_quotient ⊥) hc
  have hh := congrArg (Subgroup.map T.subtype) (le_bot_iff.mp hz)
  rw [map_subgroupOf_eq_of_le hAT, Subgroup.map_bot] at hh
  exact hne hh

private theorem commutator_normalized {G : Type*} [Group G]
    (T A : Subgroup G) (hn : T ≤ normalizer A) : T ≤ normalizer (⁅A,T⁆ : Subgroup G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hn ht),
    mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer ht)]

/-- In a nonquadratic action on an eight-element group with four-element
 displacement, its nonzero second displacement is the unique fixed line. -/
private theorem second_displacement_eq_fixed_line {G : Type*} [Group G]
    (T U D : Subgroup G) [Finite T] (hp : IsPGroup 2 T)
    (hUT : U ≤ T) (hTU : T ≤ normalizer U)
    (hU : Nat.card U = 8) (hA : Nat.card (⁅U,T⁆ : Subgroup G) = 4)
    (hD : Nat.card D = 2) (hDU : D ≤ U) (hDC : D ≤ centralizer (T : Set G))
    (hnon : ⁅⁅U,T⁆,T⁆ ≠ ⊥) : ⁅⁅U,T⁆,T⁆ = D := by
  let A := ⁅U,T⁆
  let C := U ⊓ centralizer (T : Set G)
  let K := ⁅A,T⁆
  change Nat.card A = 4 at hA
  change K ≠ ⊥ at hnon
  have hAU : A ≤ U := le_normalizer_iff_commutator_le_left.mp hTU
  have hTA := commutator_normalized T U hTU
  have hKA : K ≤ A := le_normalizer_iff_commutator_le_left.mp hTA
  have hCT : C ≤ T := inf_le_left.trans hUT
  have hTC : T ≤ normalizer C :=
    (le_inf hTU (T.le_normalizer.trans (normalizer_le_normalizer_centralizer T))).trans
      inf_normalizer_le_normalizer_inf
  let : Finite U := Finite.of_injective (inclusion hUT) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAU) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U from inf_le_left))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKA) (inclusion_injective _)
  have hproper : ¬ U ≤ C := by
    intro hh
    apply hnon
    have hz : A = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hh.trans inf_le_right)
    change ⁅A,T⁆ = ⊥
    rw [hz, commutator_bot_left]
  have hCA : C ≤ A := by
    let E := C ⊔ A
    have hEU : E ≤ U := sup_le inf_le_left hAU
    let : Finite E := Finite.of_injective (inclusion hEU) (inclusion_injective _)
    by_contra hc
    have hne : A ≠ E := fun he => hc (he ▸ (show C ≤ E from le_sup_left))
    have hlt : 4 < Nat.card E := by
      by_contra! hh
      exact hne (eq_of_le_of_card_ge le_sup_right (by omega))
    have hdiv := Nat.mem_divisors.mpr ⟨hU ▸ card_dvd_of_le hEU, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    have heq : E = U := eq_of_le_of_card_ge hEU (by omega)
    exact hproper (le_of_le_sup_commutator_of_isNilpotent T U C T
      hp.isNilpotent hUT hCT le_rfl hTC heq.ge)
  have hCsmall : Nat.card C ≤ 2 := by
    have hCne : C ≠ A := by
      intro he
      apply hnon
      change ⁅A,T⁆ = ⊥
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [← he]
      exact inf_le_right
    have hlt : Nat.card C < 4 := by
      by_contra! hh
      exact hCne (eq_of_le_of_card_ge hCA (by omega))
    have hdvd : Nat.card C ∣ 4 := hA ▸ card_dvd_of_le hCA
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hKcard : Nat.card K = 2 := by
    have hAne : A ≠ ⊥ := by intro he; have hh := hA; rw [he] at hh; simp at hh
    have hne := commutator_ne_self T A hp (hAU.trans hUT) hAne
    have hlt : Nat.card K < 4 := by
      by_contra! hh
      exact hne (eq_of_le_of_card_ge hKA (by change Nat.card A ≤ Nat.card K; omega))
    have hlo := (one_lt_card_iff_ne_bot K).mpr hnon
    have hdvd : Nat.card K ∣ 4 := hA ▸ card_dvd_of_le hKA
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hKC : K ≤ C := le_inf (hKA.trans hAU)
    (le_centralizer_iff.mp (centralizes_of_normalizes_card_two hKcard
      (commutator_normalized T A hTA)))
  have hDC' : D ≤ C := le_inf hDU hDC
  let : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have hCe : D = C := eq_of_le_of_card_ge hDC' (by omega)
  apply eq_of_le_of_card_ge (hKC.trans hCe.ge)
  omega



variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem edge_kernel_two (source : LocalSource L R) (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) : IsPGroup 2 (Q R b) := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a b).mp hab
  · have hh := Q_act R g (beta R)
    simp only [beta, act_hVertex, one_mul] at hh
    rw [hh]
    change IsPGroup 2 ((neighborhoodKernel R (hVertex R 1)).map _)
    rw [neighborhoodKernel_h_base_eq_Sbar]
    exact (source.two_group.of_surjective (embedS R).rangeRestrict
      (embedS R).rangeRestrict_surjective).map _
  · cases ha

include common in
/-- The transported central line is the actual critical commutator, hence
 belongs to the natural subgroup at the initial endpoint. -/
theorem paired_displacement_le_natural {a b d : Vertex R} {ha : color R a = false}
    (p : SpanOffender.PairedSpans geometry a b d ha) (hab : Adjacent R a b) :
    ⁅Z R p.r,Q R p.e⁆ ≤ U R a := by
  let D := ⁅Z R p.r,Q R p.e⁆
  have hZa : Z R a ≤ Q R p.e := Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha) (by
    rw [p.near, geometry.distance_constant a ha]
    exact common.large_distance)
  have hcomm : ⁅Z R p.r,Z R a⁆ ≤ D := commutator_mono le_rfl hZa
  let : Finite D := Nat.finite_of_card_ne_zero (by have hcard : Nat.card D = 2 := p.card_right; omega)
  let : Finite (⁅Z R p.r,Z R a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hcomm) (inclusion_injective _)
  have hne : ⁅Z R p.r,Z R a⁆ ≠ ⊥ := by
    rw [commutator_comm]
    exact common.critical_noncommutation a ha p.r p.critical
  have heq : ⁅Z R p.r,Z R a⁆ = D := by
    apply eq_of_le_of_card_ge hcomm
    have hh := (one_lt_card_iff_ne_bot _).mpr hne
    have hcard : Nat.card D = 2 := p.card_right
    omega
  change D ≤ U R a
  rw [← heq, commutator_comm]
  exact (commutator_mono le_rfl p.seed_edge).trans
    (edge_commutator_le_natural common a b ha hab)

include common in
/-- The terminal binary contradiction on p.902, conditional only on the
 displayed intersection index. All natural-action and fixed-line calculations
 are proved here; the index comparison remains a separate source argument. -/
theorem edge_containment_of_paired_index (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (p : SpanOffender.PairedSpans geometry a b d ha)
    (hi : (Z R p.e).relIndex (Z R a) = 2) : ⁅Z R a,Q R b⁆ ≤ Z R b := by
  let T := Q R b
  let A := ⁅Z R a,T⁆
  let D := ⁅Z R p.r,Q R p.e⁆
  let H := Z R a ⊓ Z R p.e
  have hTa : T ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hTe : T ≤ stabilizer R p.e := fun _ hx => hx.2 p.e (adjacent_symm R p.edge)
  have hHa : H ≤ Z R a := inf_le_left
  have hTH : T ≤ normalizer H :=
    (le_inf (hTa.trans (Z_normalized R a)) (hTe.trans (Z_normalized R p.e))).trans
      inf_normalizer_le_normalizer_inf
  have hAH : A ≤ H := commutator_le_of_normalized_index_two (Z R a) H T hHa
    (by change (Z R a ⊓ Z R p.e).relIndex (Z R a) = 2; rwa [inf_relIndex_left])
    (hTa.trans (Z_normalized R a)) hTH
  have hU := edge_commutator_le_natural common a b ha hab
  have hC : A ≤ centralizer (T : Set (FreeAmalgam R)) := by
    by_contra hnot
    have hnon : ⁅A,T⁆ ≠ ⊥ := fun hz => hnot (commutator_eq_bot_iff_le_centralizer.mp hz)
    let := finite_stabilizer R b
    let : Finite T := Finite.of_injective
      (inclusion (show T ≤ stabilizer R b from fun _ hx => hx.1)) (inclusion_injective _)
    have hnat : A = ⁅U R a,T⁆ := edge_commutator_eq_natural common a b ha hab
    have hcard : Nat.card (⁅U R a,T⁆ : Subgroup (FreeAmalgam R)) = 4 := by
      rw [← hnat]
      exact Transfer.SpanBound.Sharpening.edge_displacement_card_four common hb initial a b ha hab
    have hD : D ≤ U R a := paired_displacement_le_natural common p hab
    have hDC : D ≤ centralizer (T : Set (FreeAmalgam R)) :=
      p.central_right.trans (centralizer_le hTe)
    have hK : ⁅A,T⁆ = D := by
      rw [hnat]
      apply second_displacement_eq_fixed_line T (U R a) D (edge_kernel_two source a b ha hab)
        ((U_le_Z a).trans (edge_Z_le_Q common a b ha hab))
        (hTa.trans (U_normalized a)) (common.natural.card_at a ha) hcard
        p.card_right hD hDC
      rwa [← hnat]
    have hDUe : D ≤ U R p.e := by
      rw [← hK]
      exact (commutator_mono (hAH.trans inf_le_right) le_rfl).trans
        (edge_commutator_le_natural common p.e b p.he p.edge)
    have hzero : D = ⊥ := le_bot_iff.mp
      ((le_inf hDUe (p.central_right.trans (centralizer_le (Ltilde_le_stabilizer p.e)))).trans
        (Flags.U_fixed_eq_bot common p.e p.he).le)
    have hh : Nat.card D = 2 := p.card_right
    rw [hzero] at hh
    simp at hh
  rw [edge_Z_eq_fixed common a b ha hab]
  exact le_inf (hU.trans (U_le_Z a)) hC

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Terminal
