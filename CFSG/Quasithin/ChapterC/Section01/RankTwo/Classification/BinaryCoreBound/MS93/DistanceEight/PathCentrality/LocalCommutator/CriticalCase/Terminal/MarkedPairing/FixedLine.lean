module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Source
public import Theory.GroupAction.SubgroupConjugation

/-!
# Critical commutators and the fixed subgroup of the first edge

The marked natural-module calculation gives equal critical Z-image indices.
If the image has order four, its kernel in the opposite natural group has
order two and equals the critical commutator. The actual first odd-vertex
kernel is a two-group containing the endpoint Z-layer. Its action on the
natural group has a nonidentity fixed point, so its fixed subgroup is exactly
that commutator. No arbitrary line or replacement action is used.

The same order-eight calculation restricts every critical image to order two
or four. It does not exclude the order-two case for a selected terminal pair.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.5), pp.869--870, applied in (4.4.1), p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem fixed_nontrivial {G : Type*} [Group G]
    (U T : Subgroup G) [Finite U] (hcard : Nat.card U = 8)
    (hn : T ≤ normalizer (U : Set G)) (hT : IsPGroup 2 T) :
    U ⊓ centralizer (T : Set G) ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Subgroup.Normalizes T U := ⟨hn⟩
  obtain ⟨u, hu, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point U
    (by rw [hcard]; decide) (show (1 : U) ∈ MulAction.fixedPoints T U by simp)
  intro hbot
  have hfix : (u : G) ∈ U ⊓ centralizer (T : Set G) := by
    refine ⟨u.property, ?_⟩
    intro t ht
    have h := congrArg Subtype.val (hu (⟨t, ht⟩ : T))
    change t * (u : G) * t⁻¹ = u at h
    exact mul_inv_eq_iff_eq_mul.mp h
  rw [hbot, mem_bot] at hfix
  exact hne (Subtype.ext hfix.symm)

/-- Reciprocity on the literal Z images. -/
theorem critical_Z_index_reciprocity (common : CommonFacts R source geometry)
    {x y : Vertex R} (p : CriticalPath R geometry x y) :
    (Q R y).relIndex (Z R x) = (Q R x).relIndex (Z R y) := by
  let s := naturalStructure common
  rw [s.critical_Z_index_eq_U geometry x p.start_color y p.critical,
    s.critical_Z_index_eq_U geometry y p.end_color x (p.reverse common).critical]
  exact s.critical_U_index geometry common.large_distance x p.start_color y p.critical

/-- The natural critical commutator lies in the opposite kernel. -/
theorem critical_commutator_le_natural_kernel (common : CommonFacts R source geometry)
    {x y : Vertex R} (p : CriticalPath R geometry x y) :
    ⁅Z R x, Z R y⁆ ≤ U R x ⊓ Q R y := by
  let s := naturalStructure common
  rw [s.critical_commutator_eq geometry x p.start_color y p.critical]
  obtain ⟨hxy, hyx⟩ := source.critical_U_mutually_normalize geometry x p.start_color y p.critical
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hyx)
    ((le_normalizer_iff_commutator_le_right.mp hxy).trans
      ((U_le_Z R y).trans (Z_le_Q_of_dist_lt R y (geometry.exists_critical y p.end_color)
        (by rw [geometry.distance_constant y p.end_color]; simp only [SimpleGraph.dist_self];
            have := common.large_distance; change 0 < geometry.b R; omega))))

/-- The critical centralizer in U is the commutator when the actual image has order four. -/
theorem critical_natural_intersection (common : CommonFacts R source geometry)
    {x y : Vertex R} (p : CriticalPath R geometry x y)
    (hi : (Q R x).relIndex (Z R y) = 4) :
    U R x ⊓ Q R y = ⁅Z R x, Z R y⁆ := by
  let s := naturalStructure common
  let : Finite (U R x) := Nat.finite_of_card_ne_zero (by rw [s.natural.card_at x p.start_color]; decide)
  let : Finite (U R x ⊓ Q R y : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (show U R x ⊓ Q R y ≤ U R x from inf_le_left))
      (inclusion_injective _)
  have hindex : (Q R y).relIndex (U R x) = 4 := by
    rw [← s.critical_Z_index_eq_U geometry x p.start_color y p.critical,
      critical_Z_index_reciprocity common p, hi]
  have hprod := ((Q R y).subgroupOf (U R x)).index_mul_card
  have hcard : Nat.card (U R x ⊓ Q R y : Subgroup (FreeAmalgam R)) = 2 := by
    rw [s.natural.card_at x p.start_color] at hprod
    change (Q R y).relIndex (U R x) * _ = 8 at hprod
    rw [hindex, ← inf_subgroupOf_right (Q R y) (U R x),
      Nat.card_congr (subgroupOfEquivOfLe (show Q R y ⊓ U R x ≤ U R x from inf_le_right)).toEquiv,
      inf_comm] at hprod
    omega
  have hle := critical_commutator_le_natural_kernel common p
  exact (eq_of_le_of_card_ge hle (by rw [hcard, critical_commutator_card common p])).symm

/-- The fixed subgroup uses the first actual odd-vertex kernel on a geodesic. -/
theorem critical_commutator_eq_edgeFixedNatural (common : CommonFacts R source geometry)
    (_hb : 4 < geometry.b R) {x y : Vertex R} (p : CriticalPath R geometry x y)
    {t : Vertex R} (hxt : Adjacent R x t)
    (hty : (cosetGraph R).dist t y + 1 = (cosetGraph R).dist x y)
    (hi : (Q R x).relIndex (Z R y) = 4) :
    ⁅Z R x, Z R y⁆ = edgeFixedNatural x t := by
  let s := naturalStructure common
  let : Finite (U R x) := Nat.finite_of_card_ne_zero (by rw [s.natural.card_at x p.start_color]; decide)
  let : Finite (edgeFixedNatural (R := R) x t) :=
    Finite.of_injective (inclusion (show edgeFixedNatural (R := R) x t ≤ U R x from inf_le_left))
      (inclusion_injective _)
  have hYT : Z R y ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R y (geometry.exists_critical y p.end_color)
    rw [geometry.distance_constant y p.end_color, SimpleGraph.dist_comm]
    have hdist := p.shortest.symm.trans p.length_eq_b
    change (cosetGraph R).dist t y < geometry.b R
    omega
  have hTG : Q R t ≤ stabilizer R x := fun _ ht => ht.2 x (adjacent_symm R hxt)
  have hfixed : edgeFixedNatural (R := R) x t ≤ U R x ⊓ Q R y := by
    refine le_inf inf_le_left ?_
    rw [← s.natural.centralizer y p.end_color]
    exact le_inf (inf_le_left.trans ((U_le_Z R x).trans
      (source.critical_Z_le_stabilizer geometry x p.start_color y p.critical).1))
      (inf_le_right.trans (centralizer_le ((U_le_Z R y).trans hYT)))
  rw [critical_natural_intersection common p hi] at hfixed
  have hne : edgeFixedNatural (R := R) x t ≠ ⊥ :=
    fixed_nontrivial (U R x) (Q R t) (s.natural.card_at x p.start_color)
      (hTG.trans (U_normalized x)) (Escape.EdgeTransfer.edge_kernel_two source x t p.start_color hxt)
  let : Finite (⁅Z R x, Z R y⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [critical_commutator_card common p]; decide)
  exact (eq_of_le_of_card_ge hfixed (by
    rw [critical_commutator_card common p]
    exact (one_lt_card_iff_ne_bot _).mpr hne)).symm

/-- The fixed subgroup has order two, at the specified first edge. -/
theorem critical_edgeFixedNatural_card (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {x y : Vertex R} (p : CriticalPath R geometry x y)
    {t : Vertex R} (hxt : Adjacent R x t)
    (hty : (cosetGraph R).dist t y + 1 = (cosetGraph R).dist x y)
    (hi : (Q R x).relIndex (Z R y) = 4) :
    Nat.card (edgeFixedNatural (R := R) x t) = 2 := by
  rw [← critical_commutator_eq_edgeFixedNatural common hb p hxt hty hi]
  exact critical_commutator_card common p

/-- Only the two nontrivial binary image orders can occur. -/
theorem critical_Z_index_two_or_four (common : CommonFacts R source geometry)
    {x y : Vertex R} (p : CriticalPath R geometry x y) :
    (Q R y).relIndex (Z R x) = 2 ∨ (Q R y).relIndex (Z R x) = 4 := by
  let s := naturalStructure common
  let : Finite (U R x) := Nat.finite_of_card_ne_zero (by rw [s.natural.card_at x p.start_color]; decide)
  let : Finite (U R x ⊓ Q R y : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (show U R x ⊓ Q R y ≤ U R x from inf_le_left))
      (inclusion_injective _)
  have hge : 2 ≤ Nat.card (U R x ⊓ Q R y : Subgroup (FreeAmalgam R)) := by
    rw [← critical_commutator_card common p]
    exact card_le_of_le (critical_commutator_le_natural_kernel common p)
  have hindex := s.critical_Z_index_eq_U geometry x p.start_color y p.critical
  have hprod := ((Q R y).subgroupOf (U R x)).index_mul_card
  change (Q R y).relIndex (U R x) * _ = _ at hprod
  rw [← hindex, s.natural.card_at x p.start_color,
    ← inf_subgroupOf_right (Q R y) (U R x),
    Nat.card_congr (subgroupOfEquivOfLe (show Q R y ⊓ U R x ≤ U R x from inf_le_right)).toEquiv,
    inf_comm] at hprod
  have hpos : 0 < (Q R y).relIndex (Z R x) := by nlinarith
  have hbound : (Q R y).relIndex (Z R x) ≤ 4 := by nlinarith
  have hne : (Q R y).relIndex (Z R x) ≠ 1 := fun hi => p.critical.2 (relIndex_eq_one.mp hi)
  have hdvd : (Q R y).relIndex (Z R x) ∣ 8 := ⟨_, hprod.symm⟩
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
