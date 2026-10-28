module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Intersections.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Numerical

/-!
# The first commutator intersection of MS93 (4.5.1)

Centrality collapses the commutator of a moving orbit span to its initial
displacement. Hence H at either endpoint lies in the midpoint's natural
group. It also lies in every incident edge Z-layer. Two distinct incident
Z-layers cut the natural group of order eight in distinct proper subgroups,
so their intersection has order at most two. The neighboring critical
window makes the radius commutator nontrivial, giving equality and order two.

These calculations apply to a supplied SourcePath, whose existence remains
explicit. They do not assume any of the other clauses of FirstFacts.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(i), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Centrality puts H in each incident odd-color Z-layer. -/
theorem H_le_edge_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) : H R a ≤ Z R t := by
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha hat]
  refine le_inf (H_le_Z_of_central common ha (earlier.centrality a ha)) ?_
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := H_le_localCenter_of_central R a (earlier.centrality a ha) hx
  exact congrArg Subtype.val (mem_center_iff.mp hz
    ⟨y, hy.2 a (adjacent_symm R hat)⟩)

omit [Finite M] in
/-- The moving span places H in the initial displacement, without a cardinal assumption. -/
theorem H_le_displacement (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2) (hspan : Vcirc R a ≤ hatV R a c) :
    H R a ≤ ⁅Z R c, Q R a⁆ := by
  let K := ⁅Z R c, Q R a⁆
  have hKC : K ≤ (center (stabilizer R a)).map (stabilizer R a).subtype :=
    (commutator_mono
      ((Z_le_localZSpan R c a).trans (localZSpan_le_V R hca.le)) le_rfl).trans
        (earlier.centrality a ha)
  have hKcentral : K ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hKC hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
  have hKn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hKcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal : ⁅localZSpan R c a, Q R a⁆ = K := by
    rw [span_commutator_eq_conjugates (geometry := geometry) ha hca.le common.large_distance]
    exact Escape.PairingControl.conjugatesIn_eq_of_normalized K (stabilizer R a) hKn
  exact (commutator_mono hspan le_rfl).trans hlocal.le

/-- In particular, H lies in the natural subgroup at the moving neighbor. -/
theorem H_le_neighbor_U (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2) (hspan : Vcirc R a ≤ hatV R a c) :
    H R a ≤ U R c :=
  (H_le_displacement common earlier ha hca hspan).trans
    (displacement_le_U common ((color_eq_of_dist_even R c a (by rw [hca]; decide)).trans ha) hca)

private theorem proper_subgroup_card_le_four {G : Type*} [Group G]
    {U A : Subgroup G} [Finite U] (hU : Nat.card U = 8) (hAU : A ≤ U) (hne : A ≠ U) :
    Nat.card A ≤ 4 := by
  have hlt : Nat.card A < 8 := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hAU (by rwa [hU]))
  have hdiv := Nat.mem_divisors.mpr ⟨hU ▸ card_dvd_of_le hAU, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

/-- Distinct printed edge Z-layers cut the actual natural group in at most a line. -/
theorem edge_natural_intersection_card_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {c s t : Vertex R} (hc : color R c = false)
    (hcs : Adjacent R c s) (hct : Adjacent R c t) (hne : Z R s ≠ Z R t) :
    Nat.card (U R c ⊓ Z R s ⊓ Z R t : Subgroup (FreeAmalgam R)) ≤ 2 := by
  let F := Z R c ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R))
  have hsplit : Z R c = U R c ⊔ F := (naturalStructure common).decomposition_at c hc
  have hprod : (Z R c : Set (FreeAmalgam R)) =
      (U R c : Set (FreeAmalgam R)) * (F : Set (FreeAmalgam R)) := by
    rw [hsplit]
    apply coe_mul_of_left_le_normalizer_right
    exact ((U_le_Z R c).trans (Z_le_stabilizer R c)).trans
      ((le_centralizer_iff.mp (show F ≤ centralizer (stabilizer R c : Set (FreeAmalgam R)) from
        inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))
  have hF (v : Vertex R) (hcv : Adjacent R c v) : F ≤ Z R v := by
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) c v hc hcv]
    exact le_inf inf_le_left
      (inf_le_right.trans (centralizer_le (fun _ hx => hx.2 c (adjacent_symm R hcv))))
  have hdecomp (v : Vertex R) (hcv : Adjacent R c v) :
      Z R v = (U R c ⊓ Z R v) ⊔ F := by
    apply le_antisymm _ (sup_le inf_le_right (hF v hcv))
    intro x hx
    have hxZ := Escape.EdgeTransfer.edge_Z_le c v hc hcv hx
    change x ∈ (Z R c : Set (FreeAmalgam R)) at hxZ
    rw [hprod] at hxZ
    obtain ⟨u, hu, f, hf, rfl⟩ := hxZ
    have huZ : u ∈ Z R v := by
      have hh := (Z R v).mul_mem hx ((Z R v).inv_mem (hF v hcv hf))
      simpa only [mul_inv_cancel_right] using hh
    exact ((U R c ⊓ Z R v) ⊔ F).mul_mem
      ((show U R c ⊓ Z R v ≤ (U R c ⊓ Z R v) ⊔ F from le_sup_left) ⟨hu, huZ⟩)
      ((show F ≤ (U R c ⊓ Z R v) ⊔ F from le_sup_right) hf)
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at c hc]; decide)
  have hproper (v : Vertex R) (hcv : Adjacent R c v) : U R c ⊓ Z R v ≠ U R c := by
    intro he
    have hz : Z R v = Z R c := by rw [hdecomp v hcv, he, ← hsplit]
    have hindex := earlier.edge_Z_index c v hc hcv
    rw [hz, relIndex_self] at hindex
    omega
  have hsmall (v : Vertex R) (hcv : Adjacent R c v) :
      Nat.card (U R c ⊓ Z R v : Subgroup (FreeAmalgam R)) ≤ 4 :=
    proper_subgroup_card_le_four (common.natural.card_at c hc) inf_le_left (hproper v hcv)
  let K := U R c ⊓ Z R s ⊓ Z R t
  have hKU : K ≤ U R c := inf_le_left.trans inf_le_left
  have hKs : K ≤ U R c ⊓ Z R s := inf_le_left
  have hKt : K ≤ U R c ⊓ Z R t := le_inf hKU inf_le_right
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  let : Finite (U R c ⊓ Z R s : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite (U R c ⊓ Z R t : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hlt : Nat.card K < 4 := by
    by_contra! h
    have hs := eq_of_le_of_card_ge hKs ((hsmall s hcs).trans h)
    have ht := eq_of_le_of_card_ge hKt ((hsmall t hct).trans h)
    apply hne
    rw [hdecomp s hcs, hdecomp t hct, ← hs, ← ht]
  have hdiv := Nat.mem_divisors.mpr
    ⟨(common.natural.card_at c hc) ▸ card_dvd_of_le hKU, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  change Nat.card K ≤ 2
  omega

namespace SourcePath
variable {a : Vertex R}

omit [Finite M] in
/-- The neighboring critical window witnesses noncommutation of the two radii. -/
theorem commutator_ne_bot (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi8 : i ≤ 8) :
    ⁅V R (p.walk.getVert i), V R (p.walk.getVert (i + 4))⁆ ≠ ⊥ := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hp := p.critical_pair earlier he (by omega)
  have hn := common.critical_noncommutation _ (p.even_color he (by omega)) _ hp
  have hlast : i - 2 + 8 = i + 6 := by omega
  rw [hlast] at hn
  have hl : Z R (p.walk.getVert (i - 2)) ≤ V R (p.walk.getVert i) :=
    le_iSup_of_le _ (le_iSup_of_le
      (by rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega) le_rfl)
  have hr : Z R (p.walk.getVert (i + 6)) ≤ V R (p.walk.getVert (i + 4)) :=
    le_iSup_of_le _ (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega) le_rfl)
  intro hz
  exact hn (le_bot_iff.mp ((commutator_mono hl hr).trans hz.le))

/-- Clause (4.5.1)(i), for every forward pair needed directly or by reversal. -/
theorem first_commutator (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi8 : i ≤ 8) :
    ⁅V R (p.walk.getVert i), V R (p.walk.getVert (i + 4))⁆ =
        H R (p.walk.getVert i) ⊓ H R (p.walk.getVert (i + 4)) ∧
      Nat.card (⁅V R (p.walk.getVert i), V R (p.walk.getVert (i + 4))⁆ :
        Subgroup (FreeAmalgam R)) = 2 := by
  have hc := p.even_color hi (by omega)
  have hd := p.even_color (hi.add (by decide : Even 4)) (by omega)
  have hm := p.even_color (hi.add (by decide : Even 2)) (by omega)
  have hleft := H_le_neighbor_U common earlier hc
    (show (cosetGraph R).dist (p.walk.getVert (i + 2)) (p.walk.getVert i) = 2 by
      rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (p.moving_spans source common earlier hi hi2 (by omega)).2
  have hs : Adjacent R (p.walk.getVert (i + 2)) (p.walk.getVert (i + 1)) :=
    adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  have ht := p.adjacent (i := i + 2) (by omega)
  have hne : Z R (p.walk.getVert (i + 1)) ≠ Z R (p.walk.getVert (i + 3)) := by
    simpa only [show i + 2 - 1 = i + 1 by omega, Nat.add_assoc] using
      p.edge_Z_ne (i + 2) (hi.add (by decide : Even 2)) (by omega) (by omega)
  let K := H R (p.walk.getVert i) ⊓ H R (p.walk.getVert (i + 4))
  let E := U R (p.walk.getVert (i + 2)) ⊓ Z R (p.walk.getVert (i + 1)) ⊓
    Z R (p.walk.getVert (i + 3))
  have hKE : K ≤ E := by
    apply le_inf
    · exact le_inf (inf_le_left.trans hleft)
        (inf_le_left.trans (H_le_edge_Z common earlier hc (p.adjacent (by omega))))
    · apply inf_le_right.trans
      apply H_le_edge_Z common earlier hd
      exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 3) (by omega))
  let : Finite (U R (p.walk.getVert (i + 2))) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at _ hm]; decide)
  let : Finite E := Finite.of_injective (inclusion (inf_le_left.trans inf_le_left))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKE) (inclusion_injective _)
  have hKcard : Nat.card K ≤ 2 := (card_le_of_le hKE).trans
    (edge_natural_intersection_card_le_two common earlier hm hs ht hne)
  let D := ⁅V R (p.walk.getVert i), V R (p.walk.getVert (i + 4))⁆
  have hDK : D ≤ K := radius_commutator_le_intersection source earlier hc hd
    (by rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
  let : Finite D := Finite.of_injective (inclusion hDK) (inclusion_injective _)
  have hDpos : 1 < Nat.card D := (one_lt_card_iff_ne_bot D).mpr
    (p.commutator_ne_bot common earlier hi hi2 hi8)
  have hDcard : Nat.card D = 2 := by have := card_le_of_le hDK; omega
  have heq : D = K := eq_of_le_of_card_ge hDK (by rw [hDcard]; exact hKcard)
  exact ⟨heq, hDcard⟩

/-- The reversed applications use the same subgroups and commutator convention. -/
theorem first_commutator_backward (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    ⁅V R (p.walk.getVert i), V R (p.walk.getVert (i - 4))⁆ =
        H R (p.walk.getVert i) ⊓ H R (p.walk.getVert (i - 4)) ∧
      Nat.card (⁅V R (p.walk.getVert i), V R (p.walk.getVert (i - 4))⁆ :
        Subgroup (FreeAmalgam R)) = 2 := by
  have he : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  have hh := p.first_commutator source common earlier he (by omega) (by omega)
  simpa only [show i - 4 + 4 = i by omega, commutator_comm,
    inf_comm] using hh

end SourcePath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
