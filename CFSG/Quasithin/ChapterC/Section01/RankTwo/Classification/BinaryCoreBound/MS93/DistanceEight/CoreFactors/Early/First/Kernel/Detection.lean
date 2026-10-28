module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation

/-!
# Endpoint fixation detects the kernel in MS93 (4.5.1)(iii)

Clause (i) bounds the index of V_a intersect Q_e in V_a by two. The literal
product containment from (ii) places this intersection in the subgroup
fixed by Z_f modulo B_a. That fixed subgroup is proper: otherwise the
faithful natural coordinates on V_a/B_a would put all of Z_f in Q_a,
contradicting the reversed critical pair. Multiplicativity of indices
therefore identifies the fixed subgroup with the kernel intersection.

The natural coordinates come from Earlier.natural_section, with the
original two-residual and literal B_a. The final theorem supplies every
forward and reversed field of FixedPointDetectionOnPath. Product bounds
remain explicit field premises, as required by the independent assembly.
No B_a containment or quotient-centralizer equality is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), notation on printed p.881
and (4.5.1)(i)--(iii), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection
open Escape.PairingControl.FirstPairing.Orientation.ImageCases

private theorem fixed_preimage_le_of_small_index {G : Type*} [Group G] [Finite G]
    {π : G →* SL} {H N K J : Subgroup G} [N.Normal]
    (n : RankOnePairing.NaturalFactor π ⊤ H N)
    (hKH : K ≤ H) (hindex : K.relIndex H ≤ 2) (hJ : ¬ J ≤ π.ker)
    (hfix : ∀ x ∈ K, ∀ z ∈ J, ⁅z, x⁆ ∈ N) :
    centralizerModulo H J N ≤ K := by
  let C := centralizerModulo H J N
  have hCH : C ≤ H := centralizerModulo_le _ _ _
  have hKC : K ≤ C := fun x hx => mem_centralizerModulo_iff.mpr ⟨hKH hx, hfix x hx⟩
  have hproper : ¬ H ≤ C := by
    intro h
    apply hJ
    apply natural_actor_le_kernel n J
    exact commutator_le.mpr (fun z hz x hx => (mem_centralizerModulo_iff.mp (h hx)).2 z hz)
  have hne : C.relIndex H ≠ 1 := fun h => hproper (relIndex_eq_one.mp h)
  have hpos : 0 < C.relIndex H := Nat.pos_of_ne_zero (show (C.subgroupOf H).index ≠ 0 from index_ne_zero_of_finite)
  have hKpos : 0 < K.relIndex C := Nat.pos_of_ne_zero (show (K.subgroupOf C).index ≠ 0 from index_ne_zero_of_finite)
  have hmul := relIndex_mul_relIndex K C H hKC hCH
  have htwo : 2 ≤ C.relIndex H := by omega
  have hsmall : K.relIndex C ≤ 1 := by nlinarith
  exact relIndex_eq_one.mp (show K.relIndex C = 1 by omega)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Faithfulness makes the endpoint fixed subgroup proper; the product bound
identifies it with the kernel intersection once that intersection has index at most two. -/
theorem fixed_implies_kernel_of_index_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a e f : Vertex R}
    (ha : color R a = false) (hf : color R f = false)
    (hfa : Z R f ≤ stabilizer R a) (hcritical : ¬ Z R f ≤ Q R a)
    (hindex : (Q R e).relIndex (V R a) ≤ 2)
    (hprod : (V R a ⊓ Q R e : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R)))
    {x : FreeAmalgam R} (hx : x ∈ V R a)
    (hfixed : ∀ z ∈ Z R f, ⁅z, x⁆ ∈ B R a (geometry.Z_normal a)) : x ∈ Q R e := by
  obtain ⟨s⟩ := earlier.natural_section a ha
  let G := stabilizer R a
  let H := (V R a).subgroupOf G
  let N := (B R a (geometry.Z_normal a)).subgroupOf G
  let K := (V R a ⊓ Q R e).subgroupOf G
  let J := (Z R f).subgroupOf G
  let := finite_stabilizer R a
  let : N.Normal := B_normal common ha
  let n := natural_coordinates_at source common.large_distance ha s
  have hi : K.relIndex H ≤ 2 := by
    rwa [relIndex_subgroupOf s.local_group, inf_relIndex_left]
  have hJ : ¬ J ≤ s.projection.ker := by
    rw [s.module_section.projection_kernel]
    intro h
    apply hcritical
    intro z hz
    exact h (show (⟨z, hfa hz⟩ : G) ∈ J from hz)
  have hle := fixed_preimage_le_of_small_index n (show K ≤ H from comap_mono inf_le_left)
    hi hJ (fun y hy z hz => product_implies_fixed common ha hf hfa hprod hy z hz)
  have hxC : (⟨x, s.local_group hx⟩ : G) ∈ centralizerModulo H J N :=
    mem_centralizerModulo_iff.mpr ⟨hx, fun z hz => hfixed z hz⟩
  exact (hle hxC).2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Endpoint fixation detects the intervening kernel in every forward and
reversed source window, conditional only on that window's literal product bound. -/
theorem fixedPointDetectionOnPath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    FixedPointDetectionOnPath R geometry p := by
  constructor
  · intro i hi hi2 hi6 hprod x hx hfixed
    have ha := p.even_color hi (by omega)
    have he := p.even_color (hi.add (by decide : Even 6)) (by omega)
    have hf := p.even_color (hi.add (by decide : Even 8)) (by omega)
    have hlocal := (endpoint_local earlier p hi (by omega)
      (hi.add (by decide : Even 8)) (by omega) (by omega) (by omega)).1
    have hcritical := (common.critical_reverse _ ha _ hf (p.critical_pair earlier hi hi6)).2
    have hindex := Detection.radius_kernel_index_le_two common earlier ha he
      (show Adjacent R (p.walk.getVert (i + 6)) (p.walk.getVert (i + 5)) from
        adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega)))
      (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i + 5)) = 5 by
        rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
      (show (cosetGraph R).dist (p.walk.getVert (i + 6)) (p.walk.getVert (i + 4)) ≤ 2 by
        rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
      (p.first_commutator source common earlier hi hi2 (by omega)).2
    exact Detection.fixed_implies_kernel_of_index_le_two common earlier ha hf
      hlocal hcritical hindex hprod hx hfixed
  · intro i hi hi8 hi12 hprod x hx hfixed
    have heven (k : ℕ) (hk : Even k) (hki : k ≤ i) : Even (i - k) := by
      rw [Nat.even_iff] at hi hk ⊢; omega
    have ha := p.even_color hi (by omega)
    have he := p.even_color (heven 6 (by decide) (by omega)) (by omega)
    have hf := p.even_color (heven 8 (by decide) hi8) (by omega)
    have hlocal := (endpoint_local earlier p (heven 8 (by decide) hi8) (by omega)
      hi (by omega) (by omega) (by omega)).2
    have hcritical : ¬ Z R (p.walk.getVert (i - 8)) ≤ Q R (p.walk.getVert i) := by
      have hh := p.critical_pair earlier (heven 8 (by decide) hi8) (by omega)
      simpa only [Nat.sub_add_cancel hi8] using hh.2
    have hindex := Detection.radius_kernel_index_le_two common earlier ha he
      (show Adjacent R (p.walk.getVert (i - 6)) (p.walk.getVert (i - 5)) from
        by simpa only [show i - 6 + 1 = i - 5 by omega] using
          p.adjacent (i := i - 6) (by omega))
      (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i - 5)) = 5 by
        rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
      (show (cosetGraph R).dist (p.walk.getVert (i - 6)) (p.walk.getVert (i - 4)) ≤ 2 by
        rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
      (p.first_commutator_backward source common earlier hi hi8 hi12).2
    exact Detection.fixed_implies_kernel_of_index_le_two common earlier ha hf
      hlocal hcritical hindex hprod hx hfixed

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel
