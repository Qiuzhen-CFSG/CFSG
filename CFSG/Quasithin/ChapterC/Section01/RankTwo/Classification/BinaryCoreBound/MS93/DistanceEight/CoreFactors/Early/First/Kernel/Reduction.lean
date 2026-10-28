module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Calculations

/-!
# Kernel locality and the literal quotient reduction for MS93 (4.5.1)

The endpoint Z-layer lies in the actual local stabilizer at distance eight,
so its image in the quotient by B retains the entire source actor. B is
normal relative to this stabilizer. The setwise product in (ii) forces the
intersection to centralize the endpoint modulo B. Conversely, a pointwise
fixed-element test supplies both B's containment in the intervening kernel
and the reverse quotient inclusion, with exactly the stated quotient map.
The neighboring critical windows also prove the radius-four noncontainment
used for the contradiction at the end of the printed proof of (ii).

The two records below isolate the remaining source calculations. Their
existence is not asserted here: the product bound and the fixed-element test
still require the natural-section and orbit arguments. In particular this
module does not claim a proof of (4.5.1)(ii)--(iii) from Earlier alone.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The quotient kernel is normal in G_a, not in the free amalgam. -/
theorem B_normal (common : CommonFacts R source geometry)
    {a : Vertex R} (ha : color R a = false) :
    ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (Escape.Propagation.Rigidity.B_normalized common.large_distance a ha)

omit [Finite M] in
/-- Both endpoint Z-layers act in the opposite local group, including distance eight. -/
theorem endpoint_local (earlier : Earlier R geometry) {a : Vertex R}
    (p : SourcePath R a) {i j : ℕ} (hi : Even i) (hi14 : i ≤ 14)
    (hj : Even j) (hj14 : j ≤ 14) (hij : i ≤ j) (hd : j - i ≤ 8) :
    Z R (p.walk.getVert j) ≤ stabilizer R (p.walk.getVert i) ∧
      Z R (p.walk.getVert i) ≤ stabilizer R (p.walk.getVert j) := by
  constructor
  · apply geometry.Z_le_stabilizer_of_dist_le_b _ (p.even_color hj hj14)
    rw [earlier.distance, SimpleGraph.dist_comm, p.distance (geometry := geometry) hij hj14]
    exact hd
  · apply geometry.Z_le_stabilizer_of_dist_le_b _ (p.even_color hi hi14)
    rw [earlier.distance, p.distance (geometry := geometry) hij hj14]
    exact hd

private theorem commutator_mem_of_product {G : Type*} [Group G]
    {A Z Q N : Subgroup G} (hAZ : A ≤ normalizer (Z : Set G))
    (hZN : Z ≤ N) (hQA : Q ≤ centralizer (A : Set G))
    {x : G} (hx : x ∈ (Z : Set G) * (Q : Set G)) :
    ∀ a ∈ A, ⁅a, x⁆ ∈ N := by
  obtain ⟨z, hz, q, hq, rfl⟩ := hx
  intro a ha
  have hc : ⁅a, q⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hQA hq a ha)
  rw [commutatorElement_mul_right_eq_mul_conj, hc, mul_one, mul_inv_cancel_right]
  exact hZN (le_normalizer_iff_commutator_le_right.mp hAZ
    (commutator_mem_commutator ha hz))

/-- The literal product bound in (ii) gives fixation by the full endpoint modulo B. -/
theorem product_implies_fixed (common : CommonFacts R source geometry)
    {a e f : Vertex R} (ha : color R a = false) (hf : color R f = false)
    (hfa : Z R f ≤ stabilizer R a)
    (hprod : (V R a ⊓ Q R e : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R)))
    {x : FreeAmalgam R} (hx : x ∈ V R a ⊓ Q R e) :
    ∀ z ∈ Z R f, ⁅z, x⁆ ∈ B R a (geometry.Z_normal a) :=
  commutator_mem_of_product (hfa.trans (Z_normalized R a))
    (Escape.EdgeTransfer.Z_le_B common.large_distance a ha)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes f hf))) (hprod hx)

/-- Assemble one literal kernel calculation from the product bound and its
remaining fixed-element implication. The latter also proves B ≤ Q_e. -/
theorem calculation_of_product_and_detection (common : CommonFacts R source geometry)
    {a e f : Vertex R} (ha : color R a = false) (hf : color R f = false)
    (hfa : Z R f ≤ stabilizer R a)
    (hprod : (V R a ⊓ Q R e : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R)))
    (hdetect : ∀ x ∈ V R a,
      (∀ z ∈ Z R f, ⁅z, x⁆ ∈ B R a (geometry.Z_normal a)) → x ∈ Q R e) :
    KernelCalculation R geometry a e f := by
  have hBV : B R a (geometry.Z_normal a) ≤ V R a :=
    Escape.EdgeTransfer.B_le_radius common.large_distance a ha
  have hBn := B_normal common ha
  let := hBn
  let π := QuotientGroup.mk'
    ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a))
  have fixed_iff (x : stabilizer R a) :
      π x ∈ centralizer (((Z R f).subgroupOf (stabilizer R a)).map π : Set _) ↔
        ∀ z ∈ Z R f, ⁅z, (x : FreeAmalgam R)⁆ ∈ B R a (geometry.Z_normal a) := by
    constructor
    · intro hx z hz
      have hcx : x ∈ centralizerModulo ⊤ ((Z R f).subgroupOf (stabilizer R a))
          ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)) := ⟨mem_top _, hx⟩
      exact (mem_centralizerModulo_iff.mp hcx).2 ⟨z, hfa hz⟩ hz
    · intro hx
      have hcx : x ∈ centralizerModulo ⊤ ((Z R f).subgroupOf (stabilizer R a))
          ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)) :=
        mem_centralizerModulo_iff.mpr ⟨mem_top _, fun z hz => hx z hz⟩
      exact hcx.2
  have hB : B R a (geometry.Z_normal a) ≤ Q R e := by
    intro x hx
    apply hdetect x (hBV hx)
    intro z hz
    exact le_normalizer_iff_commutator_le_right.mp
      (hfa.trans (Escape.Propagation.Rigidity.B_normalized common.large_distance a ha))
      (commutator_mem_commutator hz hx)
  refine ⟨hprod, hB, hBn, ?_⟩
  change ((V R a ⊓ Q R e).subgroupOf (stabilizer R a)).map π =
    ((V R a).subgroupOf (stabilizer R a)).map π ⊓
      centralizer (((Z R f).subgroupOf (stabilizer R a)).map π : Set _)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem π hx.1, (fixed_iff x).mpr ?_⟩
    exact product_implies_fixed common ha hf hfa hprod hx
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact mem_map_of_mem π ⟨hx, hdetect x hx ((fixed_iff x).mp hy)⟩

section Radius
omit [Finite M]

private theorem radius_le_four {a c : Vertex R}
    (hca : (cosetGraph R).dist c a ≤ 2) : V R c ≤ VBall R a 4 := by
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have ht := (cosetGraph_connected R).dist_triangle (u := v) (v := c) (w := a)
  have hd : (cosetGraph R).dist v a ≤ 4 := by omega
  exact le_iSup_of_le v (le_iSup_of_le hd le_rfl)

/-- The neighboring critical window excludes the radius-four trap used at
the end of the printed proof of (ii), in the forward direction. -/
theorem radius_four_not_le_forward (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi6 : i ≤ 6) :
    ¬ VBall R (p.walk.getVert i) 4 ≤ Q R (p.walk.getVert (i + 4)) := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hp := p.critical_pair earlier he (by omega)
  rw [show i - 2 + 8 = i + 6 by omega] at hp
  have hn := common.escape _ (p.even_color he (by omega)) _ hp
    (p.walk.getVert (i + 4))
    (by rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (by rw [p.distance (geometry := geometry) (by omega) (by omega),
      p.distance (geometry := geometry) (by omega) (by omega)]; omega)
  intro h
  apply hn
  exact (radius_le_four
    (by rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)).trans h

/-- The same radius-four contradiction at each reversed source center. -/
theorem radius_four_not_le_backward (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    ¬ VBall R (p.walk.getVert i) 4 ≤ Q R (p.walk.getVert (i - 4)) := by
  have he : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have hf : Even (i + 2) := hi.add (by decide : Even 2)
  have hp := p.critical_pair earlier he (by omega)
  rw [show i - 6 + 8 = i + 2 by omega] at hp
  have hr := common.critical_reverse _ (p.even_color he (by omega)) _
    (p.even_color hf (by omega)) hp
  have hn := common.escape _ (p.even_color hf (by omega)) _ hr
    (p.walk.getVert (i - 4))
    (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (by rw [SimpleGraph.dist_comm (u := p.walk.getVert (i + 2)),
      SimpleGraph.dist_comm (u := p.walk.getVert (i + 2)),
      p.distance (geometry := geometry) (by omega) (by omega),
      p.distance (geometry := geometry) (by omega) (by omega)]; omega)
  intro h
  apply hn
  exact (radius_le_four
    (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)).trans h


end Radius

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The six instances of the source product containment still to prove. -/
structure ProductBoundsOnPath {a : Vertex R} (p : SourcePath R a) : Prop where
  forward : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
    (V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i + 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
    (V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i - 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i - 8)) : Set (FreeAmalgam R))

/-- The remaining fixed-element implication in (iii), conditional on (ii).
Its producer may use the supplied product containment without waiting for it. -/
structure FixedPointDetectionOnPath (geometry : Geometry R) {a : Vertex R}
    (p : SourcePath R a) : Prop where
  forward : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
    ((V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i + 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))) →
    ∀ x ∈ V R (p.walk.getVert i),
      (∀ z ∈ Z R (p.walk.getVert (i + 8)),
        ⁅z, x⁆ ∈ B R (p.walk.getVert i) (geometry.Z_normal _)) →
      x ∈ Q R (p.walk.getVert (i + 6))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
    ((V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i - 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i - 8)) : Set (FreeAmalgam R))) →
    ∀ x ∈ V R (p.walk.getVert i),
      (∀ z ∈ Z R (p.walk.getVert (i - 8)),
        ⁅z, x⁆ ∈ B R (p.walk.getVert i) (geometry.Z_normal _)) →
      x ∈ Q R (p.walk.getVert (i - 6))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
