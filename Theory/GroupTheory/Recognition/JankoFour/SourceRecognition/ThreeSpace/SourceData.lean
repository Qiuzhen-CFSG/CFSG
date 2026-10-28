module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreJoin

/-!
# Constructing the source three-space and its seven cores

`source_three_space_data` constructs all displayed data from `IsTypeJ4`,
for the specified original full cubic quotient and its chosen Sylow subgroup.
The construction selects the returning first-class marker, lifts the original
cubic scalar, and uses the proved commutator, triple intersection and normalizer
fusion theorems. No geometry witness is an additional source assumption.

The resulting K is exactly the join of original conjugate cores whose centers
lie in Z. It lies in N_G(Z) and is relatively normal there. The record records
only the proved (4.3) and initial (4.4) conclusions; its existence is proved
here, while the special-core, tensor and point-group constructions remain
separate obligations.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.3)(2) and the definition of K in (4.4), p.597,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open VectorOrbits
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Constructed source data, with the original cubic quotient and Sylow
retained as parameters. This record is not assumed by the recognition input. -/
structure ThreeSpaceData (z : G)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) where
  r : G
  s : G
  r_conj : IsConj z r
  s_conj : IsConj z s
  r_ne : r ≠ z
  s_ne : s ≠ z
  distinct : r ≠ s
  r_mem : r ∈ ambientCore z
  s_mem : s ∈ ambientCore z
  elementary : IsElementaryAbelian 2 (ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G)
  card : Nat.card (ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G) = 8
  generated : (ambientCore z ⊓ ambientCore r ⊓ ambientCore s) = closure ({z,r,s} : Set G)
  cubic_commutator : (ambientCore z ⊓ ambientCore r ⊓ ambientCore s) =
    zpowers z ⊔ ⁅zpowers r,(cubicSylowImage e X).map (centralizer z).subtype⁆
  cubic_normalizes : (cubicSylowImage e X).map (centralizer z).subtype ≤
    normalizer ((ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G) : Set G)
  normalizer_transitive : ∀ t ∈ (ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G),
    t ≠ 1 → ∃ n ∈ normalizer ((ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G) : Set G),
      n*z*n⁻¹=t
  contained_in_cores : ∀ t ∈ (ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G),
    t ≠ 1 → (ambientCore z ⊓ ambientCore r ⊓ ambientCore s) ≤ ambientCore t
  cores_normalize : ∀ t ∈ (ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G),
    t ≠ 1 → ambientCore t ≤
      normalizer ((ambientCore z ⊓ ambientCore r ⊓ ambientCore s : Subgroup G) : Set G)

namespace ThreeSpaceData
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}

def space (d : ThreeSpaceData z e X) : Subgroup G :=
  ambientCore z ⊓ ambientCore d.r ⊓ ambientCore d.s

def K (d : ThreeSpaceData z e X) : Subgroup G := threeSpaceCores d.space

theorem K_le_normalizer (d : ThreeSpaceData z e X) : K d ≤ normalizer (d.space : Set G) :=
  threeSpaceCores_le_normalizer d.space d.cores_normalize

theorem K_normal (d : ThreeSpaceData z e X) :
    ((K d).subgroupOf (normalizer (d.space : Set G))).Normal :=
  threeSpaceCores_normal_in_normalizer d.space

theorem K_eq_conjugate_join (h : IsTypeJ4 z) (d : ThreeSpaceData z e X) :
    K d = ⨆ g : {g : G // MulAut.conj g z ∈ d.space},
      (ambientCore z).map (MulAut.conj g.val).toMonoidHom := by
  apply threeSpaceCores_eq_conjugate_join h d.space
  intro t ht ht1
  obtain ⟨n,_,he⟩ := d.normalizer_transitive t ht ht1
  exact isConj_iff.mpr ⟨n,he⟩

end ThreeSpaceData

/-- Construct every displayed field from the intrinsic source hypotheses,
for any supplied full cubic quotient and its original cubic Sylow. -/
theorem source_three_space_data (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) : Nonempty (ThreeSpaceData z e X) := by
  let := h.extraspecial
  obtain ⟨r,_,_,_,hrc,_,hmark,_,_⟩ := source_involution_orbit_cover h e X
  obtain ⟨g,w,hw,hwne⟩ := h.exists_returning_conjugate
  have hwc : IsConj z ((w : centralizer z) : G) := isConj_iff.mpr ⟨g,hw.symm⟩
  have hl := returning_label_four h e X w hwc hwne
  have hc : IsConj (r : centralizer z) (w : centralizer z) :=
    core_isConj_of_label h e X r w hrc (by rw [hmark,VectorOrbits.label_decode,hl]; rfl)
  have hr : IsConj z ((r : centralizer z) : G) :=
    hwc.trans ((centralizer z).subtype.map_isConj hc.symm)
  have hne : ((r : centralizer z) : G) ≠ z := by
    intro he
    apply hrc
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    apply Subtype.ext
    change ((q : centralizer z) : G) * ((r : centralizer z) : G) =
      ((r : centralizer z) : G) * ((q : centralizer z) : G)
    rw [he]
    exact mem_centralizer_singleton_iff.mp (q : centralizer z).property
  obtain ⟨a,haX,ha⟩ := exists_scalar_lift h e X
  let s : core z := MulAut.conjNormal a⁻¹ r
  have hs : IsConj z ((s : centralizer z) : G) :=
    hr.trans (isConj_iff.mpr ⟨(a : G)⁻¹,by simp [s]⟩)
  have hR : ((r : centralizer z) : G) ∈ ambientCore z := mem_map_of_mem _ r.property
  have hS : ((s : centralizer z) : G) ∈ ambientCore z := mem_map_of_mem _ s.property
  have h8 : Nat.card (ambientCore z ⊓ ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((s : centralizer z) : G) : Subgroup G) = 8 :=
    by simpa [s] using (triple_core_card h e X r hr hne hmark a ha)
  have h128 := (returning_intersection_image_orders h hr hR hne).1
  have hsne : ((s : centralizer z) : G) ≠ z := by
    intro he
    rw [he,inf_eq_left.mpr inf_le_left] at h8
    change Nat.card (returningIntersection z ((r : centralizer z) : G)) = 8 at h8
    omega
  have hrs : ((r : centralizer z) : G) ≠ ((s : centralizer z) : G) := by
    intro he
    rw [← he,inf_assoc,inf_idem] at h8
    change Nat.card (returningIntersection z ((r : centralizer z) : G)) = 8 at h8
    omega
  let := returningIntersection_elementary h hr hne
  have hel : IsElementaryAbelian 2 (ambientCore z ⊓ ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((s : centralizer z) : G) : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have heZ : ambientScalarPlane h e X = ambientCore z ⊓ ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((s : centralizer z) : G) := by
    simpa [s] using ambientScalarPlane_eq_triple h e X r hr hne hmark a ha
  refine ⟨{
    r := ((r : centralizer z) : G)
    s := ((s : centralizer z) : G)
    r_conj := hr
    s_conj := hs
    r_ne := hne
    s_ne := hsne
    distinct := hrs
    r_mem := hR
    s_mem := hS
    elementary := hel
    card := h8
    generated := ?_
    cubic_commutator := ?_
    cubic_normalizes := ?_
    normalizer_transitive := ?_
    contained_in_cores := ?_
    cores_normalize := ?_ }⟩
  · simpa [s] using triple_core_eq_closure h e X r hr hne hmark a ha
  · rw [← heZ]
    exact scalarPlane_eq_commutator h e X r hmark a haX ha
  · rw [← heZ]
    exact scalarPlane_cubicSylow_normalizes h e X a haX ha
  · rw [← heZ]
    exact scalarPlane_normalizer_transitive h e X r hr hne hmark a ha
  · rw [← heZ]
    exact scalarPlane_le_each_core h e X r hr hne hmark a ha
  · rw [← heZ]
    exact scalarPlane_each_core_normalizes h e X r hr hne hmark a ha

/-- The source hypotheses alone supply the complete commutator/fusion data. -/
theorem source_three_space_data_exists (h : IsTypeJ4 z) :
    ∃ (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
      (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)), Nonempty (ThreeSpaceData z e X) := by
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  exact ⟨e,X,source_three_space_data h e X⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
