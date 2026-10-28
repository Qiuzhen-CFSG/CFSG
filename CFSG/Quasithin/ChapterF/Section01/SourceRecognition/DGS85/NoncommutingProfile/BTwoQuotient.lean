module
public import Theory.Representation.BinaryConjugationSection.QuadraticCorePair

/-!
# The quotient-action calculation for the noncentral b=2 branch

Construct the conjugation representation on the actual Q/Z, using the
local actor's specified quotient map. The two elementary generators and
commutator bounds prove quadraticity and fixed-space generation. The two
opposite-field index identities force equal field orders, after which the
natural action lifts involutions and contradicts noncommutation.

`CorePairAction` is intermediate subgroup geometry, not Hypothesis B'.
Its span, commutator, and fixed-preimage premises, and the paired cross-index
identities, still require the local arguments of 10.3--10.6. No natural
quotient action, field equality, or classification conclusion is assumed.

Source: DGS, *Groups and Graphs* (1985), 10.6, printed pp.157--158.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G]
local instance {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Intermediate subgroup geometry used in the proof of 10.6. These are
local proof obligations, not an alternative encoding of Hypothesis B'. In
particular, the fixed-preimage assertion still needs proof
when applying this constructor to a source configuration. -/
structure CorePairAction (L Q Z A C T : Subgroup G)
    (k : Type*) [Field k] [Finite k] [CharP k 2] where
  core_le : Q ≤ L
  kernel_le : Z ≤ Q
  normalized_core : L ≤ normalizer (Q : Set G)
  normalized_kernel : L ≤ normalizer (Z : Set G)
  left_le : A ≤ Q
  right_le : C ≤ Q
  span : Q = (A ⊔ C) ⊔ Z
  commutator : ⁅A,C⁆ ≤ Z
  conjugator : L
  conjugate : C = A.conjBy (conjugator : G)
  quotient : L →* SL(2,k)
  onto : Function.Surjective quotient
  kernel : quotient.ker = Q.subgroupOf L
  sylow : Sylow 2 SL(2,k)
  actor_image : (T.subgroupOf L).map quotient = sylow
  fixed_left : ⁅T,A⁆ ≤ Z
  quadratic_bound : ⁅T,⁅T,Q⁆⁆ ≤ Z
  fixed_preimage : ∀ x ∈ Q, (∀ a ∈ L, ⁅a,x⁆ ∈ Z) → x ∈ Z

namespace CorePairAction
variable {L Q Z A C T : Subgroup G}
  {k : Type*} [Field k] [Finite k] [CharP k 2]
  (c : CorePairAction L Q Z A C T k)

include c

/-- Normality is relative to the original core. -/
theorem kernel_normal : (Z.subgroupOf Q).Normal :=
  (normal_subgroupOf_iff_le_normalizer c.kernel_le).mpr
    (c.core_le.trans c.normalized_kernel)

/-- Construct the binary action on Q/Z with its literal quotient coordinates,
quadratic Sylow action and the corrected fixed-space generation property. -/
theorem exists_quadratic_section [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C] :
    letI := c.kernel_normal
    letI := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
      c.span c.commutator
    ∃ (σ : Representation (ZMod 2) SL(2,k) (Additive (Q ⧸ Z.subgroupOf Q)))
      (d : BinaryConjugationSection L Q Z (σ.comp c.quotient)),
      (∀ q : Q, (d.coordinates q).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf Q) q)) ∧
      IsQuadratic σ c.sylow ∧ GeneratedByFixedSpace σ c.sylow ∧
      fixedSpace σ ⊤ = ⊥ := by
  let := c.kernel_normal
  let := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
    c.span c.commutator
  obtain ⟨σ,d,hd⟩ := exists_canonical L Q Z c.core_le c.kernel_le
    c.normalized_core c.normalized_kernel c.quotient c.onto c.kernel
  refine ⟨σ,d,hd,?_,?_,?_⟩
  · rw [←c.actor_image]
    exact quadratic_of_commutator_bounds σ c.quotient d T ⁅T,Q⁆ le_rfl c.quadratic_bound
  · rw [←c.actor_image]
    exact pair_section_generated L Q Z A C T σ c.quotient d c.left_le
      c.span c.conjugator c.conjugate c.fixed_left
  · exact section_fixed_bot_of_commutators L Q Z σ c.quotient d c.fixed_preimage

/-- The representation and its natural coordinates are constructed on the
literal quotient Q/Z. The coordinate homomorphism is its actual quotient map. -/
theorem exists_natural_section [Finite Q]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    (hcard : Z.relIndex Q = Nat.card k ^ 2) :
    letI := c.kernel_normal
    letI := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
      c.span c.commutator
    ∃ (σ : Representation (ZMod 2) SL(2,k) (Additive (Q ⧸ Z.subgroupOf Q)))
      (d : BinaryConjugationSection L Q Z (σ.comp c.quotient))
      (E : Additive (Q ⧸ Z.subgroupOf Q) ≃ₗ[ZMod 2] (Fin 2 → k)),
      (∀ q : Q, (d.coordinates q).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf Q) q)) ∧
      (∀ a w, E (σ a w) = Matrix.mulVec a.val (E w)) := by
  let := c.kernel_normal
  let := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
    c.span c.commutator
  let W := Additive (Q ⧸ Z.subgroupOf Q)
  let : Finite W := Finite.of_surjective
    (fun q : Q => Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf Q) q))
    (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,d,hd,hq,hg,hf⟩ := c.exists_quadratic_section
  have hc : Nat.card W = Nat.card k ^ 2 := hcard
  obtain ⟨E,he⟩ := natural_of_quadratic_pair_size σ c.sylow hq hg hf hc
  exact ⟨σ,d,E,hd,he⟩

/-- Noncommutation supplies a nonzero section, so the actual actor field
square is bounded by its literal core/center index. -/
theorem field_square_le_index [Finite Q]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    (hcentral : Z ≤ centralizer (Q : Set G)) (hne : ⁅A,C⁆ ≠ ⊥) :
    Nat.card k ^ 2 ≤ Z.relIndex Q := by
  let := c.kernel_normal
  let := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
    c.span c.commutator
  let W := Additive (Q ⧸ Z.subgroupOf Q)
  let : Finite W := Finite.of_surjective
    (fun q : Q => Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf Q) q))
    (QuotientGroup.mk'_surjective _)
  have hidx : Z.relIndex Q ≠ 1 := by
    intro he
    have hQZ := relIndex_eq_one.mp he
    apply hne
    rw [commutator_eq_bot_iff_le_centralizer]
    exact (c.left_le.trans hQZ).trans (hcentral.trans (centralizer_le c.right_le))
  have hpos : 0 < Nat.card W := Nat.card_pos
  have hsize : 1 < Nat.card W := by
    change Nat.card W ≠ 1 at hidx
    omega
  obtain ⟨σ,d,_,hq,hg,hf⟩ := c.exists_quadratic_section
  exact field_square_le_of_quadratic_section (W := W) σ c.sylow hq hg hf hsize

/-- Under the same-field section count, the two critical center candidates
commute. The whole core becomes elementary when the first one escapes Z. -/
theorem commutator_eq_bot [Finite Q]
    [IsElementaryAbelian 2 Z] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hcard : Z.relIndex Q = Nat.card k ^ 2) : ⁅A,C⁆ = ⊥ := by
  by_cases hAZ : A ≤ Z
  · rw [commutator_eq_bot_iff_le_centralizer]
    exact hAZ.trans (hcentral.trans (centralizer_le c.right_le))
  · let := c.kernel_normal
    let := pair_quotient_elementary Q Z A C c.left_le c.right_le c.kernel_le
      c.span c.commutator
    obtain ⟨σ,d,E,_,he⟩ := c.exists_natural_section hcard
    let := elementary_core_of_natural_section L Q Z A σ c.quotient c.onto d
      hcentral c.left_le hAZ E he
    apply bot_unique
    exact (commutator_mono c.left_le c.right_le).trans
      (commutator_self_eq_bot_iff.mpr inferInstance).le
/-- The paired cross-index calculation forces equal field orders. These
are the two opposite-field sizes on p.157, not a same-field size assumption. -/
theorem paired_fields_equal
    {L' Q' Z' A' C' T' : Subgroup G}
    {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]
    (c' : CorePairAction L' Q' Z' A' C' T' k')
    [Finite Q] [Finite Q']
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    [IsElementaryAbelian 2 A'] [IsElementaryAbelian 2 C']
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hcentral' : Z' ≤ centralizer (Q' : Set G))
    (hne : ⁅A,C⁆ ≠ ⊥) (hne' : ⁅A',C'⁆ ≠ ⊥)
    (hcross : Z.relIndex Q = Nat.card k' ^ 2)
    (hcross' : Z'.relIndex Q' = Nat.card k ^ 2) :
    Nat.card k = Nat.card k' := by
  have h₀ := c.field_square_le_index hcentral hne
  have h₁ := c'.field_square_le_index hcentral' hne'
  rw [hcross] at h₀
  rw [hcross'] at h₁
  nlinarith

/-- Both noncommuting local sections with the source cross-indices are
impossible in characteristic two. Field equality is proved in the argument. -/
theorem paired_impossible
    {L' Q' Z' A' C' T' : Subgroup G}
    {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]
    (c' : CorePairAction L' Q' Z' A' C' T' k')
    [Finite Q] [Finite Q'] [IsElementaryAbelian 2 Z]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    [IsElementaryAbelian 2 A'] [IsElementaryAbelian 2 C']
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hcentral' : Z' ≤ centralizer (Q' : Set G))
    (hne : ⁅A,C⁆ ≠ ⊥) (hne' : ⁅A',C'⁆ ≠ ⊥)
    (hcross : Z.relIndex Q = Nat.card k' ^ 2)
    (hcross' : Z'.relIndex Q' = Nat.card k ^ 2) : False := by
  have he := c.paired_fields_equal c' hcentral hcentral' hne hne' hcross hcross'
  exact hne (c.commutator_eq_bot hcentral (hcross.trans (congrArg (· ^ 2) he.symm)))

end CorePairAction

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
