module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Marking
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The actual full symmetric central cover

The natural quotient detects the centralizer of the whole moved subgroup,
so conjugation descends faithfully through the given S₆ marking. Full
movement by its A₆ component makes the original projection a perfect
central cover. The six-letter cover theorem then gives natural or
augmentation coordinates on this same subgroup, of order sixteen or
thirty-two. Its fixed kernel has order at most two and is normal in the
replacement, hence is central in the entire replacement.

No complement to the central kernel, Sylow condition on the radical, or
whole-core equality is used. `SectionFive.Graph` transports this quotient
to the actual graph layer for the two remaining distance branches.
Source: MS93 (3.2)(vi), (5.0), pp.863--864 and 912; Aschbacher--Smith
B.3.1--3 and I.1.5--6, pp.83--84 and 408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

instance moved_elementary (d : Replacement L R) : IsElementaryAbelian 2 (replacementMoved d) := by
  let : IsElementaryAbelian 2 (initialMoved L R) :=
    IsElementaryAbelian.of_le (commutator_le_left (centralOmega L R)
      (L.subgroupOf (L ⊔ R)))
  refine {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative
      (H := initialMoved L R) (K := d.overgroup)
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro v
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian
    (A := initialMoved L R) v.val.val v.property

include s in
theorem moved_centralizer :
    centralizer (replacementMoved d : Set d.overgroup) = pCore 2 d.overgroup := by
  apply le_antisymm
  · intro g hg
    have hp : s.projection g = 1 := by
      apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      apply LinearMap.ext
      intro v
      obtain ⟨w, hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
      have he := s.cover_conjugate g w w (by
        rw [← hg w w.property, mul_inv_cancel_right])
      simp only [hw, toAdd_ofAdd] at he
      simpa only [map_one, Module.End.one_apply] using he.symm
    rwa [← s.projection_kernel]
  · intro g hg w hw
    exact ((mem_omegaCenterIn_iff _ w).mp
      (replacementMoved_le_omegaCenter h d hw)).2.1 g hg |>.symm

/-- Conjugation on the entire cover, descended through the specified S₆ map. -/
def coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (replacementMoved d)) := by
  let := replacementMoved_normal h d
  exact NormalElementaryQuotient.representation (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm)

/-- The original natural quotient in additive coordinates. -/
def coverMap : Additive (replacementMoved d) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  (coverProjection h e hz hn d).toAdditiveLeft.toZModLinearMap 2

local notation "π" => coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)

theorem coverAction_conjugate (g : d.overgroup) (v : Additive (replacementMoved d)) :
    ((coverAction s (s.projection g) v).toMul : d.overgroup) =
      g * (v.toMul : d.overgroup) * g⁻¹ := by
  let := replacementMoved_normal h d
  exact NormalElementaryQuotient.representation_apply _ _ _ _ g v

theorem coverMap_surjective : Function.Surjective (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)) := by
  intro v
  obtain ⟨w, hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
  exact ⟨Additive.ofMul w, congrArg Multiplicative.toAdd hw⟩

theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive (replacementMoved d)) :
    π (coverAction s g v) = BinaryPermutation.naturalRepresentation (Fin 6) g (π v) := by
  obtain ⟨x, rfl⟩ := s.surjective g
  exact s.cover_conjugate x v.toMul (coverAction s (s.projection x) v).toMul
    (coverAction_conjugate s x v)

theorem coverMap_kernel :
    (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)).ker =
      fixedSpace (coverAction s) (alternatingGroup (Fin 6)) := by
  let := replacementMoved_normal h d
  ext v
  change coverProjection h e hz hn d v.toMul = 1 ↔ _
  change v.toMul ∈ (coverProjection h e hz hn d).ker ↔ _
  rw [coverProjection_kernel]
  rw [← s.component_image]
  exact (NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ _ v).symm

theorem coverAction_full_movement :
    subspaceCommutator (coverAction s) ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
  let := replacementMoved_normal h d
  have he : NormalElementaryQuotient.commutatorSpace (replacementMoved d)
      (replacementComponent d) = subspaceCommutator (coverAction s) ⊤
        ((replacementComponent d).map s.projection) :=
    NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d)
      s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)
      (replacementComponent d)
  rw [s.component_image] at he
  rw [← he, NormalElementaryQuotient.commutatorSpace,
    replacementMoved_idempotent h d]
  ext v
  simp

/-- The entire moved subgroup has one of the two actual S₆ module structures. -/
theorem cover_model :
    BinaryPermutation.SixCover.IsNaturalOrCore (coverAction s) (MonoidHom.id _) := by
  exact BinaryPermutation.SixCover.naturalOrCore_symmetric (coverAction s)
    (MulEquiv.refl _) (alternatingGroup (Fin 6)) (by simp)
    π (coverMap_equivariant s) (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    (coverMap_kernel s).le (coverAction_full_movement s)

include s in
/-- The possible central attachment is retained in the moved order. -/
theorem moved_card : Nat.card (replacementMoved d) = 16 ∨ Nat.card (replacementMoved d) = 32 := by
  rcases cover_model s with ⟨E, _⟩ | ⟨E, _⟩
  · left
    change Nat.card (Additive (replacementMoved d)) = 16
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  · right
    change Nat.card (Additive (replacementMoved d)) = 32
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num

include s in
/-- The only possible central attachment has order one or two. -/
theorem coverProjection_kernel_card :
    Nat.card (coverProjection h e hz hn d).ker = 1 ∨
      Nat.card (coverProjection h e hz hn d).ker = 2 := by
  let f := coverProjection h e hz hn d
  have hr : Nat.card f.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr (coverProjection_surjective h e hz hn d), Nat.card_congr (topEquiv).toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hc := f.ker.card_mul_index
  rw [index_ker, hr] at hc
  have hm := moved_card s
  change Nat.card f.ker = 1 ∨ Nat.card f.ker = 2
  omega

include s in
/-- The fixed kernel is central in the entire replacement, as in (5.0). -/
theorem moved_fixed_le_center :
    replacementMoved d ⊓ centralizer (replacementComponent d : Set d.overgroup) ≤
      center d.overgroup := by
  let := replacementMoved_normal h d
  let := replacementComponent_normal h d
  let C := replacementMoved d ⊓ centralizer (replacementComponent d : Set d.overgroup)
  have he : (coverProjection h e hz hn d).ker.map (replacementMoved d).subtype = C := by
    rw [coverProjection_kernel, map_comap_eq, range_subtype]
  have hc : Nat.card C = 1 ∨ Nat.card C = 2 := by
    rw [← he, card_map_of_injective (replacementMoved d).subtype_injective]
    exact coverProjection_kernel_card s
  rcases hc with hc | hc
  · exact (Subgroup.card_eq_one.mp hc).le.trans bot_le
  · exact central_of_normal_card_two C hc

include s in
/-- The quotient is by the actual ambient center, without a chosen complement. -/
theorem coverProjection_kernel_center :
    (coverProjection h e hz hn d).ker =
      (center d.overgroup).comap (replacementMoved d).subtype := by
  rw [coverProjection_kernel]
  ext v
  constructor
  · intro hv
    exact moved_fixed_le_center s ⟨v.property, hv⟩
  · intro hv
    exact (center_le_centralizer (replacementComponent d : Set d.overgroup)) hv

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
