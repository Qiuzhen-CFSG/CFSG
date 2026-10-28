module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Graph
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CoreComplete

/-!
# The natural full-point branch on the original replacement

When the entire moved cover has order sixteen, its given map to the natural
module is bijective. A nonzero fixed vector for the radical supplies the
remaining data of the native symplectic source. This preserves the component,
radical, moved subgroup and free-amalgam critical distance exactly.

The native Section 5 proof therefore excludes large distance when the radical
has full point-core image. The final dichotomy retains the order-thirty-two
central cover and every other radical image; neither is ruled out here.

Source: MS93 (5.0), (5.11)--(5.12), printed pp.912, 923--927.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
open ChapterC.NaturalSixControl
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem coverProjection_bijective
    (hnat : Nat.card (replacementMoved d) = 16) :
    Function.Bijective (coverProjection h e hz hn d) := by
  apply (coverProjection_surjective h e hz hn d).bijective_of_nat_card_le
  rw [hnat]
  change 16 ≤ Nat.card (BinaryPermutation.natural (Fin 6))
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  decide

include s in
private theorem moved_fixed_vector :
    ∃ w : replacementMoved d, w ≠ 1 ∧
      ∀ g ∈ d.radical, g * (w : d.overgroup) = (w : d.overgroup) * g := by
  let := replacementMoved_normal h d
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction d.radical (replacementMoved d) :=
    conjMulDistribMulActionOfLeNormalizer _ _ (by rw [normalizer_eq_top]; exact le_top)
  have hcard : 2 ∣ Nat.card (replacementMoved d) := by
    rcases moved_card s with hc | hc <;> rw [hc] <;> decide
  obtain ⟨w, hw, hne⟩ :=
    (replacement_radical_isPGroup h d).exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (replacementMoved d) hcard
      (show (1 : replacementMoved d) ∈ MulAction.fixedPoints d.radical (replacementMoved d) by
        simp [MulAction.mem_fixedPoints])
  refine ⟨w, Ne.symm hne, ?_⟩
  intro g hg
  have hh := congrArg (replacementMoved d).subtype ((MulAction.mem_fixedPoints.mp hw) ⟨g, hg⟩)
  change g * (w : d.overgroup) * g⁻¹ = w at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The order-sixteen cover supplies actual natural coordinates, on the
unchanged replacement component, radical and whole moved subgroup. -/
def nativeSource (s : FullSymmetricAction h e hz hn d)
    (hnat : Nat.card (replacementMoved d) = 16) :
    letI := replacementComponent_normal h d
    letI := replacementMoved_normal h d
    SymplecticSetup.Source (replacementComponent d) d.radical (replacementMoved d) := by
  letI := replacementComponent_normal h d
  letI := replacementMoved_normal h d
  let E := MulEquiv.ofBijective (coverProjection h e hz hn d) (coverProjection_bijective hnat)
  let w := (moved_fixed_vector s).choose
  have hwn := (moved_fixed_vector s).choose_spec.1
  have hfixed := (moved_fixed_vector s).choose_spec.2
  refine {
    two_group := replacement_radical_isPGroup h d
    core_le := replacement_core_le_radical h d
    characteristic := replacement_characteristic h d
    product := replacement_product h d
    residual := replacement_residual h d
    projection := s.projection
    projection_kernel := s.projection_kernel
    component_image := s.component_image
    module_le_core := ?_
    module_le_component := ?_
    coordinates := E
    action := ?_
    w := w
    w_ne := hwn
    radical_fixes := hfixed }
  · intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1
  · let := h.relative_normal
    intro x hx
    exact commutator_le_right (centralOmega L R) (L.subgroupOf (L ⊔ R)) hx
  · intro g v
    exact s.cover_conjugate g v (MulAut.conjNormal g v) rfl

/-- The source projection is the given full symmetric marking itself. -/
theorem nativeSource_projection (hnat : Nat.card (replacementMoved d) = 16) :
    letI := replacementComponent_normal h d
    letI := replacementMoved_normal h d
    (nativeSource s hnat).projection = s.projection := by rfl

/-- The source has the identical free-amalgam graph and critical distance. -/
theorem nativeSource_distance (hnat : Nat.card (replacementMoved d) = 16) :
    letI := replacementComponent_normal h d
    letI := replacementMoved_normal h d
    (nativeSource s hnat).geometry.b d.radical = replacementDistance h d := by rfl

/-- The existing Section 5 theorem applies to the literal replacement when
its whole moved subgroup is natural and its radical has full point-core image. -/
theorem distance_eq_two_of_natural_full_point
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
    (hnat : Nat.card (replacementMoved d) = 16) (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom) :
    replacementDistance h d = 2 := by
  let := replacementComponent_normal h d
  let := replacementMoved_normal h d
  have hs := (nativeSource s hnat).criticalDistance_eq_two
    (h.sqtk.subgroup d.overgroup) t
      (by simpa only [nativeSource_projection, Model.pointCore_eq_exceptional] using hpoint)
  exact hs

/-- The native Section 5 source excludes critical distance four on the
order-sixteen full point-core branch. -/
theorem distance_ne_four_of_natural_full_point
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
    (hnat : Nat.card (replacementMoved d) = 16) (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom) :
    replacementDistance h d ≠ 4 := by
  let := replacementComponent_normal h d
  let := replacementMoved_normal h d
  let hsq := h.sqtk.subgroup d.overgroup
  let hlayer := (nativeSource s hnat).nativeCentralLayer hsq
  have hs := (nativeSource s hnat).criticalDistance_ne_four hlayer t
      (by simpa only [nativeSource_projection, Model.pointCore_eq_exceptional] using hpoint) hsq
  rw [nativeSource_distance s hnat] at hs
  exact hs

/-- Large distance can remain only for an order-thirty-two cover or for
an order-sixteen cover whose radical image is not any full point core. -/
theorem large_distance_remaining_cases
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
    (hb : 2 < replacementDistance h d) :
    Nat.card (replacementMoved d) = 32 ∨
      (Nat.card (replacementMoved d) = 16 ∧ ∀ t : Equiv.Perm (Fin 6),
        d.radical.map s.projection ≠
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
            (MulAut.conj t).toMonoidHom) := by
  rcases moved_card s with hnat | hnat
  · refine Or.inr ⟨hnat, ?_⟩
    intro t hpoint
    rw [distance_eq_two_of_natural_full_point s hnat t hpoint] at hb
    exact (lt_irrefl 2) hb
  · exact Or.inl hnat

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
