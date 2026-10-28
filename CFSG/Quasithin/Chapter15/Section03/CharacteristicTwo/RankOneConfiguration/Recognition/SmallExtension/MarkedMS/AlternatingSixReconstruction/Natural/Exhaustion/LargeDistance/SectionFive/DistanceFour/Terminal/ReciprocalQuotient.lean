module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer
public import Theory.Representation.BinaryConjugationSection.ElementaryQuotient
public import Theory.Representation.BinaryConjugationSection.Descent

/-!
# The literal moved Baumann quotient after radius fixedness

Full-radius fixedness puts [V,Q] in the Baumann subgroup B. Involution
generation then puts every radius square in B, so both V/B and the source
quotient (Vcirc B)/B are elementary abelian. Their canonical coordinates
retain the original numerator, denominator and conjugation action.
The action on the moved quotient descends through the actual local
stabilizer modulo Q, with the original subgroup quotient map retained.
The natural-cover application supplies fixedness from a large critical
image. These constructions prepare the source factorization argument;
they do not assert an offender or the subsequent Thompson comparison.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h in
theorem reciprocal_radius_core_le_B_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ B d.radical a ((replacementGeometry h d).Z_normal a) := by
  have hcommV : ⁅V d.radical a,Q d.radical a⁆ ≤ V d.radical a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans (V_normalized a))
  intro x hx
  apply (mem_B_iff d.radical a _ (((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1))) x).mpr
  refine ⟨hcommV hx,?_⟩
  intro l hl
  have he := (hfixed hx).2 l hl
  have hzero : ⁅l,x⁆ = 1 := by
    simp only [commutatorElement_def,he,mul_assoc,mul_inv_cancel,mul_one]
  rw [hzero]
  exact one_mem _

include h in
theorem reciprocal_radius_squares_le_B_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (v : V d.radical a) :
    (v : FreeAmalgam d.radical)^2 ∈ B d.radical a ((replacementGeometry h d).Z_normal a) :=
  reciprocal_radius_core_le_B_of_fixed (h := h) hb ha hfixed
    (commutator_mono le_rfl (V_le_Q d.radical ha hb)
      (radius_sq_mem_derived (replacementGeometry h d) (replacementDistance_pos h d) a ha v))

/-- The relative Baumann subgroup of the full radius is normal. -/
theorem reciprocal_B_normal_radius
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false) :
    ((B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf (V d.radical a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1))).trans
      (Escape.Propagation.Rigidity.B_normalized hb a ha))

include h in
theorem reciprocal_radius_quotient_elementary_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let := reciprocal_B_normal_radius (h := h) hb ha
    IsElementaryAbelian 2 ((V d.radical a) ⧸
      (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf (V d.radical a)) := by
  let := reciprocal_B_normal_radius (h := h) hb ha
  let N := (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf (V d.radical a)
  have hp (v : (V d.radical a) ⧸ N) : v^2 = 1 := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective N v
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (reciprocal_radius_squares_le_B_of_fixed (h := h) hb ha hfixed v)
  let : IsMulCommutative ((V d.radical a) ⧸ N) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun v => orderOf_dvd_of_pow_eq_one (hp v)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

include h in
theorem reciprocal_radius_quotient_coordinates_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let := reciprocal_B_normal_radius (h := h) hb ha
    let := reciprocal_radius_quotient_elementary_of_fixed (h := h) hb ha hfixed
    ∃ ρ : Representation (ZMod 2) (stabilizer d.radical a)
        (Additive ((V d.radical a) ⧸
          (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf (V d.radical a))),
      Nonempty (Representation.BinaryConjugationSection (stabilizer d.radical a)
        (V d.radical a) (B d.radical a ((replacementGeometry h d).Z_normal a)) ρ) := by
  let := reciprocal_B_normal_radius (h := h) hb ha
  let := reciprocal_radius_quotient_elementary_of_fixed (h := h) hb ha hfixed
  exact Representation.BinaryConjugationSection.exists_elementary_quotient_coordinates
    _ _ _ (((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1))) (V_normalized a)
    (Escape.EdgeTransfer.B_le_radius hb a ha)
    (Escape.Propagation.Rigidity.B_normalized hb a ha)

/-- The source numerator of the moved Baumann quotient, in the original amalgam. -/
@[expose] def reciprocalMovedNumerator (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (d : Replacement L R) (a : Vertex d.radical) : Subgroup (FreeAmalgam d.radical) :=
  Vcirc d.radical a ⊔ B d.radical a ((replacementGeometry h d).Z_normal a)

theorem reciprocal_moved_numerator_le_radius
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false) : reciprocalMovedNumerator h d a ≤ V d.radical a :=
  sup_le (le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a)))
    (Escape.EdgeTransfer.B_le_radius hb a ha)

theorem reciprocal_moved_numerator_normalized
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false) :
    stabilizer d.radical a ≤ normalizer (reciprocalMovedNumerator h d a : Set (FreeAmalgam d.radical)) :=
  (le_inf (Vcirc_normalized a) (Escape.Propagation.Rigidity.B_normalized hb a ha)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem reciprocal_B_normal_moved
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false) :
    ((B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
      (reciprocalMovedNumerator h d a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((reciprocal_moved_numerator_le_radius (h := h) hb ha).trans
      (((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1)))).trans
      (Escape.Propagation.Rigidity.B_normalized hb a ha))

include h in
theorem reciprocal_moved_quotient_elementary_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let := reciprocal_B_normal_moved (h := h) hb ha
    IsElementaryAbelian 2 ((reciprocalMovedNumerator h d a) ⧸
      (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
        (reciprocalMovedNumerator h d a)) := by
  let := reciprocal_B_normal_moved (h := h) hb ha
  let N := (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
    (reciprocalMovedNumerator h d a)
  have hp (v : (reciprocalMovedNumerator h d a) ⧸ N) : v^2 = 1 := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective N v
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (reciprocal_radius_squares_le_B_of_fixed (h := h) hb ha hfixed
        ⟨v,reciprocal_moved_numerator_le_radius (h := h) hb ha v.property⟩)
  let : IsMulCommutative ((reciprocalMovedNumerator h d a) ⧸ N) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun v => orderOf_dvd_of_pow_eq_one (hp v)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

include h in
theorem reciprocal_moved_quotient_coordinates_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let := reciprocal_B_normal_moved (h := h) hb ha
    let := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixed
    ∃ ρ : Representation (ZMod 2) (stabilizer d.radical a)
        (Additive ((reciprocalMovedNumerator h d a) ⧸
          (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
            (reciprocalMovedNumerator h d a))),
      Nonempty (Representation.BinaryConjugationSection (stabilizer d.radical a)
        (reciprocalMovedNumerator h d a)
        (B d.radical a ((replacementGeometry h d).Z_normal a)) ρ) := by
  let := reciprocal_B_normal_moved (h := h) hb ha
  let := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixed
  exact Representation.BinaryConjugationSection.exists_elementary_quotient_coordinates
    _ _ _ ((reciprocal_moved_numerator_le_radius (h := h) hb ha).trans
      (((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1))))
    (reciprocal_moved_numerator_normalized (h := h) hb ha) le_sup_right
    (Escape.Propagation.Rigidity.B_normalized hb a ha)

/-- The actual local quotient acts on the source moved quotient, with the
original subgroup quotient map retained as its coordinates. -/
theorem reciprocal_moved_quotient_action_of_fixed
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    letI := Q_normal d.radical a
    letI := reciprocal_B_normal_moved (h := h) hb ha
    letI := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixed
    ∃ (ρ : Representation (ZMod 2)
        ((stabilizer d.radical a) ⧸ (Q d.radical a).subgroupOf (stabilizer d.radical a))
        (Additive ((reciprocalMovedNumerator h d a) ⧸
          (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
            (reciprocalMovedNumerator h d a))))
      (c : Representation.BinaryConjugationSection (stabilizer d.radical a)
        (reciprocalMovedNumerator h d a)
        (B d.radical a ((replacementGeometry h d).Z_normal a))
        (ρ.comp (QuotientGroup.mk' ((Q d.radical a).subgroupOf (stabilizer d.radical a))))),
      ∀ v : reciprocalMovedNumerator h d a, (c.coordinates v).toAdd =
        Additive.ofMul (QuotientGroup.mk'
          ((B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
            (reciprocalMovedNumerator h d a)) v) := by
  let := Q_normal d.radical a
  let := reciprocal_B_normal_moved (h := h) hb ha
  let := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixed
  have hMV := reciprocal_moved_numerator_le_radius (h := h) hb ha
  apply Representation.BinaryConjugationSection.exists_descended_actor
    _ _ _ (hMV.trans ((V_le_Q d.radical ha hb).trans (fun _ hx => hx.1))) le_sup_right
    (reciprocal_moved_numerator_normalized (h := h) hb ha)
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
    (QuotientGroup.mk' ((Q d.radical a).subgroupOf (stabilizer d.radical a)))
    (QuotientGroup.mk'_surjective _)
  intro x hx v hv
  have hxN : x ∈ (Q d.radical a).subgroupOf (stabilizer d.radical a) :=
    (QuotientGroup.eq_one_iff x).mp hx
  have hxQ : (x : FreeAmalgam d.radical) ∈ Q d.radical a := hxN
  apply reciprocal_radius_core_le_B_of_fixed (h := h) hb ha hfixed
  rw [commutator_comm]
  exact commutator_mem_commutator hxQ (hMV hv)

include e hz hn in
/-- Natural-cover application: the earlier large-image calculation supplies
full-radius fixedness and hence the source's literal elementary quotient. -/
theorem natural_large_moved_quotient_elementary_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    letI := reciprocal_B_normal_moved (h := h) (by omega) (a := alpha d.radical) rfl
    IsElementaryAbelian 2 ((reciprocalMovedNumerator h d (alpha d.radical)) ⧸
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).subgroupOf
        (reciprocalMovedNumerator h d (alpha d.radical))) := by
  exact reciprocal_moved_quotient_elementary_of_fixed (h := h) (by omega) rfl
    (natural_large_radius_core_fixed_knownSimple (e := e) (hz := hz) (hn := hn) hb hnat p hlarge)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
