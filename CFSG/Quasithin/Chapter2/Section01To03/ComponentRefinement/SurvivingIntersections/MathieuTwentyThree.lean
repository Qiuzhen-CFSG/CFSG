module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.Envelope
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuShapes
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.BlockOrders
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.EnvelopeConstruction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.BlockExclusion

/-!
# The M23 intersection: projection, maximality, and local assembly

The actual inner action supplies a unique involution of L. Its image in M23
fixes a heptad, and S intersect L stabilizes this heptad. Ordinary maximality
of its full stabilizer is proved in the concrete geometry.

The constructed local overgroup X contains both the heptad subgroup and the
full S. Its alternating-power extension has no chi-zero blocks, so the genuine
block generation hypothesis forces X into M; maximality then identifies the
intersection. The final assembly discharges both of these local premises and
transports the actual E16 kernel and A7 quotient supplied by MathieuShapes.

This proves the direct M23-model case from LocalSetup and the literal inner
action in 1.1.5(3)(f). Elimination of central covers is a separate argument.

Source: Aschbacher–Smith 1.1.5(3)(f) and 2.3.9(7)(f), printed pp.502 and
525–526 of the combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem center_eq_bot_of_m23 {L : Subgroup G} (e : L ≃* M23) : center L = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center M23 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa using congrArg e (mem_center_iff.mp hx a)
  rw [m23_center_eq_bot, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

/-- The literal inner action determines the source involution projection,
with no extra assumption of nontriviality or order on its inducing element. -/
theorem mathieuTwentyThree_exists_projection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃! t : L, IsConjugationProjection L z t ∧ orderOf t = 2 :=
  h.exists_unique_projection (center_eq_bot_of_m23 e) α hα hinner

/-- The actual intersection S intersect L stabilizes the fixed heptad. This
makes no claim that S normalizes the individual component L. -/
theorem mathieuTwentyThree_sylow_le_heptad
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    {t : L} (ht : IsConjugationProjection L z t)
    (R : Sylow 2 L)
    (hR : (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L) :
    (R : Subgroup L).map e.toMonoidHom ≤ MulAction.stabilizer M23 (fixedHeptad (e t)) := by
  rintro _ ⟨x, hx, rfl⟩
  apply centralizer_le_fixedHeptad_stabilizer
  apply mem_centralizer_singleton_iff.mpr
  have hc := mem_centralizer_iff.mp (h.projection_centralizes_sylow ht R hR) x hx
  simpa using congrArg e hc

/-- Conditional assembly from a constructed local envelope and a proof that
it has no chi-zero blocks. The full stabilizer containment is derived using
the local block hypothesis, before applying ordinary maximality. -/
theorem mathieuTwentyThree_intersection_of_local_envelope
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (t : L) (ht2 : orderOf t = 2) (X : Subgroup G)
    (hX : MathieuTwentyThreeLocalEnvelope L ((S : Subgroup H).map H.subtype) e t X)
    (hblocks : ∀ B : Subgroup X, ¬ ChapterC.IsChiZeroBlockIn B) :
    (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M23 (fixedHeptad (e t)) := by
  have hXM : X ≤ M := by
    by_contra hXM
    obtain ⟨d⟩ := h.blocks X hX.1 hX.2.1 hXM
    obtain ⟨B, hB, _, _⟩ := d.exists_escapingBlock hXM
    exact hblocks B hB
  have hK : MulAction.stabilizer M23 (fixedHeptad (e t)) ≤
      (M.subgroupOf L).map e.toMonoidHom := by
    intro g hg
    let x : L := e.symm g
    have hx : x ∈ (MulAction.stabilizer M23 (fixedHeptad (e t))).comap e.toMonoidHom := by
      change e (e.symm g) ∈ MulAction.stabilizer M23 (fixedHeptad (e t))
      simpa only [e.apply_symm_apply] using hg
    have hxM : (x : G) ∈ M := hXM (hX.2.2.1 ⟨x, hx, rfl⟩)
    exact ⟨x, hxM, e.apply_symm_apply g⟩
  have hproper : (M.subgroupOf L).map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply h.outside
    apply Subgroup.subgroupOf_eq_top.mp
    apply e.mapSubgroup.injective
    simpa using he
  exact ((fixedHeptad_stabilizer_isCoatom (by simpa using ht2)).le_iff_eq hproper).mp hK

/-- Under the same explicit local premises, the actual intersection has its
normal elementary abelian kernel of order sixteen and alternating quotient. -/
theorem mathieuTwentyThree_extension_of_local_envelope
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (t : L) (ht2 : orderOf t = 2) (X : Subgroup G)
    (hX : MathieuTwentyThreeLocalEnvelope L ((S : Subgroup H).map H.subtype) e t X)
    (hblocks : ∀ B : Subgroup X, ¬ ChapterC.IsChiZeroBlockIn B) :
    AlternatingBySixteen (M.subgroupOf L) 7 := by
  have heq := mathieuTwentyThree_intersection_of_local_envelope h e t ht2 X hX hblocks
  let eq : M.subgroupOf L ≃* MulAction.stabilizer M23 (fixedHeptad (e t)) :=
    (e.subgroupMap (M.subgroupOf L)).trans (MulEquiv.subgroupCongr heq)
  exact (mathieuTwentyThree_heptad_extension (fixedHeptad_mem (by simpa using ht2))).of_equiv eq.symm

/-- The full stabilizer of the projected involution's fixed heptad is exactly
the component intersection. Both the full-S envelope and its block exclusion
are constructed from the local setup. -/
theorem mathieuTwentyThree_intersection_of_projection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    (M.subgroupOf L).map e.toMonoidHom =
      MulAction.stabilizer M23 (fixedHeptad (e t)) := by
  let := h.finite
  obtain ⟨X, hX⟩ := mathieuTwentyThree_exists_local_envelope h e ht ht2
  exact mathieuTwentyThree_intersection_of_local_envelope h e t ht2 X hX
    (not_chiZeroBlockIn_of_alternatingPowerTwoExtension hX.2.2.2)

/-- The direct M23 intersection calculation in 2.3.9(7)(f), with the actual
model isomorphism and inner action from 1.1.5(3)(f). The heptad is the fixed
set of the uniquely determined involution projection. -/
theorem mathieuTwentyThree_intersection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ B ∈ m23Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M23 B := by
  obtain ⟨t, ⟨ht, ht2⟩, _⟩ := mathieuTwentyThree_exists_projection h e α hα hinner
  exact ⟨fixedHeptad (e t), fixedHeptad_mem ((e.orderOf_eq t).trans ht2),
    mathieuTwentyThree_intersection_of_projection h e ht ht2⟩

/-- The source A7/E16 conclusion for the actual component intersection:
a normal elementary abelian subgroup of order sixteen with quotient A7. -/
theorem mathieuTwentyThree_extension
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    AlternatingBySixteen (M.subgroupOf L) 7 := by
  obtain ⟨B, hB, heq⟩ := mathieuTwentyThree_intersection h e α hα hinner
  let eq : M.subgroupOf L ≃* MulAction.stabilizer M23 B :=
    (e.subgroupMap (M.subgroupOf L)).trans (MulEquiv.subgroupCongr heq)
  exact (mathieuTwentyThree_heptad_extension hB).of_equiv eq.symm

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
