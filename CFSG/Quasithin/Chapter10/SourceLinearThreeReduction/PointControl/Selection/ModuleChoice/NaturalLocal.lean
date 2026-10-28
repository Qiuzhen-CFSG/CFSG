module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.MovingSupport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import Theory.GroupTheory.Commutator.CentralQuotientSaturation
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Recovering the original local module from natural coordinates

The original local commutator has nonzero image in the full moved module's
central quotient: otherwise perfectness would make that local commutator
trivial. Transitivity on nonzero natural vectors makes that
image the entire quotient. Commutator generation then recovers the full
moved subgroup, including its fixed kernel. The source pair-generation
identity and T-invariance recover the entire full module inside the local
module.

This applies to both literal natural rows used by the selection consumer.
It removes full/local equality as a separate classification premise; the
existence of those natural coordinates remains a source obligation.
Source: Aschbacher--Smith, 3.2.6(3) and 10.1.1(1),(3),
printed pp.581 and741.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit D [Finite G] in
private theorem eq_of_transitive_central_section
    {H W K A : Subgroup G} (hAW : A ≤ W)
    (hHA : H ≤ normalizer (A : Set G)) (hW : ⁅W,H⁆ = W)
    (hK : K ≤ centralizer (H : Set G)) (hn : ¬ A ≤ K)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (c : BinaryConjugationSection H W K ρ)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ l : H, ρ l v = w) : A = W := by
  let f := c.coordinates.comp (inclusion hAW)
  have hex : ∃ a : A, f a ≠ 1 := by
    by_contra h
    apply hn
    intro a ha
    have hz : f ⟨a,ha⟩ = 1 := by
      by_contra hz
      exact h ⟨⟨a,ha⟩,hz⟩
    exact (c.coordinates_eq_one_iff (inclusion hAW ⟨a,ha⟩)).mp hz
  obtain ⟨a,ha⟩ := hex
  have hs : Function.Surjective f := by
    intro w
    by_cases hw : w = 1
    · exact ⟨1, by simp [hw]⟩
    obtain ⟨l,hl⟩ := htrans (f a).toAdd w.toAdd ha hw
    let b : A := ⟨l*a*(l:G)⁻¹,
      (mem_normalizer_iff.mp (hHA l.property) a).mp a.property⟩
    refine ⟨b, Multiplicative.toAdd.injective ?_⟩
    exact (c.equivariant l (inclusion hAW a)).trans hl
  apply eq_of_central_quotient_surjective H W A hAW hHA hW c.coordinates _ hs
  rw [c.kernel_eq]
  exact comap_mono hK

/-- Transitive nonzero quotient vectors recover the full moved subgroup
from the original local commutator, with its central kernel retained. -/
theorem local_moved_eq_full_of_transitive_section
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ l : L, ρ l v = w) :
    ⁅D.moduleSubgroup,L⁆ = ⁅D.fullModule,L⁆ := by
  apply eq_of_transitive_central_section
    (commutator_mono (le_componentOrbit _ _) le_rfl)
    (normalizer_commutator_ge_right _ _) (source_full_moved_eq_commutator D)
    (show sourceMovedFixed D ≤ centralizer (L : Set G) from inf_le_right) _ ρ c htrans
  intro hc
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  exact local_moved_ne_bot D (commutator_eq_bot_of_iterated_eq_bot D.moduleSubgroup L
    (commutator_eq_bot_iff_le_centralizer.mpr (hc.trans inf_le_right)))

/-- Pair generation turns equality of moved subgroups into equality of
the full and local modules for the original nonnormal setup. -/
theorem full_eq_local_of_transitive_section
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ l : L, ρ l v = w) :
    D.fullModule = D.moduleSubgroup := by
  have hW : ⁅D.fullModule,L⁆ ≤ D.moduleSubgroup := by
    rw [←local_moved_eq_full_of_transitive_section D ρ c htrans]
    exact le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  obtain ⟨t,ht,_,_,hgen,_⟩ := source_nonnormal_fullModule_pair D hn
  apply le_antisymm _ (le_componentOrbit _ _)
  change D.fullModule ≤ D.moduleSubgroup
  rw [hgen]
  apply sup_le hW
  exact (map_mono hW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_module ht))

/-- Literal rank-one natural coordinates imply full/local equality. -/
theorem full_eq_local_of_rankOneNatural
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : RankOneNatural D) : D.fullModule = D.moduleSubgroup := by
  obtain ⟨n,hnn,e,⟨c⟩⟩ := hm
  let : NeZero n := ⟨by omega⟩
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
  apply full_eq_local_of_transitive_section D hn _ c
  intro v w hv hw
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq (GaloisField 2 n) v w hv hw
  obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
  refine ⟨l,?_⟩
  change (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l))) v = w
  rw [hl]
  exact hg

/-- Literal binary-three natural coordinates imply full/local equality. -/
theorem full_eq_local_of_binaryThreeNatural
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : BinaryThreeNatural D) : D.fullModule = D.moduleSubgroup := by
  obtain ⟨e,⟨c⟩⟩ := hm
  apply full_eq_local_of_transitive_section D hn _ c
  intro v w hv hw
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv hw
  obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
  refine ⟨l,?_⟩
  change specialLinearNatural 3 (e (QuotientGroup.mk' (pCore 2 L) l)) v = w
  rw [hl,specialLinearNatural_apply]
  exact hg

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
