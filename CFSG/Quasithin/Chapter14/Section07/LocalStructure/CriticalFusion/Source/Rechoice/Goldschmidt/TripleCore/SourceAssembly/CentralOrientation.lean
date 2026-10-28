module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Noncentral
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CosetBound.Exceptional
public import Stellmacher.OmegaOneCenterMap

/-!
# The forced central orientation in the original 14.7.70 triple

The marked point has order two and is centralized by the original Sylow
subgroup, so it lies in its omega-center. The right vertex moves this
omega-center: otherwise its span of the point would still have order two,
contrary to the preceding four-group geometry. If the generated group's
two-core is trivial, the five original chief factors rule out exceptional
vertices and the both-moving bound of forty-eight. Hence the left vertex
centralizes the omega-center of the literal restricted Sylow.

This isolates the remaining central-left branch without identifying the
whole omega-center with the marked point or assuming an amalgam bound.
It does not prove that the generated group has nontrivial two-core.
Source: Aschbacher--Smith, 14.7.70, printed p.1074, and F.6.5, p.305.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The original marked point lies in the original Sylow omega-center. -/
theorem point_le_original_omega (d : Data T L V F W) :
    F.Vi 1 ≤ omegaOneCenter (T : Subgroup G) := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  intro z hz
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨(F.le_seed 1).trans d.natural.chosen.le_sylow hz, ?_, ?_⟩
  · have hp := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : F.Vi 1)))
    simpa only [hcard, Subgroup.coe_pow, Subgroup.coe_one] using hp
  · intro t ht
    exact (mem_centralizer_iff.mp (group_centralizes_point d
      ((show (T : Subgroup G) ≤ group F L from le_sup_right) ht)) z hz).symm

/-- The same point containment after restricting to the actual generated group I. -/
theorem point_le_restricted_omega (d : Data T L V F W) (c : CriticalPath (L := L) F) :
    (F.Vi 1).subgroupOf (I c) ≤ omegaOneCenter (sylow c : Subgroup (I c)) := by
  intro z hz
  have hm := (mem_omegaOneCenterAmbient_iff _ _).mp (point_le_original_omega d hz)
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨hm.1, Subtype.ext hm.2.1, ?_⟩
  intro t ht
  exact Subtype.ext (hm.2.2 t ht)

/-- The four-group span forces movement at the actual right vertex. -/
theorem right_moves_restricted_omega (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (geometry : Geometry d c) :
    ⁅right c, omegaOneCenter (sylow c : Subgroup (I c))⁆ ≠ ⊥ := by
  intro hcomm
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hYP : Rechoice.Y c ≤ centralizer (F.Vi 1 : Set G) := by
    intro y hy
    apply mem_centralizer_iff.mpr
    intro z hz
    have hyI : y ∈ I c := Y_le_I c hy
    have hzI : z ∈ I c := point_le_I d c hz
    have hyR : (⟨y, hyI⟩ : I c) ∈ right c := (show Rechoice.Y c ≤ YT c from le_sup_left) hy
    have hzO := point_le_restricted_omega d c (show (⟨z, hzI⟩ : I c) ∈ (F.Vi 1).subgroupOf (I c) from hz)
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hcentral hyR) ⟨z, hzI⟩ hzO)
  have hEP : E c ≤ F.Vi 1 := by
    rw [geometry.span]
    exact conjugateSpanBy_le le_rfl (hYP.trans (Subgroup.centralizer_le_normalizer _))
  let := geometry.elementary
  have hE : Nat.card (E c) = 4 :=
    IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two geometry.rank_two
  have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hle := card_le_of_le hEP
  omega

private theorem good_vertices_of_large_left
    {H : Type u} [Group H] [Finite H] {A B : Subgroup H}
    (h : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 H = ⊥)
    (hlarge : 96 < Nat.card A) :
    generalizedFitting A = pCore 2 A ∧ generalizedFitting B = pCore 2 B := by
  have hnot : ¬ Nat.card (A ⊓ B : Subgroup H) ≤ 16 := by
    intro hsmall
    have hcorecard : Nat.card (pCore 2 A) ≤ Nat.card (A ⊓ B : Subgroup H) := by
      calc
        Nat.card (pCore 2 A) = Nat.card ((pCore 2 A).map A.subtype) :=
          Nat.card_congr ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).toEquiv
        _ ≤ Nat.card (A ⊓ B : Subgroup H) := card_le_of_le h.local_twoCore_le_intersection
    have hcard := SymmetricThreeTwoCore.card_eq h.quotient_left.some
    omega
  constructor
  · by_contra hbad
    exact hnot (h.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad)
  · by_contra hbad
    apply hnot
    simpa only [inf_comm B A] using
      h.symm.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad

/-- Under the contrary trivial-core assumption, the literal large left vertex
centralizes the restricted Sylow omega-center and the right vertex moves it. -/
theorem central_orientation_of_core_bot (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (geometry : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hcore : pCore 2 (I c) = ⊥) :
    ⁅left c, omegaOneCenter (sylow c : Subgroup (I c))⁆ = ⊥ ∧
      ⁅right c, omegaOneCenter (sylow c : Subgroup (I c))⁆ ≠ ⊥ := by
  have ht := LeftChiefFactors.triple d c geometry structural
  have hlarge := left_order_ge_1024 d c structural uniqueness mark duality hcomm
  have hgood := good_vertices_of_large_left ht hcore (by omega)
  have hright := right_moves_restricted_omega d c geometry
  refine ⟨?_, hright⟩
  by_contra hleft
  rw [← intersection_eq_sylow c ht] at hleft hright
  have hsmall := ht.local_card_le_forty_eight_of_noncentral_omega
    hcore hgood.1 hgood.2 hleft hright
  omega

/-- The original earlier setup constructs the duality needed for the same
central orientation; no independently supplied duality witness remains. -/
theorem central_orientation_of_source (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (geometry : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hcore : pCore 2 (I c) = ⊥) :
    ⁅left c, omegaOneCenter (sylow c : Subgroup (I c))⁆ = ⊥ ∧
      ⁅right c, omegaOneCenter (sylow c : Subgroup (I c))⁆ ≠ ⊥ := by
  have hc := d.sectionCentralizer_of_earlier_setup structural uniqueness
  obtain ⟨X, aX, mX, hs⟩ := CriticalIntersections.exists_sourceDuality d hc
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  exact central_orientation_of_core_bot d c geometry structural uniqueness mark duality hcomm hcore

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
