module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceExclusions
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSSpecialCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.Preparation
public import Theory.GroupTheory.PGroup.PerfectFrattiniCommutator

/-!
# A Frattini exclusion for the original alternating-five Baumann branch

For the original A₅ block, C.1.13 gives [R,L] ≤ V, where R=O₂(I)
and V is the full omega-center module. The actual Q=[O₂(K),K] lies
in R. If V lies in Φ(Q), the perfect action of L on Q is trivial by
Burnside's basis-kernel theorem. Since V=[V,L] and V≤R, this contradicts
the nonzero source module once V≤Q.

The existing case-three MS data supplies V≤Z(Q)=Φ(Q), so this excludes
that branch without the later 4.3.11--16 secondary-component endgame.
The source construction of the MS alternatives remains with
qt-d-1222-rankone-uniqueness-nonblock; its original-input specialization
must supply this Frattini containment without Hypothesis1223 exclusions.
The ordinary containing-component selection remains open as well.

Source: Aschbacher--Smith C.1.13(c), pp.124--125, C.1.34(3), pp.136--137,
and original 4.3.8--10, pp.616--617; application in 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original A₅ module cannot lie in the Frattini subgroup of the
containing component's commutator core. All ambient maps are literal. -/
theorem SourceConfiguration.false_of_alternatingFive_frattini
    (c : SourceConfiguration T L) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = Nonblock.W c)
    (hphi : Nonblock.W c ≤ (frattini (Nonblock.Q c)).map (Nonblock.Q c).subtype) : False := by
  let Q := Nonblock.Q c
  let V := Nonblock.W c
  have hQR : Q ≤ c.I.pCoreIn 2 := by
    have hQK : Q ≤ (Nonblock.K c).pCoreIn 2 :=
      le_normalizer_iff_commutator_le_left.mp
        ((Nonblock.K c).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image (Nonblock.K c) (pCore 2 _)))
    apply hQK.trans
    change (c.K.map c.H.subtype).pCoreIn 2 ≤ _
    rw [← map_pCoreIn_of_injective 2 c.K c.H.subtype c.H.subtype_injective]
    exact (map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
      c.c28.ambient_core_le_radical
  have hc : ⁅Q,L⁆ ≤ (frattini Q).map Q.subtype :=
    ((commutator_mono hQR le_rfl).trans
      (c.c28.normalized_radical_commutator_le_module inf_le_right hb hu)).trans hphi
  have hp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 c.I).to_le hQR
  let := c.c28.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe c.c28.component_le).toMonoidHom)
    (subgroupOfEquivOfLe c.c28.component_le).surjective
  have hz : ⁅Q,L⁆ = ⊥ := commutator_eq_bot_of_le_frattini_of_perfect Q L hp
    ((c.le_component.trans (map_subtype_le _)).trans (Nonblock.core_normalized c)) hc
  have hVQ : V ≤ Q := hphi.trans (map_subtype_le _)
  have hVmoved : V = ⁅V,L⁆ := by
    have he : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [he] using c.c28.module_commutator
  exact c.c28.module_nontrivial
    (bot_unique (hVmoved.le.trans ((commutator_mono hVQ le_rfl).trans hz.le)))

/-- Case-three MS data supplies precisely the Frattini containment needed
by the original A₅ exclusion; no later model-exclusion hypothesis is used. -/
theorem SourceConfiguration.false_of_alternatingFive_msData
    (c : SourceConfiguration T L) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = Nonblock.W c)
    {n : ℕ} (d : Nonblock.MSData c n) : False := by
  apply c.false_of_alternatingFive_frattini hb hu
  rw [d.core_frattini_eq_center,←d.fullModule]
  exact le_normalizer_iff_commutator_le_left.mp (c.le_component.trans d.natural.2.1)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The original Baumann escape supplies the A₅ block and identifies its
full source module, discharging both premises of the Frattini exclusion. -/
theorem Input.original_nonblock_frattini_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (c : SourceConfiguration T L)
    (hphi : Nonblock.W c ≤ (frattini (Nonblock.Q c)).map (Nonblock.Q c).subtype) : False := by
  obtain ⟨_,hb,hU,_⟩ := h.alternating_block_of_baumann_escape hout
  exact c.false_of_alternatingFive_frattini hb
    (hU.trans (h.original_fullModule_eq_moved hout).symm) hphi

/-- In the actual original-input Baumann counterexample the case-three
MS configuration is impossible, regardless of the chosen Chapter 12 module. -/
theorem Input.original_nonblock_ms_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (c : SourceConfiguration T L) {m : ℕ} (d : Nonblock.MSData c m) : False := by
  obtain ⟨_,hb,hU,_⟩ := h.alternating_block_of_baumann_escape hout
  exact c.false_of_alternatingFive_msData hb
    (hU.trans (h.original_fullModule_eq_moved hout).symm) d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
