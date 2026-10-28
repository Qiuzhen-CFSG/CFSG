module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSeed
public import Theory.GroupTheory.PResidual.FrattiniControl
public import Theory.Frattini.Intersection

/-!
# The exceptional pair on its actual holomorph graph

The original radical is a two-group containing the two-core, and MS3 makes
its holomorph amalgam faithful. Characteristic two puts its central seed in
the core; consequently the critical distance exists, is positive and is even.
The graph commutator and central omega layer use the literal factor embedding.
The Frattini branch of MS93 (3.6) therefore gives the requested exhaustion
without a module classification or an assertion about the full action kernel.

Source: MS93 (2.0)--(2.2), pp.854--857; (3.6), p.870.
The non-Frattini and large-distance arguments are not proved here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

/-- This is the original radical, not a chosen Sylow subgroup. -/
abbrev edge (L R : Subgroup G) := R.subgroupOf (L ⊔ R)

include h

/-- The infinite free-amalgam tree, with its genuine least critical radius. -/
theorem sourceGeometry : Geometry T :=
  geometry T h.relative_radical.isPGroup h.relative_radical_ne_bot
    h.relative_characteristic

def sourceDistance : ℕ := (sourceGeometry h).b T

/-- Characteristic two excludes distance zero on the original carrier. -/
theorem sourceDistance_pos : 0 < sourceDistance h := by
  have hs : omegaCenter T ≤ pCore 2 M := by
    intro x hx
    have hc := (mem_omegaCenter_iff.mp hx).2.2
    exact h.relative_self_centralizing (centralizer_le h.relative_radical.twoCore_le hc)
  have hZ : Z T (alpha T) ≤ Q T (alpha T) := by
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact ChapterC.NaturalSixControl.SymplecticSeed.Z_le_map_of_seed_le _ _ hs
  obtain ⟨a, hc⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  by_contra! hz
  have hd : (cosetGraph T).dist (alpha T) a = 0 := by
    rw [hc.1]
    change sourceDistance h = 0
    omega
  have he : alpha T = a := (cosetGraph_connected T).dist_eq_zero_iff.mp hd
  exact hc.2 (he ▸ hZ)

theorem sourceDistance_even : Even (sourceDistance h) :=
  (sourceGeometry h).even (alpha T) rfl

theorem sourceDistance_eq_two (hb : sourceDistance h ≤ 2) : sourceDistance h = 2 := by
  have hp := sourceDistance_pos h
  have he := sourceDistance_even h
  rw [Nat.even_iff] at he
  omega

/-- The entire graph core is the original ambient commutator under embedM. -/
theorem graph_core : core T (alpha T) =
    (⁅pCore 2 M, K⁆).map (embedM T) :=
  core_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le h.relative_residual

/-- X means Omega-one of the center of Q, as on source p.855. -/
theorem graph_X : X T (alpha T) = (centralOmega L R).map (embedM T) := by
  rw [X, Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    omegaCenter_map _ _ (embedM_injective T)]
  rfl

/-- The local residual is the given relative component, not an assumed actor. -/
theorem graph_component : Ltilde T (alpha T) = (K).map (embedM T) := by
  rw [Ltilde_alpha, h.relative_residual]

omit h in
/-- The source Z-layer is precisely the original radical's central-omega orbit. -/
theorem graph_Z : Z T (alpha T) =
    (ChapterC.MSCentralOrbit.omegaOrbit T).map (embedM T) :=
  ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull T

/-- Source (2.2)'s edge centralizer is the actual two-core. This does not
identify the full vertex centralizer, which may retain an odd covering kernel. -/
theorem graph_edge_centralizer (e : CentralMarking L) :
    Q T (beta T) ⊓ centralizer (Z T (alpha T) : Set (FreeAmalgam T)) =
      Q T (alpha T) := by
  rw [Q_beta, graph_Z, Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  ext x
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hc⟩
    refine mem_map_of_mem (embedM T) ((h.relative_orbit_edge_centralizer e) ▸ ?_)
    refine ⟨hr, ?_⟩
    intro z hz
    apply embedM_injective T
    simpa only [map_mul] using hc (embedM T z) (mem_map_of_mem (embedM T) hz)
  · rintro ⟨q, hq, rfl⟩
    have hqc : q ∈ T ⊓ centralizer (ChapterC.MSCentralOrbit.omegaOrbit T : Set M) :=
      (h.relative_orbit_edge_centralizer e).symm ▸ hq
    refine ⟨mem_map_of_mem (embedM T) hqc.1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa only [map_mul] using congrArg (embedM T) (hqc.2 z hz)

/-- Exhaustion is transported through the same injective homomorphism on both sides. -/
theorem coreExhaustion_of_graph_eq
    (hc : core T (alpha T) = ⁅X T (alpha T), Ltilde T (alpha T)⁆) :
    CoreExhaustion L R := by
  apply map_injective (embedM_injective T)
  rw [← graph_core h, map_commutator, ← graph_X h, ← graph_component h]
  exact hc

/-- The source identity V = U also implies the required X-commutator identity,
since Z is contained in X and X is contained in Q. -/
theorem coreExhaustion_of_graph_core_eq_U
    (hc : core T (alpha T) = U T (alpha T)) : CoreExhaustion L R := by
  apply coreExhaustion_of_graph_eq h
  apply le_antisymm
  · rw [hc]
    exact commutator_mono
      ((sourceGeometry h).omega_bound (alpha T) rfl (sourceDistance_pos h)) le_rfl
  · exact commutator_mono (omegaCenter_le (Q T (alpha T))) le_rfl

/-- Burnside's basis-kernel theorem removes the Frattini factor. No critical
distance or initial module recognition is required for this branch. -/
theorem coreExhaustion_of_graph_frattini
    (hc : core T (alpha T) ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T)) :
    CoreExhaustion L R := by
  have hsmall : ⁅pCore 2 M, K⁆ ≤
      (frattini (pCore 2 M)).map (pCore 2 M).subtype ⊔ centralOmega L R := by
    rw [graph_core h, graph_X h,
      Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
      frattini_image_map _ _ (embedM_injective T), ← Subgroup.map_sup] at hc
    exact (map_le_map_iff_of_injective (embedM_injective T)).mp hc
  exact commutator_eq_of_le_frattini_sup_of_isPPerfect
    (pCore 2 M) K (centralOmega L R) pCore_isPGroup h.relative_twoPerfect
    (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) hsmall

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
