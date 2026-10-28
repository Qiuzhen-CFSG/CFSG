module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding the quasisimple alternative for the actual cubic

In the whole-actor cases of B.5.1(1), the offender subgroup is quasisimple.
Its subnormal cubic is central, and the full commutator with the restricted
C forces that cubic to be trivial. This retains the centers of quasisimple
covers throughout the argument.

In the remaining case the actual section-action isomorphism identifies the
actor with Sₙ, n ≥ 5, or the split-octonion G₂(2). Their three-cores vanish:
a nontrivial normal subgroup contains Aₙ or the binary long-root normal
closure, respectively, and those subgroups have even order. The subnormal
cubic lies in the three-core, giving the contradiction.

Only the whole-actor and outer-action clauses of the supplied B.5.1(1)
conclusion are used. The marked application retains the original star image
and the image of the supplied Sylow subgroup.

Source: Aschbacher–Smith, B.5.1(1) and B.5.6(1), printed pp.99 and 105,
as used in 13.6.10, printed p.928. The G₂ normal-subgroup calculation is
from the attributed ATLAS development imported above.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

private theorem cubic_le_center {X : Type*} [Group X] [IsQuasisimple X]
    (B : Subgroup X) (hB : B.IsSubnormal) (hc : Nat.card B = 3) :
    B ≤ center X := by
  rcases IsQuasisimple.subnormal_le_center_or_eq_top B hB with h | ht
  · exact h
  · have hx : Nat.card X = 3 := by
      rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
      exact hc
    let : IsCyclic X := isCyclic_of_prime_card hx
    let : Subsingleton X := Group.IsPerfect.subsingleton_of_isMulCommutative
    have : Nat.card X = 1 := Nat.card_of_subsingleton (1 : X)
    omega

private theorem symmetric_threeCore (n : ℕ) (hn : 5 ≤ n) :
    pCore 3 (Equiv.Perm (Fin n)) = ⊥ := by
  by_contra hb
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hp : IsPGroup 3 (alternatingGroup (Fin n)) :=
    pCore_isPGroup.to_le (Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn)
      ((nontrivial_iff_ne_bot _).mpr hb))
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rw [nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.dvd_div_of_mul_dvd ((by decide : 2 * 2 ∣ (4 : ℕ).factorial).trans
      (Nat.factorial_dvd_factorial (by omega)))
  rw [hk] at hd
  have := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at this

private theorem g2_threeCore : pCore 3 (Atlas.G2.Model (ZMod 2)) = ⊥ := by
  by_contra hb
  have hp : IsPGroup 3 Atlas.G2.BinaryException.H :=
    pCore_isPGroup.to_le (Atlas.G2.BinaryException.H_le_normal _ hb)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 2 ∣ Nat.card Atlas.G2.BinaryException.H := by
    rw [Atlas.G2.BinaryException.card_H]
    decide
  rw [hk] at hd
  have := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at this

variable {D : Type*} [Group D] [Finite D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}

private theorem no_cubic_of_threeCore (h : CubicHypothesis ρ A S C)
    (hc : pCore 3 (offenderSubgroup ρ) = ⊥) : False := by
  have he : A.subgroupOf (offenderSubgroup ρ) = ⊥ :=
    le_bot_iff.mp (h.internal_le_threeCore.trans hc.le)
  have ha := h.internal_card
  rw [he, card_bot] at ha
  omega

omit [Finite D] in
private theorem no_cubic_of_whole (h : CubicHypothesis ρ A S C)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (he : generalizedFitting (offenderSubgroup ρ) = ⊤) : False := by
  let : IsQuasisimple (⊤ : Subgroup (offenderSubgroup ρ)) := he ▸ hq
  let : IsQuasisimple (offenderSubgroup ρ) := IsQuasisimple.of_mulEquiv Subgroup.topEquiv
  have hc := cubic_le_center (A.subgroupOf (offenderSubgroup ρ))
    h.subnormal.subgroupOf h.internal_card
  have hb : A.subgroupOf (offenderSubgroup ρ) = ⊥ := le_bot_iff.mp (calc
    A.subgroupOf (offenderSubgroup ρ) =
      ⁅A.subgroupOf (offenderSubgroup ρ), C.subgroupOf (offenderSubgroup ρ)⁆ := h.internal_full
    _ ≤ ⁅center (offenderSubgroup ρ), C.subgroupOf (offenderSubgroup ρ)⁆ :=
      commutator_mono hc le_rfl
    _ = ⊥ := commutator_center_left _)
  have ha := h.internal_card
  rw [hb, card_bot] at ha
  omega

/-- The complete quasisimple B.5.6 alternative is incompatible with the
literal subnormal cubic and its full commutator. This supplies the
quasisimple premise of `bounds_of_remaining_cases`. -/
theorem quasisimple_excluded (h : CubicHypothesis ρ A S C)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (ha : QuasisimpleSourceConclusion (offenderRepresentation ρ)
      (generalizedFitting (offenderSubgroup ρ))) : False := by
  cases ha.clause_one with
  | irreducible _ _ _ _ extension =>
    rcases extension with he | ⟨_, ho⟩
    · exact no_cubic_of_whole ρ h hq he
    · apply no_cubic_of_threeCore ρ h
      rcases ho with hs | hg
      · obtain ⟨n, hn, _, hmod⟩ := hs
        obtain ⟨e⟩ := hmod
        apply map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
        rw [pCore_map_iso, Subgroup.map_bot, symmetric_threeCore n hn]
      · obtain ⟨e⟩ := hg
        apply map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
        rw [pCore_map_iso, Subgroup.map_bot, g2_threeCore]
  | doubleThree _ he _ _ _ => exact no_cubic_of_whole ρ h hq he
  | naturalDual _ _ he _ => exact no_cubic_of_whole ρ h hq he
  | repeatedNatural _ _ _ _ _ he _ => exact no_cubic_of_whole ρ h hq he

/-- The same exclusion with the corrected projective-line contract of
B.4.2(8). Only the whole-actor or outer-action clause is needed, so no
conversion to the legacy triple-six offender clause is asserted. -/
theorem quasisimple_excluded_of_source (h : CubicHypothesis ρ A S C)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (ha : ProjectiveLine.QuasisimpleSourceConclusion (offenderRepresentation ρ)
      (generalizedFitting (offenderSubgroup ρ))) : False := by
  cases ha.clause_one with
  | irreducible _ _ _ _ extension =>
    rcases extension with he | ⟨_, ho⟩
    · exact no_cubic_of_whole ρ h hq he
    · apply no_cubic_of_threeCore ρ h
      rcases ho with hs | hg
      · obtain ⟨n, hn, _, hmod⟩ := hs
        obtain ⟨e⟩ := hmod
        apply map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
        rw [pCore_map_iso, Subgroup.map_bot, symmetric_threeCore n hn]
      · obtain ⟨e⟩ := hg
        apply map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
        rw [pCore_map_iso, Subgroup.map_bot, g2_threeCore]
  | doubleThree _ he _ _ _ => exact no_cubic_of_whole ρ h hq he
  | naturalDual _ _ he _ => exact no_cubic_of_whole ρ h hq he
  | repeatedNatural _ _ _ _ _ he _ => exact no_cubic_of_whole ρ h hq he

section Application
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)
local notation "J₀" => offenderSubgroup ρ₀

/-- The quasisimple branch is excluded for the original Chapter 13 action,
star image and supplied Sylow. All cubic inputs come from the marked setup. -/
theorem marked_quasisimple_excluded (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hq : IsQuasisimple (generalizedFitting J₀))
    (ha : QuasisimpleSourceConclusion (offenderRepresentation ρ₀) (generalizedFitting J₀)) :
    False :=
  quasisimple_excluded ρ₀ (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs) hq ha

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
