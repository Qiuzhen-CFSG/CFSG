module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Noncentral
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CosetBound.Exceptional
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Marking
public import CFSG.Quasithin.Chapter1.Defs
public import Stellmacher.OmegaOneCenterMap

/-!
# Nontrivial core of the original rank-one join

Two distinct S₃-over-O₂ subgroups containing the same ambient Sylow subgroup
intersect in exactly that Sylow subgroup. Thus their literal copies inside
the join form a Goldschmidt triple. If its two-core were trivial, the
exceptional-vertex bound and the characteristic-two noncentral-omega bound
would both give Sylow order at most sixteen.

In 13.4 the original five-dimensional module lies in T and has order 32.
The fixed-line indices in 13.4.7(b) say that both vertices move Ω₁(Z(T)),
so the join has nontrivial two-core. This proves the locality conclusion
for every original-plane pair without an additional chief-factor premise.
It does not assert any of the four structural alternatives.

Source: Aschbacher–Smith, 13.4.7, opening paragraph, printed p.899;
F.6.5, printed p.305, and the noncentral-omega analysis proved using
Stellmacher (7.5) and (8.2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open ChapterF Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem core_ne_bot_of_large_noncentral_overlap {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B)
    (hlarge : 16 < Nat.card (A ⊓ B : Subgroup G))
    (hmoveA : ⁅A, omegaOneCenter (A ⊓ B)⁆ ≠ ⊥)
    (hmoveB : ⁅B, omegaOneCenter (A ⊓ B)⁆ ≠ ⊥) :
    pCore 2 G ≠ ⊥ := by
  intro hcore
  have hgoodA : generalizedFitting A = pCore 2 A := by
    by_contra hbad
    exact (not_le_of_gt hlarge)
      (h.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad)
  have hgoodB : generalizedFitting B = pCore 2 B := by
    by_contra hbad
    have hb := h.symm.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad
    rw [inf_comm B A] at hb
    exact (not_le_of_gt hlarge) hb
  have hsmall := (h.local_card_le_forty_eight_of_noncentral_omega
    hcore hgoodA hgoodB hmoveA hmoveB).1
  rw [h.local_card_eq_three_mul_intersection] at hsmall
  omega

/-- The two original minimal parabolics have exactly the given common Sylow. -/
theorem intersection_eq_sylow {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hne : A ≠ B) : A ⊓ B = (T : Subgroup G) := by
  have hiA : (T : Subgroup G).relIndex A = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eA (T.subtype hTA)
  have hiB : (T : Subgroup G).relIndex B = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eB (T.subtype hTB)
  have hcard (X : Subgroup G) (hTX : (T : Subgroup G) ≤ X)
      (hi : (T : Subgroup G).relIndex X = 3) : Nat.card X = 3 * Nat.card T := by
    have hh := ((T : Subgroup G).subgroupOf X).index_mul_card
    rw [show ((T : Subgroup G).subgroupOf X).index = 3 from hi,
      Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv] at hh
    exact hh.symm
  have hBI : (T : Subgroup G) ≤ A ⊓ B := le_inf hTA hTB
  have hm := relIndex_mul_relIndex (T : Subgroup G) (A ⊓ B) A hBI inf_le_left
  rw [hiA] at hm
  have hp : ((T : Subgroup G).relIndex (A ⊓ B) * (A ⊓ B).relIndex A).Prime :=
    hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hi⟩ | ⟨_, hi⟩
  · have hAB : A ≤ B := (relIndex_eq_one.mp hi).trans inf_le_right
    exact (hne (eq_of_le_of_card_ge hAB (by rw [hcard A hTA hiA, hcard B hTB hiB]))).elim
  · exact le_antisymm (relIndex_eq_one.mp hi) hBI

/-- Restrict the actual pair to its join, retaining both quotient markings. -/
theorem pair_goldschmidt {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hne : A ≠ B) :
    IsGoldschmidtTriple (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) := by
  let X := A ⊔ B
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hquot (Y : Subgroup G) (hYX : Y ≤ X)
      (e : (Y ⧸ pCore 2 Y) ≃* Equiv.Perm (Fin 3)) :
      Nonempty ((Y.subgroupOf X ⧸ pCore 2 (Y.subgroupOf X)) ≃* Equiv.Perm (Fin 3)) := by
    let a := subgroupOfEquivOfLe hYX
    exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e⟩
  refine ⟨?_, hquot A le_sup_left eA, hquot B le_sup_right eB, T.subtype hTX, ?_⟩
  · apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  · change (A ⊓ B).subgroupOf X = (T : Subgroup G).subgroupOf X
    rw [intersection_eq_sylow hTA hTB eA eB hne]

/-- Both fixed-line indices and a Sylow of order greater than sixteen force locality. -/
theorem join_mem_HOver_of_large_sylow {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hne : A ≠ B) (hlarge : 16 < Nat.card T)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    A ⊔ B ∈ Chapter1.HOver G (T : Set G) := by
  let X := A ⊔ B
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hinter := intersection_eq_sylow hTA hTB eA eB hne
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have homega : (omegaOneCenter ((A.subgroupOf X) ⊓ (B.subgroupOf X))).map X.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    change (omegaOneCenterAmbient ((A ⊓ B).subgroupOf X)).map X.subtype = _
    rw [hinter, ← omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hTX]
  have hmove (Y : Subgroup G) (hYX : Y ≤ X)
      (hi : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
        centralizer (Y : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
      ⁅Y.subgroupOf X, omegaOneCenter ((A.subgroupOf X) ⊓ (B.subgroupOf X))⁆ ≠ ⊥ := by
    intro hh
    have hm := congrArg (Subgroup.map X.subtype) hh
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hYX, homega, Subgroup.map_bot] at hm
    have hc : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (Y : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)
    rw [inf_eq_left.mpr hc, relIndex_self] at hi
    omega
  have hsize : 16 < Nat.card ((A.subgroupOf X) ⊓ (B.subgroupOf X) : Subgroup X) := by
    change 16 < Nat.card ((A ⊓ B).subgroupOf X)
    rw [hinter, Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv]
    exact hlarge
  have hcore := core_ne_bot_of_large_noncentral_overlap hg hsize
    (hmove A le_sup_left hindexA) (hmove B le_sup_right hindexB)
  refine ⟨?_, hTX⟩
  change (pCore 2 X).map X.subtype ≠ ⊥
  exact fun hh => hcore ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp hh)

/-- The actual marked five-dimensional module discharges the Sylow size bound. -/
theorem original_pair_local {T : Sylow 2 G} {L V A B : Subgroup G}
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    A ⊔ B ∈ Chapter1.HOver G (T : Set G) := by
  have hc := card_le_of_le D.le_sylow
  rw [m.card_module] at hc
  exact join_mem_HOver_of_large_sylow hTA hTB eA eB hne (by omega) hindexA hindexB

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
